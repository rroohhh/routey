from debug_utils import event_annotation, mark_debug, span_annotation
from round_robin_arbiter import RoundRobinArbiter
from utils import assertFormal
from formal_utils import FormalScoreboard, FormalScoreboardWolper, AXISStreamContract

from amaranth import Module, Signal, Elaboratable, Value, Cover, Assert, Mux, Assume, ResetSignal, unsigned, Array
from amaranth.asserts import AnySeq, AnyConst
from amaranth.lib import stream, data, wiring
from amaranth.lib.wiring import In, Out, Component, Signature
from amaranth.lib.memory import Memory
from amaranth.back.verilog import convert
from pathlib import Path

def onehot(num):
    return len([1 for k in bin(num) if k == "1"]) == 1

def SeqLayout(window_size):
    return range(2 * window_size)

class ArqPayloadLayout(data.StructLayout):
    seq: Signal
    p: Signal

    def __init__(self, payload_shape, window_size):
        super().__init__({
            "seq": SeqLayout(window_size),
            "p": payload_shape
        })

class AckLayout(data.StructLayout):
    seq: Signal
    is_nack: Signal
    seq_is_valid: Signal

    def __init__(self, window_size):
        super().__init__({
            "seq": SeqLayout(window_size),
            "is_nack": 1,
            "seq_is_valid": 1 # a invalid seq can happen if we send a nack at the first received packet
        })

def AckSignature(window_size):
    return wiring.Signature({
        "p": Out(AckLayout(window_size=window_size)),
        "trigger": Out(1),
        "did_trigger": In(1)
    })

class ArqSender(Component):
    def __init__(self, window_size, payload_shape):
        self.window_size = window_size
        assert onehot(window_size), "only power of two window size supported "
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)),
            "output": Out(stream.Signature(ArqPayloadLayout(payload_shape, window_size))),
            "ack": In(stream.Signature(AckLayout(window_size=window_size), always_ready=True)),
        }))

    def elaborate(self, _):
        m = Module()

        write_ptr = Signal(range(2 * self.window_size))
        read_ptr = Signal.like(write_ptr)
        send_ptr = Signal.like(read_ptr)
        next_send_ptr = Signal.like(send_ptr)

        is_resend = Signal()
        resend_start = Signal.like(send_ptr, reset_less=True)

        m.submodules.buffer = buffer = Memory(shape = self.input.p.shape(), depth = self.window_size, init =[0])
        buffer_write = buffer.write_port(domain = "sync");
        buffer_read = buffer.read_port(domain = "sync");

        push = Signal()
        m.d.comb += push.eq(self.input.valid & self.input.ready)
        pop = Signal()
        m.d.comb += pop.eq(self.output.valid & self.output.ready)

        # full = (write_ptr - read_ptr) == self.window_size
        # expressed based on the uppermost and lowermost index here, because amaranth auto widens the minus operation
        full = (write_ptr[-1] != read_ptr[-1]) & (write_ptr[:-1] == read_ptr[:-1])

        empty = write_ptr == read_ptr

        # TODO(robin): dynamic tuning, exponential back-off?
        timeout_max = (2 * self.window_size)
        timeout_counter = Signal(range(timeout_max + 1), init=timeout_max)
        timeout_occured = timeout_counter == 0;
        with m.If(~empty):
            # Do not trigger timeout if we are currently resending, no use...
            with m.If((self.ack.valid & self.ack.ready) | is_resend):
                m.d.sync += timeout_counter.eq(timeout_max)
            with m.Else():
                with m.If(timeout_counter == 0):
                    m.d.sync += timeout_counter.eq(timeout_max)
                with m.Else():
                    m.d.sync += timeout_counter.eq(timeout_counter - 1)
        with m.Else():
            m.d.sync += timeout_counter.eq(timeout_max)


        # have to compare to the current write pointer, because we cannot read the word we write in the same cycle
        have_outstanding_to_send = Signal()
        m.d.comb += have_outstanding_to_send.eq(write_ptr != next_send_ptr)

        # write handling is simple, we just always write, when we push
        # which is whenever we have space
        m.d.comb += [
            buffer_write.en.eq(push),
            buffer_write.addr.eq(write_ptr),
            buffer_write.data.eq(self.input.p),
        ]
        m.d.comb += self.input.ready.eq(~full)

        # for reads we have to prefetch, as the read port is synchronous.
        # There are two scenarios:
        # 1. The buffer was empty and now contains a word. This is a special case, as we dont have write port transparency,
        #    so we have to delay the read one cycle.
        # 2. The send ptr was moved. Then we need to prefetch, whenever there is something outstanding to send
        last_was_empty_push = Signal()
        send_ptr_moved = Signal()
        m.d.sync += last_was_empty_push.eq(~have_outstanding_to_send & push)
        prefetch = Signal()
        m.d.comb += prefetch.eq((send_ptr_moved | last_was_empty_push) & have_outstanding_to_send)

        send_outstanding = Signal()
        # usually send_outstanding gets set by set_send_ptr, but this catches the
        # case of a last_was_empty_push prefetch
        with m.If(prefetch):
            m.d.sync += send_outstanding.eq(1)

        m.d.comb += [
            buffer_read.en.eq(prefetch),
            buffer_read.addr.eq(next_send_ptr),
            self.output.p.p.eq(buffer_read.data),
            self.output.p.seq.eq(send_ptr)
        ]
        m.d.comb += self.output.valid.eq(send_outstanding)

        def set_send_ptr(target):
            m.d.comb += send_ptr_moved.eq(1)
            # only iff we actually prefetch something we will have a send outstanding
            # overwrite any stale info here
            m.d.sync += send_outstanding.eq(prefetch)
            m.d.comb += next_send_ptr.eq(target)

        # the read ptr just gets set by received ack's
        # send ptr increments like a fifo pointer, unless we receive a nack
        m.d.comb += next_send_ptr.eq(send_ptr)
        with m.If(push):        #
            m.d.sync += write_ptr.eq(write_ptr + 1)

        with m.If(pop):
            set_send_ptr(send_ptr + 1)

        next_read_ptr = Signal.like(read_ptr)
        m.d.comb += next_read_ptr.eq(read_ptr)
        m.d.sync += read_ptr.eq(next_read_ptr)

        with m.If(is_resend & (((send_ptr - resend_start) % (2 * self.window_size)) < self.window_size)):
            m.d.sync += is_resend.eq(0)

        def trigger_resend():
            with m.If(next_read_ptr != write_ptr):
                m.d.sync += [
                    is_resend.eq(1),
                    resend_start.eq(write_ptr), # force a resend of the whole window
                ]
                set_send_ptr(next_read_ptr)

        # Timeout has lower priority than ack
        with m.If(timeout_occured):
            trigger_resend()

        with m.If(self.ack.valid & self.ack.ready):
            with m.If(self.ack.p.seq_is_valid):
                # we get the ack that was received correctly, so we want to "read" the word after that, iff there is one after
                # (the empty and full logic only works it read cannot "walk" ahead of write pointers)
                has_next = ((write_ptr - self.ack.p.seq) % (2 * self.window_size)) >= 1
                m.d.comb += next_read_ptr.eq(self.ack.p.seq + has_next)

                # transport the send ptr to the ack here (if ack > send_ptr)
                diff = (next_read_ptr - send_ptr - pop) % (2 * self.window_size)
                with m.If(diff <= self.window_size):
                    set_send_ptr(next_read_ptr)


            with m.If(self.ack.p.is_nack):
                trigger_resend()

        m.d.sync += send_ptr.eq(next_send_ptr)

        # debug annotations
        ack_recieved = Signal()
        nack_recieved = Signal()
        timeout_occured_debug = Signal()
        m.d.comb += [
            ack_recieved.eq(self.ack.valid & self.ack.ready & ~self.ack.p.is_nack),
            nack_recieved.eq(self.ack.valid & self.ack.ready & self.ack.p.is_nack),
            timeout_occured_debug.eq(timeout_occured)
        ]
        event_annotation(ack_recieved, "ack recieved")
        event_annotation(ack_recieved, "nack recieved")
        event_annotation(timeout_occured_debug, "ack timeout")
        span_annotation(is_resend, "resending")


        outstanding = Signal.like(read_ptr)
        outstanding.attrs["capacity"] = self.window_size
        mark_debug(outstanding)
        m.d.comb += outstanding.eq(write_ptr - read_ptr)

        mark_debug(is_resend)

        return m

    # TODO(robin): check axi stream properties
    @staticmethod
    def formal():
        class FormalCheck(Elaboratable):
            def __init__(self, window_size = 8, payload_shape = 1):
                self.payload_shape = payload_shape
                self.window_size = window_size
                self.arq_sender = ArqSender(window_size, self.payload_shape)

            def elaborate(self, _):
                m = Module()

                m.submodules.arq_sender = arq_sender = self.arq_sender

                m.submodules.stream_check = AXISStreamContract(arq_sender.output, c=Assert)

                m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);

                m.d.comb += [
                    arq_sender.ack.valid.eq(0),
                    scoreboard.input.valid.eq(arq_sender.input.valid & arq_sender.input.ready),
                    scoreboard.input.p.eq(arq_sender.input.p),

                    scoreboard.output.valid.eq(arq_sender.output.valid & arq_sender.output.ready),
                    scoreboard.output.p.eq(arq_sender.output.p.p)
                ]

                cycle_counter = Signal(10)
                read_counter = Signal(10)

                m.d.sync += cycle_counter.eq(cycle_counter + 1)
                with m.If(arq_sender.output.valid & arq_sender.output.ready):
                    m.d.sync += read_counter.eq(read_counter + 1)


                # 1 cycle delay for write -> not empty
                # 1 cycle delay to read the value again (no read port transparency)
                m.d.comb += Cover((cycle_counter == (self.window_size + 2)) & (read_counter == self.window_size))
                # m.d.comb += Cover(arq_sender.output.valid)

                return m


        spec = FormalCheck()
        for mode in ["prove", "cover"]:
            assertFormal(spec, ports=[
                spec.arq_sender.input.valid,
                spec.arq_sender.input.ready,
                Value.cast(spec.arq_sender.input.p),
                spec.arq_sender.output.valid,
                spec.arq_sender.output.ready,
                Value.cast(spec.arq_sender.output.p),
            ], mode=mode)



# last write wins reg
# NOTE: this is not a legal axi stream, it changes payload while valid is high
class LWWReg(Component):
    def __init__(self, payload_shape):
        super().__init__(wiring.Signature({
            "output": Out(stream.Signature(payload_shape)),
            "buffer_valid": Out(1),
            "input": In(stream.Signature(payload_shape, always_ready = True))
        }))

    def elaborate(self, _):
        m = Module()

        buffer = Signal.like(self.input.p, reset_less=True)
        buffer_valid = self.buffer_valid

        m.d.comb += self.output.p.eq(buffer)
        m.d.comb += self.output.valid.eq(buffer_valid)

        with m.If(self.output.ready & self.output.valid):
            m.d.sync += buffer_valid.eq(0)

        with m.If(self.input.valid & self.input.ready):
            m.d.sync += buffer_valid.eq(1)
            m.d.sync += buffer.eq(self.input.p)

        return m

class ArqReceiver(Component):
    def __init__(self, window_size, payload_shape, acks_per_window = 4):
        self.window_size = window_size
        self.words_per_ack = self.window_size // acks_per_window
        assert self.words_per_ack > 0
        assert onehot(window_size), "only power of two window size supported "
        super().__init__(wiring.Signature({
            "input_error": In(1),
            "output": Out(stream.Signature(payload_shape)),
            "input": In(stream.Signature(ArqPayloadLayout(payload_shape, window_size))),
            "ack": Out(AckSignature(window_size=window_size)),
        }))

    def elaborate(self, _):
        m = Module()

        last_seq = Signal.like(self.input.p.seq, init = -1)
        last_seq_valid = Signal()
        expected_seq = Signal.like(self.input.p.seq)
        m.d.comb += expected_seq.eq(last_seq + 1)
        push = self.input.valid & self.input.ready

        input_seq_valid = self.input.valid & (self.input.p.seq == expected_seq)
        with m.If(push & input_seq_valid):
            m.d.sync += last_seq_valid.eq(1),
            m.d.sync += last_seq.eq(self.input.p.seq)

        m.d.comb += [
            self.input.ready.eq(self.output.ready | (self.input.valid & ~input_seq_valid)),
            self.output.p.eq(self.input.p.p),
            self.output.valid.eq(input_seq_valid)
        ]

        m.d.comb += [
            # TODO(robin): this is slightly pessimistic, as last_seq can be outdated by one word
            self.ack.p.seq.eq(last_seq),
            self.ack.p.seq_is_valid.eq(last_seq_valid),
        ]

        nack_scheduled = Signal()
        with m.If(self.input.valid & input_seq_valid):
            m.d.sync += nack_scheduled.eq(0)

        m.d.comb += self.ack.p.is_nack.eq(nack_scheduled)

        m.d.sync += self.ack.trigger.eq(0)

        def send_ack(m, is_nack: bool, seq = None):
            m.d.sync += timeout_counter.eq(timeout_max)
            # if seq is not None:
            #     m.d.comb += self.ack.p.seq.eq(seq)
            if is_nack:
                m.d.sync += [
                    self.ack.trigger.eq(~nack_scheduled),
                    nack_scheduled.eq(1)
                ]
            else:
                m.d.sync += self.ack.trigger.eq(1)

        # normal ack flow: ack every n'th word
        word_counter = Signal(range(self.words_per_ack))


        # timeout for ack: if we have not received new words for some time and we have outstanding words
        # send a ack
        # TODO(robin): make this configurable
        # this is smaller than the arqsender resend timeout, to avoid spurious resends
        timeout_max = self.window_size
        timeout_counter = Signal(range(timeout_max + 1))

        with m.If(word_counter == 0):
            m.d.sync += timeout_counter.eq(timeout_max)
        with m.Else():
            with m.If(timeout_counter != 0):
                m.d.sync += timeout_counter.eq(timeout_counter - 1)
            with m.Else():
                m.d.sync += word_counter.eq(0)
                send_ack(m, False)

        with m.If(push & input_seq_valid):
            with m.If(word_counter == (self.words_per_ack - 1)):
                m.d.sync += word_counter.eq(0)
                # send with the expected seq,
                # last_seq only gets updated next cycle
                send_ack(m, False, expected_seq)
            with m.Else():
                m.d.sync += word_counter.eq(word_counter + 1)

        # send nack for out of order seq's
        with m.If(self.input.valid):
            # if they are in window, send a nack, we must have missed a word
            with m.If(((expected_seq - self.input.p.seq) % (2 * self.window_size)) > self.window_size):
                send_ack(m, True)
            # if they are out of window, send a ack, the sender seems to resend unnecessaryily
            with m.Elif(~input_seq_valid):
                send_ack(m, False) # TODO(robin): throttle these?

        with m.If(self.ack.did_trigger):
            m.d.sync += [
                # if we are sending an ack right now, we could also just this moment receive an word,
                # so we could have this one unacked word
                word_counter.eq(push & input_seq_valid),
                timeout_counter.eq(timeout_max)
            ]

        # TODO(robin): this about input_error <-> is_nack lwwreg stuff timing
        # scenario:
        # we get input error (because of chksum mismatch)
        # -> this is routed comb to the receiver -> receiver triggers nack immediately
        # -> nack is stored, but cannot be send out immediately
        # -> now actually we received a valid packet before the one that had a chksum mismatch, but this had higher latency into the sender
        # -> we ack this and potentially trigger a new ack to be sent, now without is_nack
        # -> the old nack gets lost and no resend is triggerd
        # Potentialy solution: make triggering is_nack reset timeout + word counter based triggering
        # -> this means, unless the latency between the input_error assertion and the sender input is greater than these timeouts / wordcounts, the nack cannot get lost
        with m.If(self.input_error):
            send_ack(m, True)

        timeout_occured = Signal()
        m.d.comb += timeout_occured.eq(timeout_counter == 0)
        span_annotation(self.input_error, "input error")
        event_annotation(timeout_occured, "ack send timeout")
        return m

    @staticmethod
    def formal():
        class FormalCheck(Elaboratable):
            def __init__(self, window_size = 8, payload_shape = 1, acks_per_window = 4):
                self.payload_shape = payload_shape
                self.window_size = window_size
                self.arq_receiver = ArqReceiver(window_size, self.payload_shape, acks_per_window)

            def elaborate(self, _):
                m = Module()

                m.submodules.arq_receiver = arq_receiver = self.arq_receiver
                m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);

                seq = Signal.like(arq_receiver.input.p.seq)
                with m.If(arq_receiver.input.valid & arq_receiver.input.ready):
                    m.d.sync += seq.eq(seq + 1)
                m.d.comb += [
                    arq_receiver.input.p.seq.eq(seq)
                ]

                m.d.comb += [
                    scoreboard.input.valid.eq(arq_receiver.input.valid & arq_receiver.input.ready),
                    scoreboard.input.p.eq(arq_receiver.input.p.p),

                    scoreboard.output.valid.eq(arq_receiver.output.valid & arq_receiver.output.ready),
                    scoreboard.output.p.eq(arq_receiver.output.p)
                ]

                cycle_counter = Signal(10)
                read_counter = Signal(10)

                m.d.sync += cycle_counter.eq(cycle_counter + 1)
                with m.If(arq_receiver.output.valid & arq_receiver.output.ready):
                    m.d.sync += read_counter.eq(read_counter + 1)


                # 1 cycle delay for write -> not empty
                # 1 cycle delay to read the value again (no read port transparency)
                m.d.comb += Cover((cycle_counter == self.window_size) & (read_counter == self.window_size))

                return m


        spec = FormalCheck()
        for mode in ["prove", "cover"]:
            assertFormal(spec, ports=[
                spec.arq_receiver.input.valid,
                spec.arq_receiver.input.ready,
                Value.cast(spec.arq_receiver.input.p),
                spec.arq_receiver.output.valid,
                spec.arq_receiver.output.ready,
                Value.cast(spec.arq_receiver.output.p),
            ], mode=mode)


def combined_formal_check(payload_shape = 1, window_size = 8, acks_per_window = 4):
    class LinkModel(Component):
        def __init__(self, payload_shape, link_delay, lossy = False):
            self.payload_shape = payload_shape
            self.link_delay = link_delay
            self.lossy = lossy

            super().__init__(wiring.Signature({
                "input": In(stream.Signature(payload_shape)),
                "output": Out(stream.Signature(payload_shape)),
                "output_error": Out(1)
            }))

        def elaborate(self, _):
            m = Module()

            buf_layout = data.StructLayout({
                "valid": 1,
                "error": 1,
                "p": self.payload_shape
            })

            bufs = [Signal(buf_layout, name=f"buf[{i}]") for i in range(self.link_delay)]
            for i in range(self.link_delay - 1):
                m.d.sync += bufs[i + 1].eq(bufs[i])

            if self.lossy:
                error = AnySeq(1)
            else:
                error = 0

            m.d.comb += [
                self.output_error.eq(bufs[-1].error),
                self.output.valid.eq(bufs[-1].valid),
                self.output.p.eq(bufs[-1].p),
                self.input.ready.eq(1)
            ]

            m.d.sync += [
                bufs[0].p.eq(self.input.p),
                bufs[0].valid.eq(self.input.valid & ~error),
                bufs[0].error.eq(error)
            ]

            return m


    class FormalCheck(Component):
        def __init__(self, window_size = 8, payload_shape = 1, acks_per_window = 4, link_delay = 2):
            self.payload_shape = payload_shape
            self.window_size = window_size
            self.link_delay = link_delay

            super().__init__(wiring.Signature({
                "input": In(stream.Signature(payload_shape)),
                "output": Out(stream.Signature(payload_shape))
            }))

        def elaborate(self, _):
            m = Module()

            m.submodules.arq_sender = arq_sender = ArqSender(window_size, self.payload_shape)
            m.submodules.arq_receiver = arq_receiver = ArqReceiver(window_size, self.payload_shape, acks_per_window)
            m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);
            # m.submodules.scoreboard = scoreboard = FormalScoreboardWolper();

            m.submodules.tx_link = tx_link = LinkModel(arq_sender.output.p.shape(), self.link_delay, lossy=True)
            m.submodules.rx_link = rx_link = LinkModel(arq_receiver.ack.p.shape(), self.link_delay)

            # with credit counting this should be a assert
            m.d.comb += Assume(self.output.ready)

            # for debug
            # m.d.comb += Assume(~ResetSignal())

            wiring.connect(m, wiring.flipped(self.input), arq_sender.input)

            wiring.connect(m, arq_sender.output, tx_link.input)
            wiring.connect(m, tx_link.output, arq_receiver.input)
            m.d.comb += arq_receiver.input_error.eq(tx_link.output_error)

            wiring.connect(m, arq_receiver.ack, rx_link.input)
            wiring.connect(m, rx_link.output, arq_sender.ack)

            wiring.connect(m, arq_receiver.output, wiring.flipped(self.output))


            m.d.comb += [
                scoreboard.input.valid.eq(self.input.valid & self.input.ready),
                scoreboard.input.p.eq(self.input.p),

                scoreboard.output.valid.eq(self.output.valid & self.output.ready),
                scoreboard.output.p.eq(self.output.p)
            ]

            cycle_counter = Signal(10)
            read_counter = Signal(10)

            m.d.sync += cycle_counter.eq(cycle_counter + 1)
            with m.If(arq_receiver.output.valid & arq_receiver.output.ready):
                m.d.sync += read_counter.eq(read_counter + 1)

            m.d.comb += Cover(read_counter == (4 * self.window_size))

            return m

    spec = FormalCheck(window_size = window_size, payload_shape = payload_shape, acks_per_window = acks_per_window)

    ports = [
            spec.input.valid,
            spec.input.ready,
            Value.cast(spec.input.p),
            spec.output.valid,
            spec.output.ready,
            Value.cast(spec.output.p),
    ]

    Path("arq.sv").write_text(convert(spec, name="arq_formal", ports = ports))

    # for mode in ["cover", "prove"]:
    #     print(mode)
    #     assertFormal(spec, ports=ports, mode=mode)

class MultiQueueFIFOInputSignature(wiring.Signature):
    def __init__(self, payload_shape, n_queues):
        super().__init__({
            "valid": Out(1),
            "target": Out(range(n_queues)),
            "p": Out(payload_shape),
            "ready": In(data.ArrayLayout(1, n_queues))
        })

    def create(self, *, path=None, src_loc_at=0):
        return MultiQueueFIFOInputInterface(self, path=path, src_loc_at=1 + src_loc_at)


class MultiQueueFIFOInputInterface(wiring.PureInterface):
    @property
    def valid_ready(self):
        return (self.valid, self.ready[self.target])

# this tracks multiple fifo queues with a shared buffer
# this means only one write can be active at any time
# and only one read can be active at any time
class MultiQueueFIFO(Component):
    def __init__(self, payload_shape, n_queues, depth):
        super().__init__(wiring.Signature({
            "input": In(MultiQueueFIFOInputSignature(payload_shape, n_queues)),
            "output": Out(stream.Signature(payload_shape)).array(n_queues)
        }))

        assert onehot(depth), "only power of two depth supported "

        self.depth = depth
        self.n_queues = n_queues

    def elaborate(self, _):
        m = Module()

        read_ptrs = [Signal(range(2 * self.depth), name = f"read_ptr_{i}") for i in range(self.n_queues)]
        write_ptrs = [Signal(range(2 * self.depth), name = f"write_ptr_{i}") for i in range(self.n_queues)]
        out_regs = [Signal.like(self.input.p, name = f"out_reg_{i}", reset_less=True) for i in range(self.n_queues)]
        out_reg_filleds = [Signal(name = f"out_reg_filled_{i}") for i in range(self.n_queues)]

        outstanding = [Signal.like(read_ptrs[i], name = f"outstanding_{i}") for i in range(self.n_queues)]
        for o, r, w in zip(outstanding, read_ptrs, write_ptrs):
            m.d.comb += o.eq(w - r)
            o.attrs["capacity"] = self.depth
            mark_debug(o)

        # TODO(robin): on asic make this macro memory
        m.submodules.buffer = buffer = Memory(shape = self.input.p.shape(), depth = self.depth * self.n_queues, init=[])
        buffer_write = buffer.write_port(domain = "sync");
        buffer_read = buffer.read_port(domain = "sync");

        # default to 1, so override
        m.d.comb += buffer_read.en.eq(0)

        mem_out_have_data = Signal()
        mem_out_id = Signal(range(self.n_queues))

        m.d.sync += mem_out_have_data.eq(buffer_read.en),

        def read(queue_id, read_ptr):
            m.d.sync += [
                mem_out_id.eq(queue_id),
            ]
            m.d.comb += [
                buffer_read.addr.eq(queue_id * self.depth + (read_ptr % self.depth)),
                buffer_read.en.eq(1)
            ]

        def incr(ptr):
            # return ptr.eq(Mux(ptr < (self.depth - 1), ptr + 1, 0))
            return ptr.eq(ptr + 1)

        for i in range(self.n_queues):
            write_ptr = write_ptrs[i]
            read_ptr = read_ptrs[i]
            out_reg = out_regs[i]
            out_reg_filled = out_reg_filleds[i]

            buf_empty = read_ptr == write_ptr
            buf_full = (read_ptr[-1] != write_ptr[-1]) & (read_ptr[:-1] == write_ptr[:-1])

            push = Signal(name=f"push_{i}")
            m.d.comb += push.eq(self.input.ready[i] & self.input.valid & (self.input.target == i))
            pop = Signal(name=f"pop_{i}")
            m.d.comb += pop.eq(self.output[i].ready & self.output[i].valid)

            data_from_memory = mem_out_have_data & (mem_out_id == i)

            # when can we bypass the memory?
            # 1. Only when buffer is empty
            # 2. Only if we have space in the out reg, or we are currently popping out
            # 3. Only if we do not to store data from the memory output register first

            out_reg_push = push & buf_empty & (~out_reg_filled | pop) & ~(data_from_memory & ~pop)
            buf_push = push & ~out_reg_push

            # always a pop of the buffer if we pop and the buffer is not empty
            buf_pop = pop & ~buf_empty

            # we prefetched and did not pop -> store in output reg
            with m.If(data_from_memory & ~pop):
                m.d.sync += [
                    out_reg_filled.eq(1),
                    out_reg.eq(buffer_read.data)
                ]

            # we push and the buf is empty -> bypass memory and store directly in memory
            with m.If(out_reg_push):
                m.d.sync += [
                    out_reg_filled.eq(1),
                    out_reg.eq(self.input.p)
                ]

            # we pop from the output reg (and do not push to it directly) -> output reg is empty now
            with m.If(pop & ~out_reg_push):
                m.d.sync += [
                    out_reg_filled.eq(0)
                ]

            # mux output between output reg or memory if output reg is empty
            m.d.comb += [
                self.output[i].valid.eq(out_reg_filled | data_from_memory),
                self.output[i].p.eq(Mux(out_reg_filled, out_reg, buffer_read.data)),
                self.input.ready[i].eq(~buf_full)
            ]

            # this is just normal cycling buffer ptr wrangling
            with m.If(buf_push):
                m.d.sync += incr(write_ptr)
                m.d.comb += [
                    buffer_write.addr.eq(i * self.depth + (write_ptr % self.depth)),
                    buffer_write.en.eq(1),
                    buffer_write.data.eq(self.input.p)
                ]

            with m.If(buf_pop):
                m.d.sync += incr(read_ptr)
                read(i, read_ptr)

        return m

    @staticmethod
    def formal():
        class FormalCheck(Component):
            def __init__(self, n_queues = 2, depth = 4, payload_shape = 1):
                self.payload_shape = payload_shape
                self.depth = depth
                self.n_queues = n_queues

                super().__init__(wiring.Signature({
                    "input": In(MultiQueueFIFOInputSignature(payload_shape, n_queues)),
                    "output": Out(stream.Signature(payload_shape)).array(self.n_queues)
                }))

            def elaborate(self, _):
                m = Module()

                m.submodules.fifo = fifo = MultiQueueFIFO(n_queues = self.n_queues, payload_shape = self.payload_shape, depth = self.depth)
                m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);

                wiring.connect(m, wiring.flipped(self.input), fifo.input)
                for sout, fout in zip(self.output, fifo.output):
                    wiring.connect(m, wiring.flipped(sout), fout)

                observed_queue = AnyConst(range(self.n_queues))
                observed_output = Array(fifo.output)[observed_queue]

                m.d.comb += [
                    scoreboard.input.valid.eq(fifo.input.valid & fifo.input.ready[observed_queue] & (fifo.input.target == observed_queue)),
                    scoreboard.input.p.eq(fifo.input.p),

                    scoreboard.output.valid.eq(observed_output.valid & observed_output.ready),
                    scoreboard.output.p.eq(observed_output.p),
                ]

                m.d.comb += [
                    Assume(sum(out.ready for out in fifo.output) <= 1)
                ]

                cycle_counter = Signal(10)
                read_counter = Signal(10)

                m.d.sync += cycle_counter.eq(cycle_counter + 1)
                with m.If(observed_output.valid & observed_output.ready):
                    m.d.sync += read_counter.eq(read_counter + 1)


                # # 1 cycle delay for write -> not empty
                # # 1 cycle delay to read the value again (no read port transparency)
                m.d.comb += Cover((read_counter == (self.depth * 2)) & (cycle_counter == (self.depth * 2 + 1)))

                return m


        spec = FormalCheck()
        Path("multi_fifo.sv").write_text(
            convert(
                MultiQueueFIFO(
                    n_queues = 2,
                    payload_shape = 1,
                    depth = 4
                ), name="multi_queue"
            )
        )
        # for mode in ["prove", "cover"]:
        #     assertFormal(spec, ports=None, mode=mode)

def CreditShape(depth):
    return range(2 * depth)

def CreditLayout(depth, n_queues):
    return data.ArrayLayout(CreditShape(depth), n_queues)

def CreditStream(depth, n_queues):
    return stream.Signature(CreditLayout(depth, n_queues), always_ready=True)

# this is basically a multi queue fifo with a remote memory
class MultiQueueCreditCounterTX(Component):
    def __init__(self, payload_shape, n_queues, depth):
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)).array(n_queues),
            "output": Out(stream.Signature(payload_shape)).array(n_queues),
            "credit_in": In(CreditStream(depth, n_queues)),
        }))

        self.n_queues = n_queues
        self.depth = depth

    def elaborate(self, _):
        m = Module()

        read_ptrs = [Signal(CreditShape(self.depth), name = f"read_ptr_{i}") for i in range(self.n_queues)]
        write_ptrs = [Signal(CreditShape(self.depth), name = f"write_ptr_{i}") for i in range(self.n_queues)]

        with m.If(self.credit_in.valid & self.credit_in.ready):
            for i in range(self.n_queues):
                m.d.sync += read_ptrs[i].eq(self.credit_in.p[i])

        for i in range(self.n_queues):
            rd_ptr = read_ptrs[i]
            wr_ptr = write_ptrs[i]
            input = self.input[i]
            output = self.output[i]

            full = (rd_ptr[-1] != wr_ptr[-1]) & (rd_ptr[:-1] == wr_ptr[:-1])

            m.d.comb += [
                output.p.eq(input.p),
                output.valid.eq(input.valid & ~full),
                input.ready.eq(output.ready & ~full)
            ]

            with m.If(output.valid & output.ready):
                m.d.sync += wr_ptr.eq(wr_ptr + 1)

        return m


class StreamMonitor(data.StructLayout):
    valid: Signal
    ready: Signal

    def __init__(self):
        super().__init__({
            "valid": 1,
            "ready": 1
        })



def CreditRXSignature(depth, n_queues):
    return wiring.Signature({
        "credit": Out(CreditLayout(depth, n_queues)),
        "did_trigger": In(1), # wether a ack was sent (acks always include credit updates)
        "trigger": Out(1) # wether a credit update should be sent
    })


class MultiQueueCreditCounterRX(Component):
    def __init__(self, payload_shape, n_queues, depth, updates_per_depth = 4):
        super().__init__(wiring.Signature({
            "fifo_output_monitor": In(StreamMonitor()).array(n_queues),
            "credit_out": Out(CreditRXSignature(depth, n_queues)),
        }))
        self.n_queues = n_queues
        self.depth = depth
        self.updates_per_depth = updates_per_depth

    def elaborate(self, _):
        m = Module()

        read_ptrs = [Signal(CreditShape(self.depth), name = f"read_ptr_{i}") for i in range(self.n_queues)]
        did_read = Signal()

        for i in range(self.n_queues):
            m.d.comb += self.credit_out.credit[i].eq(read_ptrs[i])
            with m.If(self.fifo_output_monitor[i].valid & self.fifo_output_monitor[i].ready):
                m.d.sync += read_ptrs[i].eq(read_ptrs[i] + 1)
                m.d.comb += did_read.eq(1)

        words_per_update = self.depth // self.updates_per_depth
        credit_trigger_timer = Signal(range(words_per_update))

        with m.If(self.credit_out.did_trigger):
            m.d.sync += credit_trigger_timer.eq(0)
        with m.Else():
            with m.If(credit_trigger_timer == (words_per_update - 1)):
                m.d.sync += credit_trigger_timer.eq(0)
                m.d.comb += self.credit_out.trigger.eq(1)
            with m.Else():
                m.d.sync += credit_trigger_timer.eq(credit_trigger_timer + did_read)

        return m

class RRStreamArbiterPayloadLayout(data.StructLayout):
    p: Signal
    src: Signal

    def __init__(self, payload_shape, n_queues):
        super().__init__({
            "p": payload_shape,
            "src": range(n_queues)
        })

class RRStreamArbiter(Component):
    def __init__(self, payload_shape, n_queues):
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)).array(n_queues),
            "output": Out(stream.Signature(RRStreamArbiterPayloadLayout(payload_shape, n_queues))),
        }))
        self.n_queues = n_queues

    def elaborate(self, _):
        m = Module()

        inputs = self.input
        output = self.output

        arbiter = m.submodules.arbiter = RoundRobinArbiter(len(inputs))

        for i, input in enumerate(inputs):
            m.d.comb += arbiter.requests[i].eq(input.valid)

        granted = Signal.like(arbiter.grant)
        transfer = Signal()
        selected = Array(inputs)[granted]

        with m.If(transfer):
            m.d.comb += [
                output.valid.eq(selected.valid),
                output.p.p.eq(selected.p),
                output.p.src.eq(granted),
                selected.ready.eq(output.ready)
            ]

        with m.FSM():
            with m.State("IDLE"):
                with m.If(arbiter.requests != 0):
                    m.d.comb += [
                        arbiter.next.eq(1),
                        granted.eq(arbiter.grant),
                        transfer.eq(1)
                    ]
                    with m.If(output.valid & output.ready):
                        m.next = "IDLE"
                    with m.Else():
                        m.next = "TRANSFER"
            with m.State("TRANSFER"):
                    m.d.comb += [
                        granted.eq(arbiter.grant_store),
                        transfer.eq(1)
                    ]
                    with m.If(output.valid & output.ready):
                        m.next = "IDLE"

        return m

class RRStreamLastArbiterPayloadLayout(data.StructLayout):
    last: Signal
    src: Signal

    def __init__(self, n_queues):
        super().__init__({
            "last": 1,
            "src": range(n_queues)
        })

class RRStreamLastArbiter(Component):
    def __init__(self, n_queues):
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(1)).array(n_queues),
            "output": Out(stream.Signature(RRStreamLastArbiterPayloadLayout(n_queues))),
        }))
        self.n_queues = n_queues

    def elaborate(self, _):
        m = Module()

        inputs = self.input
        output = self.output

        arbiter = m.submodules.arbiter = RoundRobinArbiter(len(inputs))

        for i, input in enumerate(inputs):
            m.d.comb += arbiter.requests[i].eq(input.valid)

        granted = Signal.like(arbiter.grant)
        transfer = Signal()
        selected = Array(inputs)[granted]

        with m.If(transfer):
            m.d.comb += [
                output.valid.eq(selected.valid),
                output.p.last.eq(selected.p),
                output.p.src.eq(granted),
                selected.ready.eq(output.ready)
            ]

        with m.FSM():
            with m.State("IDLE"):
                with m.If(arbiter.requests != 0):
                    m.d.comb += [
                        arbiter.next.eq(1),
                        granted.eq(arbiter.grant),
                        transfer.eq(1)
                    ]
                    with m.If(output.valid & output.ready & output.p.last):
                        m.next = "IDLE"
                    with m.Else():
                        m.next = "TRANSFER"
            with m.State("TRANSFER"):
                    m.d.comb += [
                        granted.eq(arbiter.grant_store),
                        transfer.eq(1)
                    ]
                    with m.If(output.valid & output.ready & output.p.last):
                        m.next = "IDLE"

        return m



# this should be used in combination with a MultiQueueFIFO to fulfill the $onehot0 requirement of the output path
class MultiQueueFifoReader(Component):
    def __init__(self, payload_shape, n_queues):
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)).array(n_queues),
            "output": Out(stream.Signature(payload_shape)).array(n_queues)
        }))
        self.n_queues = n_queues

    def elaborate(self, _):
        m = Module()

        arbiter = m.submodules.arbiter = RoundRobinArbiter(self.n_queues)
        m.d.comb += arbiter.next.eq(arbiter.requests != 0)

        for i in range(self.n_queues):
            input = self.input[i]
            output = self.output[i]
            ready_outstanding = Signal(1, name=f"ready_outstanding_{i}")

            m.d.comb += [
                # gate on input valid, as otherwise, if all outputs assert ready,
                # but not all inputs are valid, this grants a output priority,
                # that cannot even read a input, leading to wasted cycles
                arbiter.requests[i].eq(input.valid & output.ready | ready_outstanding),
                input.ready.eq((arbiter.requests != 0) & (arbiter.grant == i)),
                output.valid.eq(input.valid & ~ready_outstanding),
                output.p.eq(input.p)
            ]

            with m.If(output.valid & output.ready & ~input.ready):
                m.d.sync += ready_outstanding.eq(1)

            with m.If(ready_outstanding & input.ready):
                m.d.sync += ready_outstanding.eq(0)

        return m



if __name__ == "__main__":
    print("multi queue fifo")
    MultiQueueFIFO.formal()

    print("combined formal check")
    combined_formal_check(window_size=8, acks_per_window=4)

    # print("formal arq receiver")
    # ArqReceiver.formal()

    # print("formal arq sender")
    # ArqSender.formal()
