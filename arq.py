from utils import assertFormal
from formal_utils import FormalScoreboard, FormalScoreboardWolper, AXISStreamContract

from amaranth import Module, Signal, Elaboratable, Value, Cover, Assert, Mux, Assume, ResetSignal
from amaranth.asserts import AnySeq
from amaranth.lib import stream, data, wiring
from amaranth.lib.wiring import In, Out, Component
from amaranth.lib.memory import Memory

def onehot(num):
    return len([1 for k in bin(num) if k == "1"]) == 1

def SeqLayout(window_size):
    return range(2 * window_size)

def ArqPayload(payload_shape, window_size):
    return data.StructLayout({
        "seq": SeqLayout(window_size),
        "p": payload_shape
    })

def AckLayout(window_size):
    return data.StructLayout({
        "is_nack": 1,
        "seq_is_valid": 1, # a invalid seq can happen if we send a nack at the first received packet
        "seq": SeqLayout(window_size)
    })

class ArqSender(Component):
    def __init__(self, window_size, payload_shape):
        self.window_size = window_size
        assert onehot(window_size), "only power of two window size supported "
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)),
            "output": Out(stream.Signature(ArqPayload(payload_shape, window_size))),
            "ack": In(stream.Signature(AckLayout(window_size))),
        }))

    def elaborate(self, _):
        m = Module()

        write_ptr = Signal(range(2 * self.window_size))
        read_ptr = Signal.like(write_ptr)
        send_ptr = Signal.like(read_ptr)
        next_send_ptr = Signal.like(send_ptr)

        m.submodules.buffer = buffer = Memory(shape = self.input.p.shape(), depth = self.window_size, init =[0])
        buffer_write = buffer.write_port(domain = "sync");
        buffer_read = buffer.read_port(domain = "sync");

        push = self.input.valid & self.input.ready
        pop = self.output.valid & self.output.ready

        # full = (write_ptr - read_ptr) == self.window_size
        # expressed based on the uppermost and lowermost index here, because amaranth auto widens the minus operation
        full = (write_ptr[-1] != read_ptr[-1]) & (write_ptr[:-1] == read_ptr[:-1])

        empty = write_ptr == read_ptr
        send_empty = write_ptr == send_ptr
        have_outstanding_to_send = write_ptr != next_send_ptr

        # write handling is simple, we just always write, when we push
        # which is whenever we have space
        m.d.comb += [
            buffer_write.en.eq(push),
            buffer_write.addr.eq(write_ptr),
            buffer_write.data.eq(self.input.p),
        ]
        m.d.comb += self.input.ready.eq(~full)

        # for reads we have to prefetch, as the read port is synchronous.
        # There are three scenarios:
        # 1. The buffer was empty and now contains a word. This is a special case, as we dont have write port transparency,
        #    so we have to delay the read one cycle.
        # 2. A word was read (pop'ed) and we have outstanding data to send. This compares the *current* write pointer to the next send pointer.
        #    It has to be the *current* write pointer to avoid overlap with case 1. In this case, we can prefetch in this cycle, as the write has
        #    occured atleast one cycle ago.
        # 3. A nack was received. Here we can also prefetch in the same cycle as the nack, as the data must have been written atleast one cycle ago.
        #    (We can only receive a nack for something we already send out one)

        nack = Signal()
        last_was_empty_push = Signal()
        m.d.sync += last_was_empty_push.eq(empty & push)
        prefetch = (pop | nack | last_was_empty_push) & have_outstanding_to_send

        # m.d.sync += last_was_empty_push.eq(send_empty & push)
        # prefetch = last_was_empty_push | ((pop | nack) & have_outstanding_to_send)

        # Finally we have to track wether the word we present on the output has already been read
        # (as the send ptr is eagerly incremented on prefetch)
        # Two cases here:
        # 1. Whenever a prefetch happens, in the next cycle we have a valid word to present
        # 2. Whenever a pop (without a prefetch) happens, we no longer have a valid word to present
        send_outstanding = Signal()
        with m.If(prefetch):
            m.d.sync += send_outstanding.eq(1)
        with m.Elif(pop):
            m.d.sync += send_outstanding.eq(0)

        m.d.comb += [
            buffer_read.en.eq(prefetch),
            buffer_read.addr.eq(next_send_ptr),
            self.output.p.p.eq(buffer_read.data),
            self.output.p.seq.eq(send_ptr)
        ]
        m.d.comb += self.output.valid.eq(send_outstanding)


        # the read ptr just gets set by received ack's
        # send ptr increments like a fifo pointer, unless we receive a nack
        m.d.comb += next_send_ptr.eq(send_ptr)
        with m.If(push):        #
            m.d.sync += write_ptr.eq(write_ptr + 1)

        with m.If(pop):
            m.d.comb += next_send_ptr.eq(send_ptr + 1)

        next_read_ptr = Signal.like(read_ptr)
        m.d.comb += next_read_ptr.eq(read_ptr)
        m.d.sync += read_ptr.eq(next_read_ptr)

        m.d.comb += self.ack.ready.eq(1)
        with m.If(self.ack.valid & self.ack.ready):
            with m.If(self.ack.p.seq_is_valid):
                # we get the ack that was received correctly, so we want to "read" the word after that
                m.d.comb += next_read_ptr.eq(self.ack.p.seq + 1)


            with m.If(self.ack.p.is_nack):
                m.d.comb += next_send_ptr.eq(next_read_ptr)
                m.d.comb += nack.eq(1)

        m.d.sync += send_ptr.eq(next_send_ptr)

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

                # m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);
                m.submodules.scoreboard = scoreboard = FormalScoreboardWolper();

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
            "input": In(stream.Signature(payload_shape, always_ready = True))
        }))

    def elaborate(self, _):
        m = Module()

        buffer = Signal.like(self.input.p)
        buffer_valid = Signal()

        m.d.comb += self.output.p.eq(Mux(self.input.valid, self.input.p, buffer))
        m.d.comb += self.output.valid.eq(Mux(self.input.valid, self.input.valid, buffer_valid))

        with m.If(self.output.ready & self.output.valid):
            m.d.sync += buffer_valid.eq(0)

        with m.If(self.input.valid & ~self.output.ready):
            m.d.sync += buffer_valid.eq(1)
            m.d.sync += buffer.eq(self.input.p)

        return m

class ArqReceiver(Component):
    def __init__(self, window_size, payload_shape, acks_per_window = 4):
        self.window_size = window_size
        self.words_per_ack = self.window_size // acks_per_window
        assert onehot(window_size), "only power of two window size supported "
        super().__init__(wiring.Signature({
            "output": Out(stream.Signature(payload_shape)),
            "input": In(stream.Signature(ArqPayload(payload_shape, window_size))),
            "ack": Out(stream.Signature(AckLayout(window_size))),
        }))

    def elaborate(self, _):
        m = Module()

        last_seq = Signal.like(self.input.p.seq, init = -1)
        last_seq_valid = Signal()
        expected_seq = Signal.like(self.input.p.seq)
        m.d.comb += expected_seq.eq(last_seq + 1)
        push = self.input.valid & self.input.ready

        input_seq_valid = self.input.valid & (self.input.p.seq == expected_seq)
        input_seq_valid_dbg = Signal()
        m.d.comb += input_seq_valid_dbg.eq(input_seq_valid )

        with m.If(push & input_seq_valid_dbg):
            m.d.sync += last_seq_valid.eq(1),
            m.d.sync += last_seq.eq(self.input.p.seq)

        m.d.comb += [
            self.input.ready.eq(self.output.ready | (self.input.valid & ~input_seq_valid)),
            self.output.p.eq(self.input.p.p),
            self.output.valid.eq(input_seq_valid)
        ]

        # ack handling
        # we want lww semantics, ie if the ack stream was blocked,
        # we always want to send the latest ack info
        m.submodules.ack_sender = ack_sender = LWWReg(self.ack.p.shape())

        wiring.connect(m, ack_sender.output, wiring.flipped(self.ack))

        def send_ack(is_nack: bool, seq, seq_valid):
            return [
                ack_sender.input.valid.eq(1),
                ack_sender.input.p.is_nack.eq(is_nack),
                ack_sender.input.p.seq_is_valid.eq(seq_valid),
                ack_sender.input.p.seq.eq(seq)
            ]

        # normal ack flow: ack every n'th block
        word_counter = Signal(range(self.words_per_ack))
        with m.If(push):
            with m.If(word_counter == (self.words_per_ack - 1)):
                m.d.sync += word_counter.eq(0)
                m.d.comb += send_ack(False, self.input.p.seq, True)
            with m.Else():
                m.d.sync += word_counter.eq(word_counter + 1)

        # TODO(robin): timeout for ack

        # send nack for out of order seq's
        with m.If(self.input.valid & ~input_seq_valid):
            m.d.comb += send_ack(True, last_seq, last_seq_valid)

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
                "output": Out(stream.Signature(payload_shape))
            }))

        def elaborate(self, _):
            m = Module()

            buf_layout = data.StructLayout({
                "valid": 1,
                "p": self.payload_shape
            })

            bufs = [Signal(buf_layout) for _ in range(self.link_delay)]
            for i in range(self.link_delay - 1):
                m.d.sync += bufs[i + 1].eq(bufs[i])

            if self.lossy:
                gate = AnySeq(1)
            else:
                gate = 1

            m.d.comb += [
                self.output.valid.eq(bufs[-1].valid & gate),
                self.output.p.eq(bufs[-1].p),
                self.input.ready.eq(1)
            ]

            m.d.sync += [
                bufs[0].p.eq(self.input.p),
                bufs[0].valid.eq(self.input.valid)
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
            # m.submodules.scoreboard = scoreboard = FormalScoreboard(self.payload_shape);
            m.submodules.scoreboard = scoreboard = FormalScoreboardWolper();

            m.submodules.tx_link = tx_link = LinkModel(arq_sender.output.p.shape(), self.link_delay, lossy=True)
            m.submodules.rx_link = rx_link = LinkModel(arq_receiver.ack.p.shape(), self.link_delay)

            # with credit counting this should be a assert
            m.d.comb += Assume(self.output.ready)

            # for debug
            # m.d.comb += Assume(~ResetSignal())

            wiring.connect(m, wiring.flipped(self.input), arq_sender.input)

            wiring.connect(m, arq_sender.output, tx_link.input)
            wiring.connect(m, tx_link.output, arq_receiver.input)

            wiring.connect(m, arq_receiver.ack, rx_link.input)
            wiring.connect(m, rx_link.output, arq_sender.ack)

            wiring.connect(m, arq_receiver.output, wiring.flipped(self.output))


            m.d.comb += [
                scoreboard.input.valid.eq(self.input.valid & self.input.ready),
                scoreboard.input.p.eq(self.input.p),

                scoreboard.output.valid.eq(self.output.valid & self.output.ready),
                scoreboard.output.p.eq(self.output.p)
            ]

            return m


    spec = FormalCheck(window_size = window_size, payload_shape = payload_shape, acks_per_window = acks_per_window)
    for mode in ["cover", "prove"]:
        print(mode)
        assertFormal(spec, ports=[
            spec.input.valid,
            spec.input.ready,
            Value.cast(spec.input.p),
            spec.output.valid,
            spec.output.ready,
            Value.cast(spec.output.p),
        ], mode=mode)


if __name__ == "__main__":
    print("combined formal check")
    combined_formal_check()

    print("formal arq receiver")
    ArqReceiver.formal()

    print("formal arq sender")
    ArqSender.formal()
