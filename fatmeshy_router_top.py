#!/usr/bin/env python3


from amaranth import Module, Mux, Signal
from amaranth.back.rtlil import convert
from amaranth.lib import data, stream, wiring
from amaranth.lib.wiring import Component, In, Out
from arq import AckLayout, AckSignature, ArqPayloadLayout, ArqReceiver, ArqSender, CreditLayout, CreditRXSignature, MultiQueueCreditCounterRX, MultiQueueFIFO, MultiQueueFifoReader, RRStreamArbiter, CreditStream
from debug_utils import event_annotation
from format_utils import add_formatting_attrs
from memory_mapped_router import Config, Flit, FlitStream, FlitWithVC, FlitWithVCStream, MemoryMappedRouter, MemoryMappedRouterConfig, Port, StreamFIFO
from memory_mapped_router_types import CardinalPort
from trace_signal_flow import trace_signal_flow

ArqPayload = ArqPayloadLayout(FlitWithVC, Config.ARQ_WINDOW_SIZE)
ArqStream = stream.Signature(ArqPayload)

class LinkStreamSignature(wiring.Signature):
    def __init__(self, payload_shape):
        super().__init__({
            "valid": Out(1),
            "p": Out(payload_shape),
            "input_error": Out(1),
            "ready": In(1),
        })

LinkStream = LinkStreamSignature(ArqPayload)

class AckCreditLayout(data.StructLayout):
    def __init__(self, window_size, depth, n_queues):
        super().__init__({
            "ack": AckLayout(window_size=window_size),
            "credit": CreditLayout(depth, n_queues)
        })


class AckCreditCombiner(Component):
    def __init__(self, window_size, n_queue, depth):
        super().__init__(wiring.Signature({
            "ack_in": In(AckSignature(window_size=window_size)),
            "credit_in": In(CreditRXSignature(depth, n_queue)),
            "output": Out(stream.Signature(AckCreditLayout(window_size, depth, n_queue)))
        }))

    def elaborate(self, _):
        m = Module()
        out = self.output.p
        outstanding = Signal()

        with m.If((self.credit_in.trigger | self.ack_in.trigger) & ~self.output.ready):
            m.d.sync += outstanding.eq(1)

        with m.If(outstanding & self.output.ready):
            m.d.sync += outstanding.eq(0)

        m.d.comb += [
            self.output.valid.eq(outstanding | self.credit_in.trigger | self.ack_in.trigger),

            # TODO(robin): think about making these trigger on self.output.valid & self.output.ready
            self.ack_in.did_trigger.eq(self.credit_in.trigger),
            self.credit_in.did_trigger.eq(self.ack_in.trigger),

            out.ack.is_nack.eq(self.ack_in.p.is_nack),
            out.ack.seq_is_valid.eq(self.ack_in.p.seq_is_valid),
            out.ack.seq.eq(self.ack_in.p.seq),
            out.credit.eq(self.credit_in.credit)
        ]

        return m

class LinkMux(Component):
    arq_tx: In(ArqStream)

    ack: In(AckSignature(Config.ARQ_WINDOW_SIZE))
    credit: In(CreditRXSignature(Config.INPUT_CHANNEL_DEPTH, Config.N_VC, ))

    link_out: Out(ArqStream)

    def elaborate(self, _):
        m = Module()
        m.submodules.ack_credit_combiner = combiner = AckCreditCombiner(
            window_size=Config.ARQ_WINDOW_SIZE,
            n_queue=Config.N_VC,
            depth=Config.INPUT_CHANNEL_DEPTH
        )
        # TODO(robin): maybe make this priority?
        m.submodules.arbiter = arbiter = RRStreamArbiter(self.arq_tx.p.shape(), 2)

        wiring.connect(m, wiring.flipped(self.ack), combiner.ack_in)
        wiring.connect(m, wiring.flipped(self.credit), combiner.credit_in)
        wiring.connect(m, wiring.flipped(self.arq_tx), arbiter.input[0])

        # combiner -> arbiter.input[1]
        # This is a bit more involved than straight forward connecting it,
        # because we need to encode the credit / ack data into the flit and seq fields
        # wiring.connect(m, combiner.output, arbiter.input[1])
        arb_in_1 = arbiter.input[1]
        m.d.comb += [
            arb_in_1.valid.eq(combiner.output.valid),
            arb_in_1.p.seq.eq(combiner.output.p.ack.seq),
            arb_in_1.p.p.flit.tag.eq(Flit.arq_ack),
            arb_in_1.p.p.flit.data.arq_ack.seq_is_valid.eq(combiner.output.p.ack.seq_is_valid),
            arb_in_1.p.p.flit.data.arq_ack.is_nack.eq(combiner.output.p.ack.is_nack),
            arb_in_1.p.p.flit.data.arq_ack.credit.eq(combiner.output.p.credit),
            combiner.output.ready.eq(arb_in_1.ready),
        ]

        # wiring.connect(m, arbiter.output, wiring.flipped(self.link_out))
        m.d.comb += [
            self.link_out.valid.eq(arbiter.output.valid),
            self.link_out.p.eq(arbiter.output.p.p),
            arbiter.output.ready.eq(self.link_out.ready)
        ]

        # debug annotations
        ack_sent = Signal()
        nack_sent = Signal()
        m.d.comb += [
            ack_sent.eq(arb_in_1.ready & arb_in_1.valid & ~arb_in_1.p.p.flit.data.arq_ack.is_nack),
            nack_sent.eq(arb_in_1.ready & arb_in_1.valid & arb_in_1.p.p.flit.data.arq_ack.is_nack)
        ]
        event_annotation(ack_sent, "ack sent")
        event_annotation(ack_sent, "nack sent")

        return m

class LinkDemux(Component):
    link_in: In(LinkStream)

    arq_rx: Out(ArqStream)

    ack: Out(stream.Signature(AckLayout(Config.ARQ_WINDOW_SIZE), always_ready=True))
    credit: Out(stream.Signature(CreditLayout(Config.INPUT_CHANNEL_DEPTH, Config.N_VC), always_ready=True))


    def elaborate(self, _):
        m = Module()


        arq_ack_flit = self.link_in.p.p.flit.data.arq_ack
        is_ack = self.link_in.p.p.flit.is_ack()

        m.d.comb += [
            self.arq_rx.p.eq(self.link_in.p),

            self.ack.p.seq.eq(self.link_in.p.seq),
            self.ack.p.is_nack.eq(arq_ack_flit.is_nack),
            self.ack.p.seq_is_valid.eq(arq_ack_flit.seq_is_valid),
            self.credit.p.eq(arq_ack_flit.credit),

            self.credit.valid.eq(self.link_in.valid & is_ack),
            self.ack.valid.eq(self.link_in.valid & is_ack),

            self.arq_rx.valid.eq(self.link_in.valid & ~is_ack),


            self.link_in.ready.eq(Mux(
                is_ack,
                1,
                self.arq_rx.ready
            ))
        ]

        return m

class RouterLink(Component):
    input: In(LinkStream)
    output: Out(ArqStream)

    to_router: Out(FlitStream).array(Config.N_VC)
    from_router: In(FlitWithVCStream)
    to_router_credit: Out(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC))

    def elaborate(self, _):
        m = Module()

        # router out -> arq_sender -> link
        m.submodules[f"arq_sender"] = arq_sender = ArqSender(Config.ARQ_WINDOW_SIZE, FlitWithVC)
        m.submodules[f"link_mux"] = link_mux = LinkMux()

        wiring.connect(m, wiring.flipped(self.from_router), arq_sender.input)
        wiring.connect(m, arq_sender.output, link_mux.arq_tx)
        wiring.connect(m, link_mux.link_out, wiring.flipped(self.output))

        # link -> arq_receiver -> MQ FIFO -> MQ Reader -> router in
        m.submodules[f"link_demux"] = link_demux = LinkDemux()
        m.submodules[f"arq_receiver"] = arq_receiver = ArqReceiver(Config.ARQ_WINDOW_SIZE, FlitWithVC, acks_per_window = 4)
        m.submodules[f"input_mq_fifo"] = input_fifo = MultiQueueFIFO(Flit, Config.N_VC, Config.INPUT_CHANNEL_DEPTH)
        m.submodules[f"input_mq_reader"] = input_reader = MultiQueueFifoReader(Flit, Config.N_VC)

        m.submodules[f"credit_counter_rx"] = credit_rx = MultiQueueCreditCounterRX(self, Config.N_VC, Config.INPUT_CHANNEL_DEPTH, updates_per_depth = 4)

        # print(link_in, link_demux.link_in)
        # wiring.connect(m, wiring.flipped(link_in), link_demux.link_in)
        m.d.comb += [
            link_demux.link_in.valid.eq(self.input.valid),
            link_demux.link_in.p.eq(self.input.p),

            # due to credit counting, this is always 1
            # TODO(robin): add module that counts up when we have valid == 1 and ready == 0
            # (should always be zero, but nice for debugging)
            # self.input.ready.eq(link_demux.link_in.ready),
            self.input.ready.eq(1),

            # NOTE: input_error must have same latency as input to avoid spurious failures, add delay regs to match link_demux latency
            arq_receiver.input_error.eq(self.input.input_error)
        ]

        wiring.connect(m, link_demux.arq_rx, arq_receiver.input)

        # wiring.connect(m, arq_receiver.output, input_fifo.input)
        m.d.comb += [
            input_fifo.input.valid.eq(arq_receiver.output.valid),
            input_fifo.input.p.eq(arq_receiver.output.p.flit),
            input_fifo.input.target.eq(arq_receiver.output.p.vc),
            arq_receiver.output.ready.eq(input_fifo.input.ready[arq_receiver.output.p.vc]),
        ]

        # print(m, input_fifo.output, input_reader.input)
        for o, i in zip(input_fifo.output, input_reader.input):
            wiring.connect(m, o, i)

        for vc in range(Config.N_VC):
            wiring.connect(m, input_reader.output[vc], wiring.flipped(self.to_router[vc]))
            m.d.comb += [
                credit_rx.fifo_output_monitor[vc].valid.eq(input_fifo.output[vc].valid),
                credit_rx.fifo_output_monitor[vc].ready.eq(input_fifo.output[vc].ready)
            ]

        wiring.connect(m, link_demux.credit, wiring.flipped(self.to_router_credit))
        wiring.connect(m, link_demux.ack, arq_sender.ack)

        wiring.connect(m, link_mux.credit, credit_rx.credit_out)
        wiring.connect(m, link_mux.ack, arq_receiver.ack)

        return m

class RouterTop(Component):
    local_in: In(FlitStream).array(Config.N_VC)
    local_out: Out(FlitStream).array(Config.N_VC)

    link_n_i: In(LinkStream)
    link_n_o: Out(ArqStream)
    link_s_i: In(LinkStream)
    link_s_o: Out(ArqStream)
    link_e_i: In(LinkStream)
    link_e_o: Out(ArqStream)
    link_w_i: In(LinkStream)
    link_w_o: Out(ArqStream)

    cfg: In(MemoryMappedRouterConfig)

    def links(self):
        return [
            (CardinalPort.north, self.link_n_i, self.link_n_o),
            (CardinalPort.south, self.link_s_i, self.link_s_o),
            (CardinalPort.east, self.link_e_i, self.link_e_o),
            (CardinalPort.west, self.link_w_i, self.link_w_o)
        ]

    def elaborate(self, plat):
        m = Module()
        router = m.submodules.router = MemoryMappedRouter()
        wiring.connect(m, wiring.flipped(self.cfg), router.cfg)

        for i, (r_l_in, l_in) in enumerate(zip(router.local_in, self.local_in)):
            m.submodules[f"input_fifo_{i}"] = fifo = StreamFIFO(l_in, depth=Config.LOCAL_INPUT_FIFO_DEPTH)
            wiring.connect(m, fifo.w_stream, wiring.flipped(l_in))
            wiring.connect(m, r_l_in, fifo.r_stream)

        for r_l_out, l_out in zip(router.local_out, self.local_out):
            wiring.connect(m, r_l_out, wiring.flipped(l_out))

        for dir, link_in, link_out in self.links():
            dir_name = dir.name.lower()
            m.submodules[f"{dir_name}"] = link = RouterLink()

            wiring.connect(m, wiring.flipped(link_in), link.input)
            wiring.connect(m, link.output, wiring.flipped(link_out))

            for vc in range(Config.N_VC):
                wiring.connect(m, router.in_port(Port.const({"port": dir, "vc_id": vc})), link.to_router[vc])
            wiring.connect(m, router.out_port(dir), link.from_router)
            wiring.connect(m, router.credit_port(dir), link.to_router_credit)

        return add_formatting_attrs(m, plat)



def flit_id(f: Flit, idw=32):
    return Mux(f.is_head(), f.data.start.payload[:idw], f.data.payload.payload[:idw])

if __name__ == "__main__":
    m, ports = trace_signal_flow(RouterTop(), Flit, flit_id)
    print(convert(m, ports=ports))
