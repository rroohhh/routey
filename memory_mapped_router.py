#!/usr/bin/env python3

from collections import defaultdict
from typing import Callable
import typing

from arq import CreditLayout, CreditStream, LWWReg, MultiQueueCreditCounterTX, RRStreamArbiter, RRStreamLastArbiter
from debug_utils import mark_debug
from tagged_union import *
from format_utils import *
from memory_mapped_router_types import CardinalPort
from amaranth import Signal, Mux, Print, Format, Array
from amaranth.sim import Simulator, Period
from amaranth.lib import data, stream, wiring
from amaranth.lib.fifo import SyncFIFO as SyncFIFOAmaranth
from amaranth.lib.wiring import Component, In, Out

from util import EqDefaultDict

class StreamFIFO(Component):
    def __init__(self, payload_shape, *, depth=2):
        self.depth = depth
        if isinstance(payload_shape, wiring.FlippedInterface):
            payload_shape = wiring.flipped(payload_shape)
        if isinstance(payload_shape, stream.Interface):
            payload_shape = payload_shape.payload

        payload_shape = payload_shape.shape()

        super().__init__(wiring.Signature({
            "r_stream": Out(stream.Signature(payload_shape)),
            "w_stream": In(stream.Signature(payload_shape)),
        }))


    def elaborate(self, _):
        m = Module()
        if self.depth == 0:
            wiring.connect(m, wiring.flipped(self.r_stream), wiring.flipped(self.w_stream))
        elif self.depth == 1:
            buffer = Signal.like(self.w_stream.p, reset_less = True)
            buffer_valid = Signal()

            with m.If(self.r_stream.ready & self.r_stream.valid):
                m.d.sync += buffer_valid.eq(0)

            with m.If(self.w_stream.ready & self.w_stream.valid):
                m.d.sync += buffer.eq(self.w_stream.p)
                m.d.sync += buffer_valid.eq(1)

            m.d.comb += [
                self.w_stream.ready.eq(~buffer_valid | self.r_stream.ready),
                self.r_stream.valid.eq(buffer_valid),
                self.r_stream.p.eq(buffer)
            ]
        else:
            fifo = m.submodules.fifo = SyncFIFOAmaranth(width=len(self.r_stream.p.as_value()), depth=self.depth)
            wiring.connect(m, wiring.flipped(self.r_stream), fifo.r_stream)
            wiring.connect(m, wiring.flipped(self.w_stream), fifo.w_stream)
        return m


class Config:
    # for formal
    # LINK_BITS = 25
    # MUX_COUNT = 1
    # COORD_BITS = 4

    # 64 bit payload + 8 bit byteen
    FLIT_SIZE = 64 + 8
    COORD_BITS = 6

    LINK_COUNT = 4 # one for each cardinal direction

    MUX_COUNT = 5
    LINK_BITS = 18

    # calculate link bits from flit size
    # 3 bits tag
    # 8 bits sequence number
    # 8 bits checksum
    # MUX_COUNT * 2 bits for link id
    # LINK_BITS = int(ceil((FLIT_SIZE + 3 + 8 + 8 + (MUX_COUNT * 2)) / (2 * MUX_COUNT)) * 2)

    LOCAL_INPUT_FIFO_DEPTH = 2
    INPUT_CHANNEL_FIFO_DEPTH = 1
    INPUT_CHANNEL_OUTPUT_FIFO_DEPTH = 0
    INPUT_CHANNEL_ROUTE_PIPELINE_DEPTH = INPUT_CHANNEL_FIFO_DEPTH
    CROSSBAR_OUTPUT_FIFO_DEPTH = 0

    INPUT_CHANNEL_DEPTH = 32
    ARQ_WINDOW_SIZE = 64

    N_VC = 2


VcID = range(Config.N_VC)

class Coordinate(data.Struct):
    x: Config.COORD_BITS
    y: Config.COORD_BITS


class FlowID(Coordinate):
    pass

class RoutingTarget(data.Struct):
    is_flow: 1
    target: Coordinate

class FlitStart(data.Struct):
    target: RoutingTarget
    payload: Config.FLIT_SIZE - RoutingTarget.as_shape().size

class FlitPayload(data.Struct):
    payload: Config.FLIT_SIZE

class FlitTail(FlitPayload):
    ...

class FlitStartAndEnd(FlitStart):
    ...

# this should never enter the router, it is used for arq internal signaling
class FlitARQAck(data.Struct):
    credit: CreditLayout(Config.INPUT_CHANNEL_DEPTH, Config.N_VC)
    seq_is_valid: 1
    is_nack: 1

    payload: Config.FLIT_SIZE - CreditLayout(Config.INPUT_CHANNEL_DEPTH, Config.N_VC).size - 2


class Flit(TaggedUnion):
    start: FlitStart
    tail: FlitTail
    payload: FlitPayload
    start_and_end: FlitStartAndEnd
    arq_ack: FlitARQAck

    def is_last(self):
        return self.tag.matches(Flit.start_and_end, Flit.tail)

    def is_head(self):
        return self.tag.matches(Flit.start_and_end, Flit.start)

    def is_ack(self):
        return self.tag.matches(Flit.arq_ack)

Config.ENCODED_FLIT_SIZE = data.Layout.cast(Flit).size

FlitStream = stream.Signature(Flit)

class FlitWithVC(data.Struct):
    flit: Flit
    vc: VcID

FlitWithVCStream = stream.Signature(FlitWithVC)

class Port(data.Struct):
    port: CardinalPort
    vc_id: VcID

    @classmethod
    def __members__(cls) -> dict:
        return {
            cls.name_for(v := cls.const({"port": dir, "vc_id": vc})) : v
            for _, dir in CardinalPort.__members__.items()
            for vc in VcID
        }

    @classmethod
    def name_for(cls, value) -> str:
        return f"{value.port.name.lower()}_vc_{value.vc_id}"

class RouteResult(data.Struct):
    new_target: RoutingTarget
    port: Port

RouteComputerConfig = wiring.Signature({
    "position": Out(Coordinate),
    "xy": Out(1),
    "flow_lookup": In(stream.Signature(FlowID)),
    "flow_result": Out(stream.Signature(RouteResult, always_ready=True))
})


class RoutingInput(data.Struct):
    vc: VcID
    target: RoutingTarget

# responsible for calculating which port to send this packet
# for now just takes a coordinate and outputs a target port
#
# This implements deterministic distributed routing in form of XY routing
# By using a deterministic routing algorithm, we ensure the ordering of packets
# However this does not use for example congestion info to route around congested paths
#
# This samples the config whenever a new coordinate is fed in
#
# TODO(robin): add a flow id + lookuptable configuration routing scheme (maybe shared buffer )
# add source based routing aswell
class RouteComputer(Component):
    input: In(stream.Signature(RoutingInput))
    result: Out(stream.Signature(RouteResult))
    cfg: In(RouteComputerConfig)

    def elaborate(self, _):
        m = Module()

        with m.If(self.input.payload.target.is_flow):
            m.submodules.flow_result_reg = flow_result_reg = LWWReg(RouteResult)

            wiring.connect(m, wiring.flipped(self.cfg.flow_result), flow_result_reg.input)
            wiring.connect(m, flow_result_reg.output, wiring.flipped(self.result))

            m.d.comb += [
                self.cfg.flow_lookup.valid.eq(self.input.valid),
                self.cfg.flow_lookup.p.eq(self.input.payload.target.target),
                self.input.ready.eq(self.cfg.flow_lookup.ready)
            ]
        with m.Else():
            m.d.comb += self.input.ready.eq(self.result.ready)
            m.d.comb += self.result.valid.eq(self.input.valid)

            input_x = self.input.payload.target.target.x
            input_y = self.input.payload.target.target.y

            my_x = self.cfg.position.x
            my_y = self.cfg.position.y
            res = self.result.payload

            m.d.comb += res.new_target.eq(self.input.payload.target)
            m.d.comb += res.port.vc_id.eq(self.input.payload.vc)

            with m.If(self.cfg.xy):
                with m.If(input_x != my_x):
                    m.d.comb += res.port.port.eq(Mux(input_x > my_x, CardinalPort.east, CardinalPort.west))
                with m.Elif(input_y != my_y):
                    m.d.comb += res.port.port.eq(Mux(input_y > my_y, CardinalPort.south, CardinalPort.north))
                with m.Else():
                    m.d.comb += res.port.port.eq(CardinalPort.local)
            with m.Else():
                with m.If(input_y != my_y):
                    m.d.comb += res.port.port.eq(Mux(input_y > my_y, CardinalPort.south, CardinalPort.north))
                with m.Elif(input_x != my_x):
                    m.d.comb += res.port.port.eq(Mux(input_x > my_x, CardinalPort.east, CardinalPort.west))
                with m.Else():
                    m.d.comb += res.port.port.eq(CardinalPort.local)

        return m


COUNTER_SIZE = 32

class RoutedFlit(data.Struct):
    flit: Flit
    last: 1
    target: Port

RoutedFlitStream = stream.Signature(RoutedFlit)

InputChannelConfig = wiring.Signature({
    "invalid_flit_ctr": In(COUNTER_SIZE)
})

# assumes clean input
# TODO(robin): input cleaner
class InputChannel(Component):
    flit_in: In(FlitStream)
    flit_out: Out(RoutedFlitStream)
    cfg: In(InputChannelConfig)
    route_computer_cfg: In(RouteComputerConfig)

    def __init__(self, vc, name):
        super().__init__()
        # super().__init__(path=(name + "_input_channel",))
        self._name = name
        self.vc = vc

    def elaborate(self, _):
        m = Module()
        route_computer = m.submodules.route_computer = RouteComputer()
        wiring.connect(m, wiring.flipped(self.route_computer_cfg), route_computer.cfg)

        flit_out = self.flit_out
        flit_in_before_fifo = self.flit_in
        input_fifo = m.submodules.input_fifo = StreamFIFO(self.flit_in, depth=Config.INPUT_CHANNEL_FIFO_DEPTH)

        # we do not need to wait for the route computer if the next flit wont have routing information
        # this is the case if the previous flit was the last flit of a so, packet the next one will have to have routing info
        next_flit_in_has_routing = Signal(reset=1)
        with m.If(flit_in_before_fifo.valid & flit_in_before_fifo.ready):
            m.d.sync += next_flit_in_has_routing.eq(flit_in_before_fifo.p.is_last())

        route_computer_stall = Signal()
        input_stall = route_computer_stall

        m.d.comb += [
            flit_in_before_fifo.ready.eq(input_fifo.w_stream.ready & ~input_stall),
            input_fifo.w_stream.valid.eq(flit_in_before_fifo.valid & ~input_stall),
            input_fifo.w_stream.p.eq(flit_in_before_fifo.p)
        ]

        # start and start_and_end have the same layout, so this is always valid
        m.d.comb += [
            route_computer.input.payload.target.eq(flit_in_before_fifo.payload.data.start.target),
            route_computer.input.payload.vc.eq(self.vc)
        ]

        with m.FSM(name="route_computer_fsm"):
            with m.State("idle"):
                with m.If(next_flit_in_has_routing):
                    m.d.comb += [
                        route_computer.input.valid.eq(flit_in_before_fifo.valid),
                        route_computer_stall.eq(~route_computer.input.ready)
                    ]
                    # if we fed this into the route computer, but we did not feed it into the fifo yet, we cannot longer assert
                    # valid, as otherwise we read the same flit multiple times
                    with m.If(route_computer.input.valid & route_computer.input.ready & ~input_fifo.w_stream.ready):
                        m.next = "wait_for_new"
            with m.State("wait_for_new"):
                with m.If(input_fifo.w_stream.valid & input_fifo.w_stream.ready):
                    m.next = "idle"

        route_result_buffer = m.submodules.route_result_fifo = StreamFIFO(
            route_computer.result,
            depth=Config.INPUT_CHANNEL_ROUTE_PIPELINE_DEPTH
        )
        wiring.connect(m, route_computer.result, route_result_buffer.w_stream)

        route_result = route_result_buffer.r_stream
        flit_in = input_fifo.r_stream

        # track this to reduce combinatorial path for the output stuff
        next_flit_out_has_routing = Signal(reset=1)
        with m.If(flit_out.valid & flit_out.ready):
            m.d.sync += next_flit_out_has_routing.eq(flit_out.p.flit.is_last())

        # finally combine the buffered flits with the routing result
        m.d.comb += [
            flit_in.ready.eq(flit_out.ready & flit_out.valid),
            # rewrite old target with the new target obtained from the route computer
            flit_out.p.flit.data.start.target.eq(Mux(next_flit_out_has_routing, route_result.p.new_target, flit_in.payload.data.start.target)),
            flit_out.p.flit.data.start.payload.eq(flit_in.payload.data.start.payload),
            flit_out.p.flit.tag.eq(flit_in.p.tag),
            flit_out.p.target.eq(route_result.p.port),
            flit_out.p.last.eq(flit_in.p.is_last()),
            flit_out.valid.eq(flit_in.valid & route_result.valid),
            route_result.ready.eq(flit_out.ready & flit_out.valid & flit_out.p.flit.is_last())
        ]

        return m

class VCAllocatorInput(data.Struct):
    target: Port
    last: 1

class VCAllocator(Component):
    def __init__(self, should_connect: Callable[[Port, Port], bool] = None):
        self.should_connect = should_connect
        self.port_order = list(Port.__members__().values())
        self.credit_port_order = [port for port in CardinalPort.__members__.values() if port != CardinalPort.local]
        n_ports = len(self.port_order)
        super().__init__({
            "inputs": In(stream.Signature(VCAllocatorInput)).array(n_ports), # is last
            "credit": In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC)).array(len(self.credit_port_order)),
            "outputs": Out(stream.Signature(0)).array(n_ports)
        })

    def elaborate(self, _):
        m = Module()

        PortIdx = len(self.port_order)

        arb_for = EqDefaultDict(lambda: stream.Signature(range(PortIdx)).create())
        inputs_for = EqDefaultDict(list)

        input_ready = [[] for _ in range(PortIdx)]

        for target in self.port_order:
            srcs, inputs_for_arb = list(zip(*list(
                (i, input) for i, (src, input) in enumerate(zip(self.port_order, self.inputs)) if self.should_connect(src, target)
            )))
            m.submodules[f"credit_counter_tx_{Port.name_for(target)}_arb"] = arb = RRStreamLastArbiter(len(inputs_for_arb))

            # print(Port.name_for(target), srcs)
            inputs_for[target] = srcs

            for i, (input_idx, input) in enumerate(zip(srcs, inputs_for_arb)):
                m.d.comb += [
                    arb.input[i].valid.eq(input.valid & (input.p.target == target)),
                    arb.input[i].p.eq(input.p.last),
                ]
                input_ready[input_idx].append(arb.input[i].ready & arb.input[i].valid)

            m.d.comb += [
                arb_for[target].valid.eq(arb.output.valid),
                arb_for[target].p.eq(Array(srcs)[arb.output.p.src]),
                arb.output.ready.eq(arb_for[target].ready)
            ]

        for i, input in enumerate(self.inputs):
            m.d.comb += input.ready.eq(Cat(input_ready[i]).any())

        output_valid = [[] for _ in range(PortIdx)]

        for name, port in CardinalPort.__members__.items():
            if port != CardinalPort.local:
                m.submodules[f"credit_counter_tx_{name}"] = credit_tx = MultiQueueCreditCounterTX(range(PortIdx), Config.N_VC, Config.INPUT_CHANNEL_DEPTH)
                wiring.connect(m, wiring.flipped(self.credit[self.credit_port_order.index(port)]), credit_tx.credit_in)

            for vc_id in range(Config.N_VC):
                src_port = Port.const({"port": port, "vc_id": vc_id})

                arb = arb_for[src_port]
                if port != CardinalPort.local:
                    wiring.connect(m, arb, credit_tx.input[vc_id])
                    credit_tx_out = credit_tx.output[vc_id]

                    p = credit_tx_out.p
                    valid = credit_tx_out.valid
                    m.d.comb += [
                        credit_tx_out.ready.eq(Array(self.outputs)[credit_tx_out.p].ready)
                    ]
                else: # local has no credit counting, so always ready
                    p = arb.p
                    valid = arb.valid
                    m.d.comb += [
                        arb.ready.eq(Array(self.outputs)[arb.p].ready)
                    ]

                # print(Port.name_for(src_port), inputs_for[src_port])
                for input in inputs_for[src_port]:
                    # print(input, p)
                    output_valid[input].append(valid & (p == input))

        for i, output in enumerate(self.outputs):
            m.d.comb += output.valid.eq(Cat(output_valid[i]).any())

        return m

class StreamCrossbarOutput(Component):
    def __init__(self, n_inputs, target: Port):
        super().__init__(wiring.Signature({
            "inputs": In(stream.Signature(RoutedFlit)).array(n_inputs),
            "output": Out(FlitWithVCStream),
            "input_ready": Out(n_inputs)
        }))
        if isinstance(target, data.Const):
            target = [target]
        self._target = target

    def elaborate(self, _):
        m = Module()
        inputs = self.inputs
        target = self._target


        m.submodules["arbiter"] = arb = RRStreamArbiter(FlitWithVC, len(inputs))
        for i, input in enumerate(inputs):
            m.d.comb += [
                arb.input[i].valid.eq(input.valid & Value.cast(input.p.target).matches(*target)),
                arb.input[i].p.flit.eq(input.p.flit),
                arb.input[i].p.vc.eq(input.p.target.vc_id),
                self.input_ready[i].eq(arb.input[i].ready)
            ]

        m.d.comb += [
            self.output.valid.eq(arb.output.valid),
            self.output.p.eq(arb.output.p.p),
            arb.output.ready.eq(self.output.ready)
        ]

        return m

class StreamTee(Component):
    def __init__(self, payload_shape, n_output):
        super().__init__(wiring.Signature({
            "input": In(stream.Signature(payload_shape)),
            "output": Out(stream.Signature(payload_shape)).array(n_output)
        }))

    def elaborate(self, _):
        m = Module()

        in_stalled = Signal()
        new_input = self.input.valid & ~in_stalled
        stalled = Signal(len(self.output))
        next_stalled = Signal(len(self.output))
        m.d.sync += stalled.eq(next_stalled)

        m.d.comb += self.input.ready.eq(~next_stalled.any())
        m.d.sync += in_stalled.eq(self.input.valid & ~self.input.ready)

        for i, output in enumerate(self.output):
            m.d.comb += next_stalled[i].eq(output.valid & ~output.ready)
            m.d.comb += [
                output.valid.eq(new_input | stalled[i]),
                output.p.eq(self.input.p)
            ]

        return m

class RouterCrossbar(Component):
    def __init__(self, should_connect: Callable[[Port, Port], bool] = None):
        if should_connect is None:
            def sc(a, b):
                if hasattr(a, "port"):
                    a = a.port
                if hasattr(b, "port"):
                    b = b.port
                if isinstance(b, typing.Iterable):
                    values = set(p.port for p in b)
                    values.discard(a)
                    return len(values) > 0
                else:
                    return a != b

                # lambda a, b: a.port != b.port


            self.should_connect = sc

        self.input_port_order = list(Port.__members__().values())
        self.output_port_order = [p for p in CardinalPort.__members__.values() if p != CardinalPort.local]
        self.credit_port_order = self.output_port_order

        super().__init__(wiring.Signature({
            "inputs": In(RoutedFlitStream).array(len(self.input_port_order)),
            "credit": In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC)).array(len(self.input_port_order)),
            "cardinal_outputs": Out(FlitWithVCStream).array(len(self.output_port_order)),
            "local_outputs": Out(FlitStream).array(Config.N_VC)
        }))

    def credit_for(self, port: CardinalPort):
        return self.credit[self.credit_port_order.index(port)]

    def input_for(self, port: Port):
        return self.inputs[self.input_port_order.index(port)]

    def output_for(self, port: CardinalPort):
        if isinstance(port, CardinalPort):
            return self.cardinal_outputs[self.output_port_order.index(port)]
        else:
            assert port.port == CardinalPort.local
            return self.local_outputs[port.vc_id]

    def target_output_pairs(self):
        cardinal_names = [port.name.lower() for port in self.output_port_order]
        cardinal_ports = [[Port.const({"port": port, "vc_id": vc_id}) for vc_id in range(Config.N_VC)] for port in self.output_port_order]
        local_ports = [Port.const({"port": CardinalPort.local, "vc_id": vc_id}) for vc_id in range(Config.N_VC)]
        local_names = [Port.name_for(p) for p in local_ports]

        cardinal_connect = [wiring.connect] * len(cardinal_ports)
        def local_c(m, i, o):
            m.d.comb += [o.valid.eq(i.valid), o.p.eq(i.p.flit), i.ready.eq(o.ready)]

        local_connect = [local_c] * len(local_ports)

        yield from zip(cardinal_names, cardinal_ports, self.cardinal_outputs, cardinal_connect)
        yield from zip(local_names, local_ports, self.local_outputs, local_connect)

    def elaborate(self, _):
        m = Module()

        m.submodules["vc_allocator"] = alloc = VCAllocator(self.should_connect)

        for credit_in, credit_alloc in zip(self.credit, alloc.credit):
            wiring.connect(m, wiring.flipped(credit_in), credit_alloc)


        cb_input_ports = []
        for name, port in CardinalPort.__members__.items():
            m.submodules[f"crossbar_{name}_arb"] = vc_arb = RRStreamArbiter(RoutedFlit, Config.N_VC)

            vc_arb_out = stream.Signature(RoutedFlit).create(path=[name])
            m.d.comb += [
                vc_arb_out.valid.eq(vc_arb.output.valid),
                vc_arb_out.p.eq(vc_arb.output.p.p),
                vc_arb.output.ready.eq(vc_arb_out.ready)
            ]
            cb_input_ports.append((port, vc_arb_out))

            for vc_id in range(Config.N_VC):
                src_port = Port.const({"port": port, "vc_id": vc_id})

                alloc_in = alloc.inputs[self.input_port_order.index(src_port)]
                alloc_out = alloc.outputs[self.input_port_order.index(src_port)]
                input = self.input_for(src_port)

                m.submodules[f"crossbar_{Port.name_for(src_port)}_tee"] = tee = StreamTee(0, 2)

                alloc_output = tee.output[0]
                arb_output = tee.output[1]

                m.d.comb += [
                    tee.input.valid.eq(input.valid),
                    input.ready.eq(tee.input.ready),

                    alloc_in.valid.eq(alloc_output.valid),
                    alloc_in.p.target.eq(input.p.target),
                    alloc_in.p.last.eq(input.p.last),
                    alloc_output.ready.eq(alloc_in.ready),

                    vc_arb.input[vc_id].valid.eq(alloc_out.valid & arb_output.valid),
                    vc_arb.input[vc_id].p.eq(input.p),

                    alloc_out.ready.eq(vc_arb.input[vc_id].ready & arb_output.valid),
                    arb_output.ready.eq(vc_arb.input[vc_id].ready & alloc_out.valid)
                ]

        input_readys = defaultdict(list)
        for name, target, output_stream, connect in self.target_output_pairs():
            inputs_for_output = list(
                input for (src, input) in cb_input_ports if self.should_connect(src, target)
            )
            output = m.submodules[f"crossbar_output_{name}"] = StreamCrossbarOutput(len(inputs_for_output), target)

            for i, input in enumerate(inputs_for_output):
                wiring.connect(m, output.inputs[i], input)
            connect(m, output.output, wiring.flipped(output_stream))

            for i, input in enumerate(inputs_for_output):
                input_readys[input].append(output.input_ready[i])

        for _, input in cb_input_ports:
            # print(input_readys[input], input)
            m.d.comb += input.ready.eq(sum(input_readys[input])[0])

        return m


MemoryMappedRouterConfig = wiring.Signature({
    **{f"{port}_route_computer_cfg": Out(RouteComputerConfig) for port in Port.__members__().keys()},
    **{f"{port}_cfg": Out(InputChannelConfig) for port in Port.__members__().keys()}
})

class MemoryMappedRouter(Component):
    local_in: In(FlitStream).array(Config.N_VC)
    local_out: Out(FlitStream).array(Config.N_VC)

    north_in: In(FlitStream).array(Config.N_VC)
    north_out: Out(FlitWithVCStream)
    north_credit_in: In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC))
    south_in: In(FlitStream).array(Config.N_VC)
    south_out: Out(FlitWithVCStream)
    south_credit_in: In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC))
    east_in: In(FlitStream).array(Config.N_VC)
    east_out: Out(FlitWithVCStream)
    east_credit_in: In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC))
    west_in: In(FlitStream).array(Config.N_VC)
    west_out: Out(FlitWithVCStream)
    west_credit_in: In(CreditStream(Config.INPUT_CHANNEL_DEPTH, Config.N_VC))

    cfg: In(MemoryMappedRouterConfig)

    def in_port(self, port: Port):
        return getattr(self, f"{port.port.name.lower()}_in")[port.vc_id]

    def credit_port(self, port: CardinalPort):
        return getattr(self, f"{port.name.lower()}_credit_in")

    def credit_ports(self):
        for port in CardinalPort.__members__.values():
            if port != CardinalPort.local:
                yield (port, self.credit_port(port))

    def out_port(self, port: CardinalPort):
        if isinstance(port, CardinalPort):
            return getattr(self, f"{port.name.lower()}_out")
        else:
            assert port.port == CardinalPort.local
            return getattr(self, f"{port.port.name.lower()}_out")[port.vc_id]

    def in_ports(self):
        for name, port in Port.__members__().items():
            yield (name.lower(), self.in_port(port), port)

    def out_ports(self):
        for name, port in CardinalPort.__members__.items():
            if port != CardinalPort.local:
                yield (name.lower(), self.out_port(port), port)

        for vc_id in range(Config.N_VC):
            port = Port.const({"port": CardinalPort.local, "vc_id": vc_id})
            yield (Port.name_for(port), self.out_port(port), port)

    def elaborate(self, _):
        m = Module()

        m.submodules.crossbar = crossbar = RouterCrossbar()

        for name, in_port, port in self.in_ports():
            # input path: InputChannel -> FIFO -> Crossbar
            channel = m.submodules[f"{name}_input_channel"] = InputChannel(port.vc_id, name)
            # print(channel.route_computer_cfg, self.cfg.route_computer_cfg)
            wiring.connect(m, channel.route_computer_cfg, wiring.flipped(getattr(self.cfg, f"{name}_route_computer_cfg")))
            wiring.connect(m, channel.cfg, wiring.flipped(getattr(self.cfg, f"{name}_cfg")))
            wiring.connect(m, channel.flit_in, wiring.flipped(in_port))

            crossbar_in_buffer = m.submodules[f"{name}_input_channel_output_fifo"] = StreamFIFO(channel.flit_out.p, depth=Config.INPUT_CHANNEL_OUTPUT_FIFO_DEPTH)
            wiring.connect(m, channel.flit_out, crossbar_in_buffer.w_stream)

            crossbar_in = crossbar.input_for(port)
            wiring.connect(m, crossbar_in_buffer.r_stream, crossbar_in)

        for port, credit_port in self.credit_ports():
            wiring.connect(m, wiring.flipped(credit_port), crossbar.credit_for(port))


        for name, out_port, port in self.out_ports():
            crossbar_out = crossbar.output_for(port)

            # output path: put a FIFO after the crossbar output
            crossbar_out_buffer = m.submodules[f"{name}_crossbar_output_fifo"] = StreamFIFO(crossbar_out, depth=Config.CROSSBAR_OUTPUT_FIFO_DEPTH)
            wiring.connect(m, crossbar_out, crossbar_out_buffer.w_stream)
            wiring.connect(m, crossbar_out_buffer.r_stream, wiring.flipped(out_port))


        mark_debug(self.local_in, self.local_out)

        # Value.cast(self.local_in.payload).attrs["debug_item"] = 1
        # self.local_in.ready.attrs["debug_item"] = 1
        # self.local_in.valid.attrs["debug_item"] = 1
        # Value.cast(self.local_out.payload).attrs["debug_item"] = 1
        # self.local_out.ready.attrs["debug_item"] = 1
        # self.local_out.valid.attrs["debug_item"] = 1

        return m

async def send_packet(ctx, port, target, n_payload):
    tags = [Flit.start_and_end]
    if n_payload > 1:
        tags = [Flit.start] + [Flit.payload] * (n_payload - 2) + [Flit.tail]

    ctx.set(port.valid, 1)
    for i, tag in enumerate(tags):
        ctx.set(port.payload.tag, tag)
        if i == 0:
            ctx.set(port.payload.data.start_and_end.payload, i)
            ctx.set(port.payload.data.start_and_end.target.target.x, target[0])
            ctx.set(port.payload.data.start_and_end.target.target.y, target[1])
            # ctx.set(port.payload.data.start_and_end.target.vc, target[2])
        else:
            ctx.set(port.payload.data.payload.payload, i)
        await ctx.tick().until(port.ready & port.valid)
    ctx.set(port.valid, 0)


def sim():
    grid_size = 2
    n_packets = 10

    m = Module()

    routers = [[MemoryMappedRouter() for _ in range(grid_size)] for _ in range(grid_size)]
    for x in range(grid_size):
        for y in range(grid_size):
            router = m.submodules[f"router_{x}_{y}"] = routers[x][y]
            for port in Port.__members__().values():
                m.d.comb += [
                    getattr(router.cfg, f"{Port.name_for(port)}_route_computer_cfg").position.x.eq(x),
                    getattr(router.cfg, f"{Port.name_for(port)}_route_computer_cfg").position.y.eq(y)
                ]
            routers[x][y] = router

    def conn(m, a, b):
        readys = Signal(Config.N_VC)
        for vc in range(Config.N_VC):
            m.d.comb += [
                b[vc].valid.eq(a.valid & (a.p.vc == vc)),
                b[vc].p.eq(a.p.flit),
                readys[vc].eq(b[vc].valid & b[vc].ready)
            ]
        m.d.comb += a.ready.eq(readys.any())

    for x in range(grid_size):
        for y in range(grid_size):
            if x > 0:
                # for port_a, port_b in zip(routers[x][y].west_out, routers[x - 1][y].east_in):
                conn(m, routers[x][y].west_out, routers[x - 1][y].east_in)
            if x < (grid_size - 1):
                # for port_a, port_b in zip(routers[x][y].east_out, routers[x + 1][y].west_in):
                conn(m, routers[x][y].east_out, routers[x + 1][y].west_in)
            if y > 0:
                # for port_a, port_b in zip(routers[x][y].north_out, routers[x][y - 1].south_in):
                conn(m, routers[x][y].north_out, routers[x][y - 1].south_in)
            if y < (grid_size - 1):
                # for port_a, port_b in zip(routers[x][y].south_out, routers[x][y + 1].north_in):
                conn(m, routers[x][y].south_out, routers[x][y + 1].north_in)

    dut = m

    # comment in for more in depth checking (conflicting drivers)
    # convert(dut, ports=(routers[0][0].local_in.payload.as_value(),routers[0][0].local_in.valid,routers[0][0].local_in.ready))
    # print(convert(routers[0][0]))

    def write_packets(port, target, len):
        async def write_packet(ctx):
            await ctx.tick()
            await ctx.tick()
            await ctx.tick()
            with ctx.critical():
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
                await send_packet(ctx, port, target, len)
        return write_packet


    def verify_packets(coord, port):
        m.d.comb += port.ready.eq(1)
        with dut.If(port.ready & port.valid):
            m.d.sync += Print(Format("{} received flit {}", coord, port.payload))
        # async def verify(ctx):
        #     ctx.set(port.ready, 1)
        #     while True:
        #         flit, = await ctx.tick().sample(port.payload).until(port.ready & port.valid)
        #         print(coord, f"received flit {flit}")
        # return verify

    for x, r in enumerate(routers):
        for y, router in enumerate(r):
            for i, port in enumerate(router.local_out):
                verify_packets((x,y, i), port)
                # sim.add_process(verify_packets((x,y), port))


    sim = Simulator(dut)
    sim.add_clock(Period(MHz=100))
    sim.add_process(write_packets(routers[0][0].local_in[0], (0, 1, 0), 1))
    sim.add_process(write_packets(routers[0][0].local_in[1], (1, 1, 0), 1))
    # sim.add_process(write_packets(routers[0][0].west_in, (1, 0), 3))

    with sim.write_vcd("test.vcd"):
        sim.run_until(Period(MHz=100) * 1000)

def generate():
    import amaranth.back.verilog
    cls = MemoryMappedRouter
    name = ".".join([__spec__.name, cls.__qualname__])
    print(amaranth.back.verilog.convert(cls(), name=name))

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser("generate")
    subparsers.add_parser("sim")
    args = parser.parse_args()
    if args.action == "generate":
        generate()
    elif args.action == "sim":
        sim()
