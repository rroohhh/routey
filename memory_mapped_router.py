#!/usr/bin/env python3

from collections import defaultdict
from typing_extensions import override

from tagged_union import *
from format_utils import *
from memory_mapped_router_types import CardinalPort
from amaranth import Signal, Mux, Print, Format, Value, Array
from amaranth.sim import Simulator, Period
from amaranth.lib import data, stream, enum, wiring
from amaranth.lib.fifo import SyncFIFO as SyncFIFOAmaranth
from amaranth.lib.wiring import Component, In, Out
from math import ceil

class StreamFIFO(Component):
    # w_stream: In(stream.Signature())
    # r_stream: Out(stream.Signature())

    def __init__(self, payload_shape: wiring.PureInterface | Shape, *, depth=2):
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


    def elaborate(self, plat):
        m = Module()
        if self.depth == 0:
            wiring.connect(m, wiring.flipped(self.r_stream), wiring.flipped(self.w_stream))
        else:
            fifo = m.submodules.fifo = SyncFIFOAmaranth(width=len(self.r_stream.p.as_value()), depth=self.depth)
            wiring.connect(m, wiring.flipped(self.r_stream), fifo.r_stream)
            wiring.connect(m, wiring.flipped(self.w_stream), fifo.w_stream)
        return m


# NUM_PER_SIDE = 2
# NUM_LOCAL = NUM_PER_SIDE


# flits should be ~large to avoid large overhead from UT
# we need to be able to send flits idependently, so they will get independently UT and ARQ handled
# ARQ has 1 byte overhead (for SEQ), UT has 1 byte overhead (for ix), so
# lets say flit size is 16 bytes

# want: 64 + 8 bits payload plus byteen

class Config:
    # for formal
    # LINK_BITS = 25
    # MUX_COUNT = 1
    # COORD_BITS = 4

    # minus three for id bits, minus 1 byte for seq minus 1 byte for crc
    FLIT_SIZE = 64 + 8 + 2
    MUX_COUNT = 4
    COORD_BITS = 7

    # calculate link bits from flit size
    # 3 bits tag
    # 8 bits sequence number
    # 8 bits checksum
    # MUX_COUNT * 2 bits for link id
    LINK_BITS = int(ceil((FLIT_SIZE + 3 + 8 + 8 + (MUX_COUNT * 2)) / (2 * MUX_COUNT)) * 2)

    INPUT_CHANNEL_FIFO_DEPTH = 2
    INPUT_CHANNEL_OUTPUT_FIFO_DEPTH = 0
    INPUT_CHANNEL_ROUTE_PIPELINE_DEPTH = INPUT_CHANNEL_FIFO_DEPTH
    CROSSBAR_OUTPUT_FIFO_DEPTH = 0

    N_VC = 2


VcID = range(Config.N_VC)
# class VcID(data.Struct):
#     id: range(Config.N_VC)

class Coordinate(data.Struct):
    x: Config.COORD_BITS
    y: Config.COORD_BITS

class RoutingTarget(data.Struct):
    vc: VcID
    target: Coordinate

class FlitStart(data.Struct):
    target: RoutingTarget
    payload: Config.FLIT_SIZE - RoutingTarget.as_shape().size

class FlitPayload(data.Struct):
    payload: Config.FLIT_SIZE

class FlitTail(data.Struct):
    payload: Config.FLIT_SIZE

class FlitStartAndEnd(FlitStart):
    ...
    # target: RoutingTarget
    # payload: Config.FLIT_SIZE - RoutingTarget.as_shape().size

# this should never enter the router, it is used for arq internal signaling
class FlitARQAck(data.Struct):
    payload: Config.FLIT_SIZE

# this should never enter the router, it is used for arq internal signaling
class FlitARQNack(data.Struct):
    payload: Config.FLIT_SIZE

class Flit(TaggedUnion):
    start: FlitStart
    tail: FlitTail
    payload: FlitPayload
    start_and_end: FlitStartAndEnd
    arq_ack: FlitARQAck
    arq_nack: FlitARQNack

    def is_last(self):
        return self.tag.matches(Flit.start_and_end, Flit.tail)

    def is_head(self):
        return self.tag.matches(Flit.start_and_end, Flit.start)

Config.ENCODED_FLIT_SIZE = data.Layout.cast(Flit).size

FlitStream = stream.Signature(Flit)

RouteComputerConfig = wiring.Signature({
    "position": Out(Coordinate)
})

class Port(data.Struct):
    port: CardinalPort
    vc_id: VcID

    @classmethod
    def __members__(cls) -> dict:
        return {
            f"{name}_vc_{vc}" : cls.const({"port": dir, "vc_id": vc})
            for name, dir in CardinalPort.__members__.items()
            for vc in VcID
        }

    # @override
    # def __getitem__(self, key):
    #     return Port.__members__()[key]

class RouteResult(data.Struct):
    new_target: RoutingTarget
    port: CardinalPort


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
    input: In(stream.Signature(RoutingTarget))
    result: Out(stream.Signature(RouteResult))
    cfg: In(RouteComputerConfig)

    def elaborate(self, _):
        m = Module()

        m.d.comb += self.input.ready.eq(self.result.ready)
        m.d.comb += self.result.valid.eq(self.input.valid)

        input_x = self.input.payload.target.x
        input_y = self.input.payload.target.y
        my_x = self.cfg.position.x
        my_y = self.cfg.position.y
        res = self.result.payload

        m.d.comb += res.new_target.eq(self.input.payload)

        with m.If(input_x != my_x):
            m.d.comb += res.port.eq(Mux(input_x > my_x, CardinalPort.east, CardinalPort.west))
        with m.Elif(input_y != my_y):
            m.d.comb += res.port.eq(Mux(input_y > my_y, CardinalPort.south, CardinalPort.north))
        with m.Else():
            m.d.comb += res.port.eq(CardinalPort.local)

        return m


COUNTER_SIZE = 32

class RoutedFlit(data.Struct):
    flit: Flit
    last: 1
    target: Port

InputChannelConfig = wiring.Signature({
    "invalid_flit_ctr": In(COUNTER_SIZE)
})

# assumes clean input
# TODO(robin): input cleaner
class InputChannel(Component):
    flit_in: In(FlitStream)
    flit_out: Out(stream.Signature(RoutedFlit))
    cfg: In(InputChannelConfig)
    route_computer_cfg: In(RouteComputerConfig)

    def __init__(self, name):
        super().__init__()
        # super().__init__(path=(name + "_input_channel",))
        self._name = name


    # what values for result.p are possible given that I am the InputChannel for port `position`?
    # def outputs_reachable(self, position: Port) -> set[Port]:
    #     from crossbar_opt import outputs_reachable_by
    #     return outputs_reachable_by(position, RouteComputer)

    def _print(self, string, *args):
        args = f"{{}}, {{}}: {self.__class__.__name__}/{self._name}: {string}", self.route_computer_cfg.position.x, self.route_computer_cfg.position.y, *args
        return Print(Format(*args))

    def elaborate(self, _):
        m = Module()
        route_computer = m.submodules.route_computer = RouteComputer()
        wiring.connect(m, wiring.flipped(self.route_computer_cfg), route_computer.cfg)

        flit_out = self.flit_out
        flit_in_before_fifo = self.flit_in
        input_fifo = m.submodules.input_fifo = StreamFIFO(self.flit_in, depth=Config.INPUT_CHANNEL_FIFO_DEPTH)

        # we do not need to wait for the route computer if the next flit wont have routing information
        # this is the case if the previous flit was the last flit of a so, packet the next one will have to have routing info
        next_flit_has_routing = Signal(reset=1)
        with m.If(flit_in_before_fifo.valid & flit_in_before_fifo.ready):
            m.d.sync += next_flit_has_routing.eq(flit_in_before_fifo.p.is_last())

        route_computer_stall = Signal()
        input_stall = route_computer_stall

        m.d.comb += [
            flit_in_before_fifo.ready.eq(input_fifo.w_stream.ready & ~input_stall),
            input_fifo.w_stream.valid.eq(flit_in_before_fifo.valid & ~input_stall),
            input_fifo.w_stream.p.eq(flit_in_before_fifo.p)
        ]

        # start and start_and_end have the same layout, so this is always valid
        m.d.comb += route_computer.input.payload.eq(flit_in_before_fifo.payload.data.start.target)

        with m.FSM(name="route_computer_fsm"):
            with m.State("idle"):
                with m.If(next_flit_has_routing):
                    m.d.comb += [
                        route_computer.input.valid.eq(flit_in_before_fifo.valid),
                        route_computer_stall.eq(~route_computer.input.ready)
                    ]
                    # if we fed this into the route computer, but we did not feed it into the fifo yet, we cannot longer assert
                    # valid, as otherwise we read the same flit multiple times
                    with m.If(route_computer.input.ready & ~input_fifo.w_stream.ready):
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

        # finally combine the buffered flits with the routing result
        m.d.comb += [
            flit_in.ready.eq(flit_out.ready & flit_out.valid),
            # rewrite old target with the new target obtained from the route computer
            flit_out.p.flit.data.start.target.eq(Mux(flit_in.p.is_head(), route_result.p.new_target, flit_in.payload.data.start.target)),
            flit_out.p.flit.data.start.payload.eq(flit_in.payload.data.start.payload),
            flit_out.p.target.port.eq(route_result.p.port),
            flit_out.p.target.vc_id.eq(route_result.p.new_target.vc),
            flit_out.p.last.eq(flit_out.p.flit.is_last()),
            flit_out.valid.eq(flit_in.valid & route_result.valid),
            route_result.ready.eq(flit_out.ready & flit_out.valid & flit_out.p.flit.is_last())
        ]

        return m

# when asserting grant, this gives out a index on the next cycle
class RoundRobinArbiter(Component):
    def __init__(self, num_clients):
        super().__init__({
            "requests": In(num_clients),
            "next": In(1),
            "grant_store": Out(range(num_clients)),
            "grant": Out(range(num_clients)),
        })

    def elaborate(self, _):
        m = Module()

        with m.Switch(self.grant_store):
            for i in range(len(self.requests)):
                with m.Case(i):
                    with m.If(self.requests[i]):
                        m.d.comb += self.grant.eq(i)

                    for pred in reversed(range(i)):
                        with m.If(self.requests[pred]):
                            m.d.comb += self.grant.eq(pred)
                    for succ in reversed(range(i + 1, len(self.requests))):
                        with m.If(self.requests[succ]):
                            m.d.comb += self.grant.eq(succ)

        with m.If(self.next):
            m.d.sync += self.grant_store.eq(self.grant)

        return m

# think about making this more async, by having a target and a data stream, like axi does
# -> we can look at the upcoming inputs, do we gain anything by that?
class PacketizedStreamCrossbarOutput(Component):
    output: Out(FlitStream)

    def __init__(self, inputs, target: Port):
        super().__init__()
        self._inputs = inputs
        self._target = target
        self.input_ready = Signal(len(inputs))

    def elaborate(self, _):
        m = Module()
        inputs = self._inputs
        target = self._target

        arbiter = m.submodules.arbiter = RoundRobinArbiter(len(inputs))

        # this is used to mask out the input stream that is currently transferred
        # because this is a round robin arbiter, we should not really select the same input stream twice back to back anyways
        mask = Signal.like(arbiter.requests)
        for i, input in enumerate(inputs):
            m.d.comb += arbiter.requests[i].eq(input.valid & (input.payload.target == target) & ~mask[i])

        target = Signal.like(arbiter.grant)
        transfer = Signal()
        selected = Array(self._inputs)[target]

        with m.If(transfer):
            m.d.comb += [
                self.output.valid.eq(selected.valid),
                self.output.p.eq(selected.p.flit),
                self.input_ready.bit_select(target, 1).eq(self.output.ready)
            ]

        with m.FSM():
            with m.State("IDLE"):
                with m.If(arbiter.requests != 0):
                    m.d.comb += [
                        arbiter.next.eq(1),
                        target.eq(arbiter.grant),
                        transfer.eq(1)
                    ]
                    with m.If(self.output.valid & self.output.ready & selected.p.last):
                        m.next = "IDLE"
                    with m.Else():
                        m.next = "TRANSFER"
            with m.State("TRANSFER"):
                    m.d.comb += [
                        target.eq(arbiter.grant_store),
                        transfer.eq(1)
                    ]
                    with m.If(self.output.valid & self.output.ready):
                        with m.If(selected.p.last):
                            m.next = "IDLE"
                        with m.Else():
                            m.next = "TRANSFER"

        return m

class PacketizedStreamCrossbar(Component):
    def __init__(self, outputs: dict[enum.Enum, stream.Signature]):
        self.outputs = outputs
        self._inputs = []

    def add_input(self, input_stream: stream.Signature, reachable: set(enum.Enum)):
        self._inputs.append((input_stream, reachable))

    def elaborate(self, _):
        m = Module()
        inputs = self._inputs

        input_readys = defaultdict(list)

        for target, output_stream in self.outputs.items():
            inputs_for_output, input_idx = list(zip(*(
                (input, i) for i, (input, targets) in enumerate(inputs) if target in targets
            )))
            output = m.submodules[f"crossbar_output_{target.name.lower()}"] = PacketizedStreamCrossbarOutput(inputs_for_output, target)
            wiring.connect(m, output.output, wiring.flipped(output_stream))

            for i, (input, idx) in enumerate(zip(inputs_for_output, input_idx)):
                input_readys[input].append(output.input_ready[i])

        for i, (input, _) in enumerate(inputs):
            m.d.comb += input.ready.eq(sum(input_readys[input])[0])

        return m


MemoryMappedRouterConfig = wiring.Signature({
    "route_computer_cfg": In(RouteComputerConfig),
    **{f"{port.lower()}_cfg": In(InputChannelConfig) for port in Port.__members__().keys()}
})

# requirments for this router:
# - never drop a packet, only ever send a packet when there is space, only ever read a packet when it will not be dropped
# - process packets in order, the packets from any port have to be processed in order
class MemoryMappedRouter(Component):
    local_in: In(FlitStream).array(Config.N_VC)
    local_out: Out(FlitStream).array(Config.N_VC)

    north_in: In(FlitStream).array(Config.N_VC)
    north_out: Out(FlitStream).array(Config.N_VC)
    south_in: In(FlitStream).array(Config.N_VC)
    south_out: Out(FlitStream).array(Config.N_VC)
    east_in: In(FlitStream).array(Config.N_VC)
    east_out: Out(FlitStream).array(Config.N_VC)
    west_in: In(FlitStream).array(Config.N_VC)
    west_out: Out(FlitStream).array(Config.N_VC)

    cfg: In(MemoryMappedRouterConfig)

    def in_port(self, port: Port):
        return getattr(self, f"{port.port.name.lower()}_in")[port.vc_id]

    def out_port(self, port: Port):
        return getattr(self, f"{port.port.name.lower()}_out")[port.vc_id]

    # def in_ports(self):
    #     for port in Port.__members__.values():
    #         yield self.in_port(port)

    # def out_ports(self):
    #     for port in Port.__members__.values():
    #         yield self.out_port(port)

    # def port_pairs(self):
    #     for port in Port.__members__.values():
    #         yield (self.in_port(port), self.out_port(port))

    def port_name_pairs(self):
        for port_name, port in Port.__members__.items():
            yield (port_name, self.in_port(port), self.out_port(port))

    # def port_name_direction_pairs(self):
    #     for port in Port.__members__.values():
    #         yield (port.name.lower(), self.in_port(port), self.out_port(port), port)

    def elaborate(self, _):
        m = Module()

        output_ports = {}
        for name, _, out_port in self.port_name_pairs():
            crossbar_out = FlitStream.create(path=[f"{name}_flit_out_buffered"])
            output_ports[Port[name]] = crossbar_out

            buffer = m.submodules[f"{name}_crossbar_output_fifo"] = SyncFIFO(width=len(crossbar_out.p.as_value()), depth=Config.CROSSBAR_OUTPUT_FIFO_DEPTH)
            wiring.connect(m, crossbar_out, buffer.w_stream)
            wiring.connect(m, buffer.r_stream, wiring.flipped(out_port))

        crossbar = m.submodules.crossbar = PacketizedStreamCrossbar(output_ports)

        # each input port gets a buffer, that stores the current flit we process and a route compute unit, that if a head flit is encountered figures out, where the packet is supposed to go
        for (name, in_port, _, position) in self.port_name_direction_pairs():
            channel = m.submodules[f"{name}_input_channel"] = InputChannel(name)
            wiring.connect(m, wiring.flipped(channel.route_computer_cfg), wiring.flipped(self.cfg.route_computer_cfg))
            wiring.connect(m, wiring.flipped(channel.cfg), wiring.flipped(getattr(self.cfg, f"{name}_cfg")))
            wiring.connect(m, channel.flit_in, wiring.flipped(in_port))

            buffer = m.submodules[f"{name}_input_channel_output_fifo"] = SyncFIFO(width=len(channel.flit_out.p.as_value()), depth=Config.INPUT_CHANNEL_OUTPUT_FIFO_DEPTH)
            flit_out = stream.Signature(RoutedFlit).create(path=[f"{name}_flit_out_buffered"])

            wiring.connect(m, wiring.flipped(channel.flit_out), buffer.w_stream)
            wiring.connect(m, buffer.r_stream, wiring.flipped(flit_out))
            crossbar.add_input(flit_out, channel.outputs_reachable(position))

        Value.cast(self.local_in.payload).attrs["debug_item"] = 1
        self.local_in.ready.attrs["debug_item"] = 1
        self.local_in.valid.attrs["debug_item"] = 1
        Value.cast(self.local_out.payload).attrs["debug_item"] = 1
        self.local_out.ready.attrs["debug_item"] = 1
        self.local_out.valid.attrs["debug_item"] = 1

        return add_formatting_attrs(m)

async def send_packet(ctx, port, target, n_payload):
    tags = [Flit.start_and_end]
    if n_payload > 1:
        tags = [Flit.start] + [Flit.payload] * (n_payload - 2) + [Flit.tail]

    ctx.set(port.valid, 1)
    for i, tag in enumerate(tags):
        ctx.set(port.payload.tag, tag)
        if i == 0:
            ctx.set(port.payload.data.start_and_end.payload, i)
            ctx.set(port.payload.data.start_and_end.target.x, target[0])
            ctx.set(port.payload.data.start_and_end.target.y, target[1])
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
            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(x),
                router.cfg.route_computer_cfg.position.y.eq(y)
            ]
            routers[x][y] = router

    for x in range(grid_size):
        for y in range(grid_size):
            if x > 0:
                wiring.connect(m, routers[x][y].west_out, routers[x - 1][y].east_in)
            if x < (grid_size - 1):
                wiring.connect(m, routers[x][y].east_out, routers[x + 1][y].west_in)
            if y > 0:
                wiring.connect(m, routers[x][y].north_out, routers[x][y - 1].south_in)
            if y < (grid_size - 1):
                wiring.connect(m, routers[x][y].south_out, routers[x][y + 1].north_in)

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


    def verify_packets(coord, router):
        async def verify(ctx):
            ctx.set(router.local_out.ready, 1)
            # ctx.set(router.west_out.ready, 0)
            # ctx.set(router.east_out.ready, 0)
            # ctx.set(router.north_out.ready, 0)
            # ctx.set(router.south_out.ready, 0)
            while True:
                flit, = await ctx.tick().sample(router.local_out.payload).until(router.local_out.ready & router.local_out.valid)
                print(coord, f"received flit {flit}")
        return verify


    sim = Simulator(dut)
    sim.add_clock(Period(MHz=100))
    sim.add_process(write_packets(routers[0][0].local_in, (1, 0), 10))
    # sim.add_process(write_packets(routers[0][0].west_in, (1, 0), 3))

    for x, r in enumerate(routers):
        for y, router in enumerate(r):
            sim.add_process(verify_packets((x,y), router))

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
