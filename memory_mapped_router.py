#!/usr/bin/env python3

from .tagged_union import *
from amaranth import Signal, Mux, Print, Format
from amaranth.hdl._ast import SwitchValue
from amaranth.sim import Simulator, Period
from amaranth.lib import data, stream, enum, wiring
from amaranth.lib.fifo import SyncFIFOBuffered
from amaranth.lib.wiring import Component, In, Out

# NUM_PER_SIDE = 2
# NUM_LOCAL = NUM_PER_SIDE


# flits should be ~large to avoid large overhead from UT
# we need to be able to send flits idependently, so they will get independently UT and ARQ handled
# ARQ has 1 byte overhead (for SEQ), UT has 1 byte overhead (for ix), so
# lets say flit size is 16 bytes


class Config:
    FLIT_SIZE = 16 * 4
    COORD_BITS = 8
    INPUT_CHANNEL_FIFO_DEPTH = 2

class Coordinate(data.Struct):
    x_coord: Config.COORD_BITS
    y_coord: Config.COORD_BITS


class FlitStart(data.Struct):
    target: Coordinate
    payload: Config.FLIT_SIZE - Coordinate.as_shape().size

class FlitPayload(data.Struct):
    payload: Config.FLIT_SIZE

class FlitTail(data.Struct):
    payload: Config.FLIT_SIZE

class FlitStartAndEnd(data.Struct):
    target: Coordinate
    payload: Config.FLIT_SIZE - Coordinate.as_shape().size

class Flit(TaggedUnion):
    start: FlitStart
    tail: FlitTail
    payload: FlitPayload
    start_and_end: FlitStartAndEnd

    @staticmethod
    def print(flit):
        tag = flit.shape()["tag"].shape(flit.tag)
        body = f"payload={flit.data.payload.payload}"
        if tag in [Flit.start, Flit.start_and_end]:
            f = flit.data.start_and_end
            body = f"x={f.target.x_coord}, y={f.target.y_coord}, payload={f.payload}"

        return f"Flit.{tag.name}({body})"

    @staticmethod
    def runtime_print(flit):
        return SwitchValue(flit.tag, [
            (Flit.start, flit.data.start),
            (Flit.tail, flit.data.tail),
            (Flit.payload, flit.data.payload),
            (Flit.start_and_end, flit.data.start_and_end),
        ])

Config.ENCODED_FLIT_SIZE = data.Layout.cast(Flit).size

FlitStream = stream.Signature(Flit)

class Port(enum.Enum):
    Local = 0
    North = enum.auto()
    South = enum.auto()
    East = enum.auto()
    West = enum.auto()


RouteComputerConfig = wiring.Signature({
    "position": In(Coordinate)
})

# responsible for calculating which port to send this packet
# for now just takes a coordinate and outputs a target port
#
# This implements deterministic distributed routing in form of XY routing
# By using a deterministic routing algorithm, we ensure the ordering of packets
# However this does not use for example congestion info to route around congested paths
#
# This samples the config whenever a new coordinate is fed in
class RouteComputer(Component):
    input: In(stream.Signature(Coordinate))
    result: Out(stream.Signature(Port))
    cfg: In(RouteComputerConfig)

    def elaborate(self, _):
        m = Module()

        m.d.comb += self.input.ready.eq(self.result.ready)
        m.d.comb += self.result.valid.eq(self.input.valid)

        input_x_coord = self.input.payload.x_coord
        input_y_coord = self.input.payload.y_coord
        my_x_coord = self.cfg.position.x_coord
        my_y_coord = self.cfg.position.y_coord
        res = self.result.payload

        with m.If(input_x_coord != my_x_coord):
            m.d.comb += res.eq(Mux(input_x_coord > my_x_coord, Port.East, Port.West))
        with m.Elif(input_y_coord != my_y_coord):
            m.d.comb += res.eq(Mux(input_y_coord > my_y_coord, Port.South, Port.North))
        with m.Else():
            m.d.comb += res.eq(Port.Local)

        return m


COUNTER_SIZE = 32

class RoutedFlit(data.Struct):
    last: 1
    target: Port
    flit: Flit

InputChannelConfig = wiring.Signature({
    "invalid_flit_ctr": Out(COUNTER_SIZE)
})

class InputChannel(Component):
    flit_in: In(FlitStream)
    flit_out: In(stream.Signature(RoutedFlit))
    cfg: In(InputChannelConfig)
    route_computer_cfg: In(RouteComputerConfig)

    def __init__(self, name):
        super().__init__()
        # super().__init__(path=(name + "_input_channel",))
        self._name = name

    def _print(self, string, *args):
        args = f"{{}}, {{}}: {self.__class__.__name__}/{self._name}: {string}", self.route_computer_cfg.position.x_coord, self.route_computer_cfg.position.y_coord, *args
        return Print(Format(*args))

    def elaborate(self, _):
        m = Module()
        route_computer = m.submodules.route_computer = RouteComputer()
        wiring.connect(m, self.route_computer_cfg, wiring.flipped(route_computer.cfg))

        flit_out = self.flit_out

        # flit_in = self.flit_in
        flit_in_before_fifo = self.flit_in
        input_fifo = m.submodules.input_fifo = SyncFIFOBuffered(width=len(self.flit_in.payload.as_value()), depth=Config.INPUT_CHANNEL_FIFO_DEPTH)
        wiring.connect(m, wiring.flipped(flit_in_before_fifo), input_fifo.w_stream)
        flit_in = FlitStream.create(path=["flit_in_buffered"])
        wiring.connect(m, input_fifo.r_stream, wiring.flipped(flit_in))


        cfg = self.cfg

        # start and start_and_end have the same layout, so this is always valid
        m.d.comb += route_computer.input.payload.eq(flit_in.payload.data.start.target)

        target_port = Signal(Port)

        m.d.comb += [
            flit_out.payload.flit.eq(flit_in.payload),
            flit_out.payload.target.eq(target_port),
        ]

        m.d.comb += route_computer.result.ready.eq(1)
        with m.If(route_computer.result.ready & route_computer.result.valid):
            m.d.sync += target_port.eq(route_computer.result.payload)


        # TODO(robin): runs into cxxrtl bug
        # with m.If(flit_in.valid & flit_in.ready):
        #     m.d.sync += self._print("read flit {}", flit_in.payload.data.start)

        with m.FSM():
            # TODO(robin): consider inserting a pipeline / buffer stage that takes in some flit_in
            with m.State("IDLE"):
                with m.If(flit_in.valid): # this should always be a start or start_and_end flit
                    # m.d.comb += Assert(flit_in.payload.tag.matches(Flit.start, Flit.start_and_end))

                    with m.If(flit_in.payload.tag.matches(Flit.start, Flit.start_and_end)):
                        m.d.comb += route_computer.input.valid.eq(1)
                    with m.Else(): # drop this flit, we have no way to route it, as we never received a corresponding start flit
                        m.d.sync += cfg.invalid_flit_ctr.eq(cfg.invalid_flit_ctr + 1)
                        m.d.comb += flit_in.ready.eq(1)

                    # shortcut for combinatorial route computer
                    with m.If(route_computer.result.ready & route_computer.result.valid):
                        m.next = "ALLOCATED"
                    with m.Else():
                        m.next = "WAITING_FOR_ROUTE"
            with m.State("WAITING_FOR_ROUTE"):
                m.d.comb += route_computer.input.valid.eq(1)
                with m.If(route_computer.result.ready & route_computer.result.valid):
                    m.next = "ALLOCATED"
            with m.State("ALLOCATED"):
                m.d.comb += [
                    flit_in.ready.eq(flit_out.ready),
                    flit_out.valid.eq(flit_in.valid)
                ]

                with m.If(flit_out.valid & flit_out.payload.flit.tag.matches(Flit.start_and_end, Flit.tail)):
                    m.d.comb += flit_out.payload.last.eq(1)
                    with m.If(flit_out.ready):
                        m.next = "IDLE"

        return m

# when asserting grant, this gives out a index on the next cycle
class RoundRobinArbiter(Component):
    def __init__(self, num_clients):
        super().__init__({
            "requests": In(num_clients),
            "next": In(1),
            "grant": Out(range(num_clients)),
        })

    def elaborate(self, _):
        m = Module()

        with m.If(self.next):
            with m.Switch(self.grant):
                for i in range(len(self.requests)):
                    with m.Case(i):
                        for pred in reversed(range(i)):
                            with m.If(self.requests[pred]):
                                m.d.sync += self.grant.eq(pred)
                        for succ in reversed(range(i + 1, len(self.requests))):
                            with m.If(self.requests[succ]):
                                m.d.sync += self.grant.eq(succ)

        return m
# think about making this more async, by having a target and a data stream, like axi does
# -> we can look at the upcoming inputs, do we gain anything by that?
class PacketizedStreamCrossbarOutput(Component):
    output: Out(FlitStream)

    def __init__(self, inputs, target):
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

        def arbitrate_and_transfer():
            with m.If(arbiter.requests != 0):
                m.d.comb += arbiter.next.eq(1)
                m.next = "TRANSFER"

        for i, input in enumerate(inputs):
            m.d.comb += arbiter.requests[i].eq(input.valid & (input.payload.target == target) & ~mask[i])

        with m.FSM():
            with m.State("IDLE"):
                arbitrate_and_transfer()

            with m.State("TRANSFER"):
                m.d.comb += mask.eq(1 << arbiter.grant)

                for i, input in enumerate(inputs):
                    with m.If(i == arbiter.grant):
                        m.d.comb += [
                            self.input_ready[i].eq(self.output.ready),
                            self.output.valid.eq(input.valid),
                            self.output.p.eq(input.p.flit),
                        ]

                        with m.If(input.valid & input.ready & input.payload.last):
                            arbitrate_and_transfer()
                            with m.Else():
                                m.next = "IDLE"

        return m

class PacketizedStreamCrossbar(Component):
    def __init__(self, outputs: dict[enum.Enum, stream.Signature]):
        self.outputs = outputs
        self._inputs = []

    def add_input(self, input_stream: stream.Signature):
        self._inputs.append(input_stream)

    def elaborate(self, _):
        m = Module()
        inputs = self._inputs

        input_readys = []

        for target, output_stream in self.outputs.items():
            output = m.submodules[f"crossbar_output_{target.name.lower()}"] = PacketizedStreamCrossbarOutput(inputs, target)
            wiring.connect(m, output.output, wiring.flipped(output_stream))
            input_readys.append(output.input_ready)

        for i, input in enumerate(inputs):
            m.d.comb += input.ready.eq(sum(input_ready[i] for input_ready in input_readys)[0])

        return m


MemoryMappedRouterConfig = wiring.Signature({
    "route_computer_cfg": In(RouteComputerConfig),
    **{f"{port.name.lower()}_cfg": In(InputChannelConfig) for port in Port.__members__.values()}
})

# requirments for this router:
# - never drop a packet, only ever send a packet when there is space, only ever read a packet when it will not be dropped
# - process packets in order, the packets from any port have to be processed in order
class MemoryMappedRouter(Component):
    local_in: In(FlitStream)
    local_out: Out(FlitStream)

    north_in: In(FlitStream)
    north_out: Out(FlitStream)
    south_in: In(FlitStream)
    south_out: Out(FlitStream)
    east_in: In(FlitStream)
    east_out: Out(FlitStream)
    west_in: In(FlitStream)
    west_out: Out(FlitStream)

    cfg: In(MemoryMappedRouterConfig)

    def in_port(self, port: Port):
        return getattr(self, f"{port.name.lower()}_in")

    def out_port(self, port: Port):
        return getattr(self, f"{port.name.lower()}_out")

    def in_ports(self):
        for port in Port.__members__.values():
            yield self.in_port(port)

    def out_ports(self):
        for port in Port.__members__.values():
            yield self.out_port(port)

    def port_pairs(self):
        for port in Port.__members__.values():
            yield (self.in_port(port), self.out_port(port))

    def port_name_pairs(self):
        for port in Port.__members__.values():
            yield (port.name.lower(), self.in_port(port), self.out_port(port))

    def elaborate(self, _):
        m = Module()

        output_ports = {
            port: self.out_port(port) for port in Port.__members__.values()
        }
        crossbar = m.submodules.crossbar = PacketizedStreamCrossbar(output_ports)

        # each input port gets a buffer, that stores the current flit we process and a route compute unit, that if a head flit is encountered figures out, where the packet is supposed to go
        for (name, in_port, _) in self.port_name_pairs():
            channel = m.submodules[f"{name}_input_channel"] = InputChannel(name)
            wiring.connect(m, wiring.flipped(channel.route_computer_cfg), wiring.flipped(self.cfg.route_computer_cfg))
            wiring.connect(m, wiring.flipped(channel.cfg), wiring.flipped(getattr(self.cfg, f"{name}_cfg")))
            wiring.connect(m, channel.flit_in, wiring.flipped(in_port))
            crossbar.add_input(channel.flit_out)

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
            ctx.set(port.payload.data.start_and_end.target.x_coord, target[0])
            ctx.set(port.payload.data.start_and_end.target.y_coord, target[1])
        else:
            ctx.set(port.payload.data.payload.payload, i)
        await ctx.tick().until(port.ready & port.valid)
    ctx.set(port.valid, 0)


if __name__ == "__main__":
    grid_size = 2
    n_packets = 10

    m = Module()

    routers = [[MemoryMappedRouter() for _ in range(grid_size)] for _ in range(grid_size)]
    for x in range(grid_size):
        for y in range(grid_size):
            router = m.submodules[f"router_{x}_{y}"] = routers[x][y]
            m.d.comb += [
                router.cfg.route_computer_cfg.position.x_coord.eq(x),
                router.cfg.route_computer_cfg.position.y_coord.eq(y)
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
            with ctx.critical():
                await send_packet(ctx, port, target, len)
        return write_packet


    def verify_packets(coord, router):
        async def verify(ctx):
            # ctx.set(router.local_out.ready, 0)
            # ctx.set(router.west_out.ready, 0)
            # ctx.set(router.east_out.ready, 0)
            # ctx.set(router.north_out.ready, 0)
            # ctx.set(router.south_out.ready, 0)
            while True:
                flit, = await ctx.tick().sample(router.local_out.payload).until(router.local_out.ready & router.local_out.valid)
                print(coord, f"received flit {Flit.print(flit)}")
        return verify


    sim = Simulator(dut)
    sim.add_clock(Period(MHz=100))
    sim.add_process(write_packets(routers[0][0].local_in, (0, 0), 3))
    sim.add_process(write_packets(routers[0][0].west_in, (1, 0), 3))

    for x, r in enumerate(routers):
        for y, router in enumerate(r):
            sim.add_process(verify_packets((x,y), router))

    with sim.write_vcd("test.vcd"):
        sim.run_until(Period(MHz=100) * 100)
