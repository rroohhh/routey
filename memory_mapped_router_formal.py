#!/usr/bin/env python3

from amaranth import Module, Elaboratable, Assert, ClockDomain, Assume, Signal, Cover, Mux
from amaranth.lib import stream
from amaranth.lib.wiring import Component, In
from amaranth.asserts import AnyConst, Initial
from .utils import assertFormal
from .memory_mapped_router import MemoryMappedRouter, Port, Flit, FlitStream, Coordinate

def get_router_ports(router: MemoryMappedRouter):
    ports = []

    for (in_port, out_port) in list(router.port_pairs()):
        ports.append(in_port.ready)
        ports.append(in_port.valid)
        ports.append(in_port.p.as_value())
        ports.append(out_port.ready)

    return ports

# adds assumptions that a flit stream should satisfy
# ie, a start tag is never followed by a start or an start_and_end tag
class ValidFlitStream(Component):
    stream: In(FlitStream)

    def __init__(self, c=Assume):
        super().__init__()
        self._cell = c

    def elaborate(self, _):
        c = self._cell

        m = Module()
        stream = self.stream
        last_tag = Signal.like(stream.p.tag)
        last_data = Signal.like(stream.p)

        with m.FSM(name="stream"):
            with m.State("NO_DATA"):
                with m.If(stream.valid & ~stream.ready):
                    m.d.sync += last_data.eq(stream.p)
                    m.next = "HAVE_DATA"
            with m.State("HAVE_DATA"):
                m.d.comb += c(stream.p == last_data)
                with m.If(stream.valid & stream.ready):
                    m.next = "NO_DATA"

        with m.FSM(name="flit"):
            with m.State("IDLE"):
                with m.If(stream.valid & stream.ready):
                    m.d.comb += [
                        c(stream.p.is_head()),
                    ]
                    m.d.sync += last_tag.eq(stream.p.tag)
                    m.next = "HAVE_TAG"
            with m.State("HAVE_TAG"):
                with m.If(stream.valid & stream.ready):
                    m.d.sync += last_tag.eq(stream.p.tag)
                with m.If(stream.valid):
                    with m.If(last_tag.matches(Flit.start, Flit.payload)):
                        m.d.comb += c((stream.p.tag == Flit.tail) | (stream.p.tag == Flit.payload))
                    with m.If(last_tag.matches(Flit.start_and_end, Flit.tail)):
                        m.d.comb += c((stream.p.tag == Flit.start_and_end) | (stream.p.tag == Flit.start))

        return m


# test local_out can only produce packets that belong to us
def test_routing():
    class RoutingSpec(Elaboratable):
        """
        while receiving flits for arbitrary targets, only flits meant for ourselves are sent to local_out
        """
        def __init__(self, router):
            self.router   = router
            self.cd_sync = ClockDomain("sync")

        def elaborate(self, _):
            m = Module()

            m.domains += self.cd_sync

            m.submodules.dut = router = self.router

            for (name, in_port, _) in router.port_name_pairs():
                valid_stream = m.submodules[f"input_stream_{name}"] = ValidFlitStream(c=Assume)
                m.d.comb += [
                    valid_stream.stream.ready.eq(in_port.ready),
                    valid_stream.stream.valid.eq(in_port.valid),
                    valid_stream.stream.p.eq(in_port.p),
                ]


            our_x = AnyConst(len(router.cfg.route_computer_cfg.position.x))
            our_y = AnyConst(len(router.cfg.route_computer_cfg.position.y))
            # our_x = 1
            # our_y = 1

            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(our_x),
                router.cfg.route_computer_cfg.position.y.eq(our_y)
            ]

            with m.If(router.local_out.valid & router.local_out.ready & (router.local_out.p.tag.matches(Flit.start, Flit.start_and_end))):
                m.d.comb += [
                    Assert(router.local_out.p.data.start_and_end.target.x == our_x),
                    Assert(router.local_out.p.data.start_and_end.target.y == our_y)
                ]

            return m

    dut = MemoryMappedRouter()
    spec_contract = RoutingSpec(dut)
    assertFormal(spec_contract, [
        *get_router_ports(dut),
        spec_contract.cd_sync.clk, spec_contract.cd_sync.rst
    ], mode="prove", depth=20)

# checks valid flit type ordering
def test_valid_flit_stream_out():
    class ValidFlitStreamSpec(Elaboratable):
        """
        while receiving valid filt streams, this can only ever output valid flit streams
        """
        def __init__(self, router):
            self.router   = router
            self.cd_sync = ClockDomain("sync")

        def elaborate(self, _):
            m = Module()

            m.domains += self.cd_sync

            m.submodules.dut = router = self.router

            for (name, in_port, out_port) in router.port_name_pairs():
                input_stream = m.submodules[f"input_stream_{name}"] = ValidFlitStream(c=Assume)
                m.d.comb += [
                    input_stream.stream.ready.eq(in_port.ready),
                    input_stream.stream.valid.eq(in_port.valid),
                    input_stream.stream.p.eq(in_port.p),
                ]

                output_stream = m.submodules[f"output_stream_{name}"] = ValidFlitStream(c=Assert)
                m.d.comb += [
                    output_stream.stream.ready.eq(out_port.ready),
                    output_stream.stream.valid.eq(out_port.valid),
                    output_stream.stream.p.eq(out_port.p),
                ]

            our_x = AnyConst(len(router.cfg.route_computer_cfg.position.x))
            our_y = AnyConst(len(router.cfg.route_computer_cfg.position.y))
            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(our_x),
                router.cfg.route_computer_cfg.position.y.eq(our_y)
            ]

            return m

    dut = MemoryMappedRouter()
    spec_contract = ValidFlitStreamSpec(dut)
    assertFormal(spec_contract, [
        *get_router_ports(dut),
        spec_contract.cd_sync.clk, spec_contract.cd_sync.rst
    ], mode="prove", depth=20)

# checks if the streams obey the stream contract
# - valid must not depend on ready
# - valid is held until ready is asserted
# - payload is held until ready is asserted
def test_stream_contract_spec():
    class RouterStreamContractSpec(Elaboratable):
        def __init__(self, router):
            self.router   = router
            self.cd_sync = ClockDomain("sync")

        def elaborate(self, _):
            m = Module()
            m.domains += self.cd_sync
            m.submodules.dut = router = self.router

            our_x = AnyConst(len(router.cfg.route_computer_cfg.position.x))
            our_y = AnyConst(len(router.cfg.route_computer_cfg.position.y))

            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(our_x),
                router.cfg.route_computer_cfg.position.y.eq(our_y),
                Assume(our_x > 0),
                Assume(our_y > 0),
            ]

            for port in router.out_ports():
                m.d.comb += Assume(~port.ready),
                m.d.comb += Cover(port.valid)

            return m

    dut = MemoryMappedRouter()
    spec_contract = RouterStreamContractSpec(dut)
    assertFormal(spec_contract, [
        *get_router_ports(dut),
        spec_contract.cd_sync.clk, spec_contract.cd_sync.rst
    ], mode="cover", depth=20)


# this uses wolper coloring to check the data flow inside of packets
# - no dupe flits
# - no reordered flits
# - no dropped flits
def test_flit_data_flow():
    class FlitPayloadWolperColoring(Component):
        stream: In(FlitStream)

        def __init__(self, c=Assume, payload_bit_start_idx = -1, payload_bit_payload_idx = -1):
            super().__init__()
            self._cell = c
            self._payload_bit_start_idx = payload_bit_start_idx
            self._payload_bit_payload_idx = payload_bit_payload_idx

        def elaborate(self, _):
            c = self._cell

            m = Module()
            stream = self.stream

            payload_bit = Signal()
            payload_bit_start = Signal()
            payload_bit_payload = Signal()

            m.d.comb += payload_bit_start.eq(stream.p.data.start.payload.bit_select(self._payload_bit_start_idx, 1))
            m.d.comb += payload_bit_payload.eq(stream.p.data.payload.payload.bit_select(self._payload_bit_payload_idx, 1))

            m.d.comb += payload_bit.eq(Mux(stream.p.tag.matches(Flit.start), payload_bit_start, payload_bit_payload))


            def idle_if_end(alternative):
                with m.If(stream.p.tag.matches(Flit.tail)):
                    m.next = "IDLE"
                with m.Else():
                    m.next = alternative

            def check_payload():
                with m.If(payload_bit == 1):
                    idle_if_end("SEEN_ONE")
                with m.Else():
                    idle_if_end("SEEN_ZERO")

            with m.FSM():
                with m.State("IDLE"):
                    with m.If(stream.valid & stream.ready):
                        with m.If(stream.p.tag.matches(Flit.start)):
                            check_payload()
                with m.State("SEEN_ONE"):
                    with m.If(stream.valid & stream.ready):
                        m.d.comb += c(payload_bit == 1)
                        idle_if_end("ZEROS")
                with m.State("SEEN_ZERO"):
                    with m.If(stream.valid & stream.ready):
                        check_payload()
                with m.State("ZEROS"):
                    with m.If(stream.valid & stream.ready):
                        m.d.comb += c(payload_bit == 0)
                        idle_if_end("ZEROS")

            return m


    class FlitNoReorder(Elaboratable):
        """
        when receiving flits with consecutive payloads, the output payloads are also always consecutive
        """
        def __init__(self, router):
            self.router   = router
            self.cd_sync = ClockDomain("sync")

        def elaborate(self, _):
            m = Module()

            m.domains += self.cd_sync

            m.submodules.dut = router = self.router

            for (name, in_port, out_port) in router.port_name_pairs():
                # try to run through this again at some point?
                # checked_bit_start = AnyConst(range(len(p.p.data.start.payload)))
                # checked_bit_payload = AnyConst(range(len(p.p.data.payload.payload)))

                checked_bit_start = len(in_port.p.data.start.payload) - 1
                checked_bit_payload = len(in_port.p.data.payload.payload) - 1
                input_stream = m.submodules[f"input_stream_{name}"] = ValidFlitStream(c=Assume)
                input_payload = m.submodules[f"input_payload_{name}"] = FlitPayloadWolperColoring(Assume, checked_bit_start, checked_bit_payload)
                m.d.comb += [
                    input_stream.stream.ready.eq(in_port.ready),
                    input_stream.stream.valid.eq(in_port.valid),
                    input_stream.stream.p.eq(in_port.p),
                ]
                m.d.comb += [
                    input_payload.stream.ready.eq(in_port.ready),
                    input_payload.stream.valid.eq(in_port.valid),
                    input_payload.stream.p.eq(in_port.p),
                ]

                # output_stream = m.submodules[f"output_stream_{name}"] = ValidFlitStream(c=Assert)
                output_payload = m.submodules[f"output_payload_{name}"] = FlitPayloadWolperColoring(Assert, checked_bit_start, checked_bit_payload)
                # m.d.comb += [
                #     output_stream.stream.ready.eq(out_port.ready),
                #     output_stream.stream.valid.eq(out_port.valid),
                #     output_stream.stream.p.eq(out_port.p),
                # ]
                m.d.comb += [
                    output_payload.stream.ready.eq(out_port.ready),
                    output_payload.stream.valid.eq(out_port.valid),
                    output_payload.stream.p.eq(out_port.p),
                ]

            our_x = AnyConst(len(router.cfg.route_computer_cfg.position.x))
            our_y = AnyConst(len(router.cfg.route_computer_cfg.position.y))
            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(our_x),
                router.cfg.route_computer_cfg.position.y.eq(our_y)
            ]

            return m

    dut = MemoryMappedRouter()
    spec_contract = FlitNoReorder(dut)
    assertFormal(spec_contract, [
        *get_router_ports(dut),
        spec_contract.cd_sync.clk, spec_contract.cd_sync.rst
    ], mode="prove", depth=20)


# ordering rules:
# on the same input port: packets to the same target are send out to the same port and ordered the same as the input
#  - pick a source port, pick a target
#  - then use wolper coloring across packets to ensure ordering, no drops, etc?
#    - could also just make the payload of two consecutive packets something known and assert the same contents at the output
#    - need to make the input payload contain the input port, otherwise cannot distinguish between the packets received on different ports for different targets
def test_packet_data_flow():
    class PacketPayloadWolperColoring(Component):
        stream: In(FlitStream)

        def __init__(self, *, c=Assume, my_port, src_port, target):
            super().__init__()
            self._cell = c
            self._target = target
            self._my_port = my_port
            self._src_port = src_port

        def elaborate(self, _):
            c = self._cell

            m = Module()
            stream = self.stream

            payload_start_src_port = Signal.like(self._src_port)
            m.d.comb += payload_start_src_port.eq(stream.p.data.start.payload[0:len(payload_start_src_port)])

            payload_bit_idx = len(payload_start_src_port)
            payload_bit = Signal()
            m.d.comb += payload_bit.eq(Mux(stream.p.tag.matches(Flit.start), stream.p.data.start.payload[payload_bit_idx], stream.p.data.payload.payload[payload_bit_idx]))

            if c == Assume:
                with m.If(stream.valid & stream.ready & stream.p.tag.matches(Flit.start, Flit.start_and_end)):
                    m.d.comb += c(payload_start_src_port == self._my_port)
                    # m.d.comb += c(stream.p.tag.matches(Flit.start_and_end))


            color_matches = (stream.p.data.start.target == self._target) & (payload_start_src_port == self._src_port)
            new_packet_and_color_matches = stream.p.tag.matches(Flit.start, Flit.start_and_end) & color_matches

            if c == Assume:
                packet_len_counter = Signal(range(10))

                m.d.comb += Assume(packet_len_counter < 1)

                with m.If(stream.valid & stream.ready):
                    # with m.If(color_matches):
                        with m.If(stream.p.tag.matches(Flit.start)):
                            m.d.sync += packet_len_counter.eq(0)
                        with m.If(stream.p.tag.matches(Flit.payload, Flit.tail)):
                            m.d.sync += packet_len_counter.eq(packet_len_counter + 1)


            # FSM for the wolper coloring over packets, so this only transitions on packet starts to the target we are observing
            with m.If(stream.valid & stream.ready):
                with m.FSM():
                    with m.State("WAIT_FIRST_PACKET"):
                        # m.d.sync += Cover(payload_bit == 1)
                        with m.If(new_packet_and_color_matches & (payload_bit == 1)):
                            with m.If(stream.p.tag.matches(Flit.start_and_end)):
                                m.next = "WAIT_SECOND_ONE_PACKET"
                            with m.Else():
                                m.next = "READ_FIRST_ONE_PACKET"
                    with m.State("READ_FIRST_ONE_PACKET"):
                        m.d.comb += c(payload_bit == 1)
                        with m.If(stream.p.tag.matches(Flit.tail)):
                            m.next = "WAIT_SECOND_ONE_PACKET"
                    with m.State("WAIT_SECOND_ONE_PACKET"):
                        with m.If(new_packet_and_color_matches):
                            m.d.comb += c(payload_bit == 1)
                            with m.If(stream.p.tag.matches(Flit.start_and_end)):
                                m.next = "WAIT_ZEROS"
                            with m.Else():
                                m.next = "READ_SECOND_ONE_PACKET"
                    with m.State("READ_SECOND_ONE_PACKET"):
                        m.d.comb += c(payload_bit == 1)
                        with m.If(stream.p.tag.matches(Flit.tail)):
                            m.next = "WAIT_ZEROS"
                    with m.State("WAIT_ZEROS"):
                        with m.If(new_packet_and_color_matches):
                            m.d.comb += c(payload_bit == 0)
                            with m.If(stream.p.tag.matches(Flit.start_and_end)):
                                m.next = "WAIT_ZEROS"
                            with m.Else():
                                m.next = "READ_ZEROS"
                    with m.State("READ_ZEROS"):
                        m.d.comb += c(payload_bit == 0)
                        with m.If(stream.p.tag.matches(Flit.tail)):
                            m.next = "WAIT_ZEROS"


            return m


    class PacketDataflowSpec(Elaboratable):
        """
        when receiving flits with consecutive payloads, the output payloads are also always consecutive
        """
        def __init__(self, router):
            self.router   = router
            self.cd_sync = ClockDomain("sync")

        def elaborate(self, _):
            m = Module()

            m.domains += self.cd_sync

            m.submodules.dut = router = self.router


            # src_port = Port.Local
            src_port = AnyConst(Port)
            target_const = AnyConst(Coordinate)
            # target_x = 1
            # target_y = 0
            target = Signal(Coordinate)
            m.d.comb += target.eq(target_const)
            # m.d.comb += target.x.eq(target_const.x)
            # m.d.comb += target.y.eq(target_const.y)

            for (name, in_port, out_port) in router.port_name_pairs():
                my_port = getattr(Port, name.capitalize())
                input_stream = m.submodules[f"input_stream_{name}"] = ValidFlitStream(c=Assume)
                input_payload = m.submodules[f"input_payload_{name}"] = PacketPayloadWolperColoring(c=Assume, my_port=my_port , src_port=src_port, target=target)
                m.d.comb += [
                    input_stream.stream.ready.eq(in_port.ready),
                    input_stream.stream.valid.eq(in_port.valid),
                    input_stream.stream.p.eq(in_port.p),
                ]
                m.d.comb += [
                    input_payload.stream.ready.eq(in_port.ready),
                    input_payload.stream.valid.eq(in_port.valid),
                    input_payload.stream.p.eq(in_port.p),
                ]

                # output_stream = m.submodules[f"output_stream_{name}"] = ValidFlitStream(c=Assert)
                output_payload = m.submodules[f"output_payload_{name}"] = PacketPayloadWolperColoring(c=Assert, my_port=my_port, src_port=src_port, target=target)
                # m.d.comb += [
                #     output_stream.stream.ready.eq(out_port.ready),
                #     output_stream.stream.valid.eq(out_port.valid),
                #     output_stream.stream.p.eq(out_port.p),
                # ]
                m.d.comb += [
                    output_payload.stream.ready.eq(out_port.ready),
                    output_payload.stream.valid.eq(out_port.valid),
                    output_payload.stream.p.eq(out_port.p),
                ]

            our_x = 1
            our_y = 1
            # our_x = AnyConst(len(router.cfg.route_computer_cfg.position.x))
            # our_y = AnyConst(len(router.cfg.route_computer_cfg.position.y))
            m.d.comb += [
                router.cfg.route_computer_cfg.position.x.eq(our_x),
                router.cfg.route_computer_cfg.position.y.eq(our_y)
            ]

            return m

    dut = MemoryMappedRouter()
    spec_contract = PacketDataflowSpec(dut)
    assertFormal(spec_contract, [
        *get_router_ports(dut),
        spec_contract.cd_sync.clk, spec_contract.cd_sync.rst
    ], mode="prove", depth=12)


# do we want to prove some liveness guarantees?
# -> can we prove deadlock freeness?

if __name__ == "__main__":
    print("start", Flit.start.value)
    print("end", Flit.tail.value)
    print("payload", Flit.payload.value)
    print("start_and_end", Flit.start_and_end.value)

    test_routing()
    test_valid_flit_stream_out()
    test_stream_contract_spec()
    test_flit_data_flow()
    test_packet_data_flow()
