#!/usr/bin/env python3

from amaranth import Module, Signal, ClockDomain, Assume, Shape, Assert
from amaranth.asserts import AnyConst
from memory_mapped_router import RouteComputer, Coordinate
from memory_mapped_router_types import Port
from utils import FormalVerificationFailed, assertFormal
from functools import lru_cache

@lru_cache
def outputs_reachable_by(input_channel_position: Port, route_computer_gen):
    def max_value(thing):
        if not isinstance(thing, Shape):
            thing = thing.shape()
        thing = Shape.cast(thing)
        assert not thing.signed
        return (1 << thing.width) - 1

    # this build a "chain" of two route computers
    # we take an arbitrary packet and a arbitrary sender position
    # and assume the sender routes it to the sender output port
    # the we assume the proper position for the receiver
    # (ie if the sender (sx, sy) sends to north, the receiver has position (sx, sy - 1))
    # and assert that the desired receiver output port *cannot* be reached
    # So if this check fails, the port can be reached, if it succeeds the port cannot be reached
    def build(sender_output_port: Port, receiver_output_port: Port):
        m = Module()

        cd_sync = ClockDomain("sync")
        m.domains += cd_sync

        m.submodules.sender = sender = route_computer_gen()
        m.submodules.receiver = receiver = route_computer_gen()

        packet_target = AnyConst(Coordinate)

        sender_coord = AnyConst(Coordinate)
        receiver_coord = Signal(Coordinate)

        m.d.comb += sender.cfg.position.eq(sender_coord)
        m.d.comb += receiver.cfg.position.eq(receiver_coord)

        m.d.comb += [
            sender.input.p.eq(packet_target),
            sender.input.valid.eq(1),
            sender.result.ready.eq(1),

            receiver.input.p.eq(packet_target),
            receiver.input.valid.eq(1),
            receiver.result.ready.eq(1),
        ]

        if sender_output_port != Port.local:
            with m.If(sender.result.valid & sender.result.ready):
                m.d.comb += Assume(sender.result.p == sender_output_port)

        sender_pos = sender.cfg.position
        receiver_pos = receiver.cfg.position

        match sender_output_port:
            case Port.north:
                m.d.comb += Assume(sender_pos.y > 0)
                m.d.comb += [
                    receiver_pos.x.eq(sender_pos.x),
                    receiver_pos.y.eq(sender_pos.y - 1),
                ]
            case Port.south:
                m.d.comb += Assume(sender_pos.y < max_value(sender_pos.y))
                m.d.comb += [
                    receiver_pos.x.eq(sender_pos.x),
                    receiver_pos.y.eq(sender_pos.y + 1),
                ]
            case Port.east:
                m.d.comb += Assume(sender_pos.x < max_value(sender_pos.x))
                m.d.comb += [
                    receiver_pos.x.eq(sender_pos.x + 1),
                    receiver_pos.y.eq(sender_pos.y),
                ]
            case Port.west:
                m.d.comb += Assume(sender_pos.x > 0)
                m.d.comb += [
                    receiver_pos.x.eq(sender_pos.x - 1),
                    receiver_pos.y.eq(sender_pos.y),
                ]
            case Port.local:
                m.d.comb += [
                    # we assume we dont send packets to ourselves through the crossbar
                    Assume(receiver_pos != receiver.input.p),
                    receiver_pos.x.eq(sender_pos.x),
                    receiver_pos.y.eq(sender_pos.y),
                ]
            case _:
                assert False, f"unsupported port direction {sender_output_port}"

        with m.If(receiver.result.valid & receiver.result.valid):
            m.d.comb += Assert(receiver.result.p != receiver_output_port)

        return m, cd_sync

    def opposite(port: Port):
        return {
            Port.north: Port.south,
            Port.south: Port.north,
            Port.east: Port.west,
            Port.west: Port.east,
            Port.local: Port.local
        }[port]

    sender_dir = opposite(input_channel_position)
    # for sender_dir in Port.__members__.values():
    #     # if we send to locals its not continuing further on the mesh
    #     if sender_dir == Port.local:
    #         continue

    #     print("input channel", opposite(sender_dir))

    reachable = set()
    for receiver_dir in Port.__members__.values():
        m, cd_sync = build(sender_dir, receiver_dir)

        try:
            assertFormal(m, [
                cd_sync.clk, cd_sync.rst
            ], mode="prove", depth=20, tmp=True)
            # print("cannot reach", receiver_dir)
        except FormalVerificationFailed:
            # print(e, type(e))
            reachable.add(receiver_dir)
            # print("can reach", receiver_dir)

    # print(f"crossbar_opt: reachable ports for {input_channel_position}: {reachable}")
    return reachable
        # print()


if __name__ == "__main__":
    for input_channel_dir in Port.__members__.values():
        # if we send to locals its not continuing further on the mesh
        # if input_channel_dir == Port.local:
        #     continue

        print("input channel", input_channel_dir, "reaches", outputs_reachable_by(input_channel_dir, lambda: RouteComputer()))

    # reachable = set()
    # for receiver_dir in Port.__members__.values():
    #     m, cd_sync = build(sender_dir, receiver_dir)

    #     try:
    #         assertFormal(m, [
    #             cd_sync.clk, cd_sync.rst
    #         ], mode="prove", depth=20)
    #         # print("cannot reach", receiver_dir)
    #     except Exception as e:
    #         print(e)
    #         # print("can reach", receiver_dir)

    #     # print()
