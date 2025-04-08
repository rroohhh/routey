#!/usr/bin/env python3


from amaranth.asserts import AnyConst, AnySeq
from amaranth.lib.wiring import Component, Signature, In, connect, flipped
from amaranth import Elaboratable, Signal, Assume, Assert, Module, Cover
from amaranth.lib import stream


class FormalScoreboard(Component):
    def __init__(self, payload_shape):
        super().__init__(Signature({
            "input": In(stream.Signature(payload_shape, always_ready = True)),
            "output": In(stream.Signature(payload_shape, always_ready = True)),
        }))

    def elaborate(self, _):
        m = Module()
        watched_data = AnyConst(self.input.p.shape())
        trigger = AnySeq(1)

        # kind of arbitrary size, must be bigger than sequential depth
        tracking_counter = Signal(32)
        wait_counter = Signal(32)

        sampled_input = Signal()
        sampled_output = Signal()

        incr = self.input.valid & ~sampled_input
        decr = self.output.valid & ~sampled_output

        ready_to_sample_input = (self.input.p == watched_data) & incr & trigger;
        ready_to_sample_output = decr & (((tracking_counter == 0) & ready_to_sample_input) | ((tracking_counter == 1) & sampled_input))

        m.d.sync += [
            sampled_input.eq(sampled_input | ready_to_sample_input),
            sampled_output.eq(sampled_output | ready_to_sample_output),
            tracking_counter.eq(tracking_counter + incr - decr),
            wait_counter.eq(wait_counter + sampled_input - sampled_output),
            # Assert(wait_counter < 16),
            # Cover(wait_counter == 8),
            Cover(sampled_input),
            Cover(ready_to_sample_output, "formal scoreboard sanity check covered"),
            Cover(sampled_input & sampled_output, "formal scoreboard sanity check covered"),
        ]
        with m.If(ready_to_sample_output):
            m.d.sync += Assert(self.output.p == watched_data, "scoreboard data mismatch")

        return m

class WolperCheck(Component):
    input: In(stream.Signature(1, always_ready=True))

    def __init__(self, assume = True):
        self._assume = assume
        super().__init__()

    def elaborate(self, _):
        m = Module()

        input = self.input

        with m.If(input.valid):
            with m.FSM() as fsm:
                with m.State("WAITING_FOR_ONE"):
                    with m.If(input.p):
                        m.next = "SAW_ONE"
                with m.State("SAW_ONE"):
                    with m.If(input.p):
                        m.next = "ZEROS"
                    with m.Else():
                        m.next = "ERROR"
                with m.State("ZEROS"):
                    with m.If(input.p):
                        m.next = "ERROR"
                with m.State("ERROR"):
                    ...


        if self._assume:
            m.d.comb += Assume(~fsm.ongoing("ERROR"))
        else:
            m.d.comb += Assert(~fsm.ongoing("ERROR"))

        return m


# this can only be used for cases where the datapath does not influence the control logic
class FormalScoreboardWolper(Component):
    input: In(stream.Signature(1, always_ready = True))
    output: In(stream.Signature(1, always_ready = True))

    def elaborate(self, _):
        m = Module()
        m.submodules.input_assume = input = WolperCheck(assume=True)
        m.submodules.output_assert = output = WolperCheck(assume=False)
        print(self.input)
        connect(m, flipped(self.input), input.input)
        connect(m, flipped(self.output), output.input)
        return m


class AXISStreamContract(Elaboratable):
    def __init__(self, stream, c=Assume):
        self.stream = stream
        self.c = c

    def elaborate(self, _):
        c = self.c

        m = Module()

        outstanding = Signal()
        last_payload = Signal.like(self.stream.p)

        with m.If(self.stream.valid & self.stream.ready):
            m.d.sync += outstanding.eq(0)

        with m.If(self.stream.valid & ~self.stream.ready):
            m.d.sync += outstanding.eq(1)
            m.d.sync += last_payload.eq(self.stream.p)

        with m.If(outstanding):
            m.d.comb += [
                c(self.stream.valid),
                c(last_payload == self.stream.payload),
            ]

        if c is Assert:
            m.d.comb += Cover(~self.stream.ready & self.stream.valid)

        return m
