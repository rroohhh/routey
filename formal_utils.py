#!/usr/bin/env python3


from amaranth.asserts import AnyConst, AnySeq
from amaranth.lib.wiring import Component, Signature, In
from amaranth.lib import stream
from amaranth import Assert, Cover, Signal, Module

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
        tracking_counter = Signal(3)
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
