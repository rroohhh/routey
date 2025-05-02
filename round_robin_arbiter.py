#!/usr/bin/env python3

from amaranth import Module
from amaranth.lib.wiring import Component, In, Out


# asserts round robin on requests and grant_store
# asserting next sync writes grant to grant_store
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
