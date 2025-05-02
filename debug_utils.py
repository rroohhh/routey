#!/usr/bin/env python3

from amaranth.lib import stream
from amaranth import Value, ValueCastable
from amaranth.lib import wiring
from amaranth.lib.wiring import FlippedInterface

def mark_debug(*args):
    for arg in args:
        if isinstance(arg, stream.Interface):
            mark_debug(arg.ready, arg.valid, arg.p)
        elif isinstance(arg, FlippedInterface):
            mark_debug(wiring.flipped(arg))
        elif isinstance(arg, ValueCastable):
            mark_debug(Value.cast(arg))
        elif isinstance(arg, Value):
            arg.attrs["debug_item"] = 1
        elif isinstance(arg, list):
            mark_debug(*arg)
        else:
            assert False
