#!/usr/bin/env python3

from typing import Dict
from amaranth import *
from amaranth.lib import enum, data, wiring
from amaranth.lib.wiring import In, Out

class UTLayout(data.StructLayout):
    def __init__(self, alphabet: Dict[str, data.Layout]):
        super().__init__({
            "idx":  enum.Enum("Kind", [name for name in alphabet.keys()]),
            "data": data.UnionLayout(alphabet),
        })


class UTSignature(wiring.Signature):
    def __init__(self, layout: UTLayout):
        super().__init__({
            "data": Out(layout),
            "valid": Out(1),
            "next": In(1)
        })

    def __eq__(self, other):
        return self.members == other.members
