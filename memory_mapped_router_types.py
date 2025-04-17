#!/usr/bin/env python3

from amaranth import unsigned
from amaranth.lib import enum

# TODO(robin): remove shape again
class CardinalPort(enum.Enum, shape=unsigned(3)):
    local = 0
    north = enum.auto()
    south = enum.auto()
    east = enum.auto()
    west = enum.auto()
