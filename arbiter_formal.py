#!/usr/bin/env python3

from amaranth import Assert, Module, Assume, Signal, ClockDomain, Cover, Mux, Print
from amaranth.sim import Simulator
from amaranth.lib.wiring import Component, In

from utils import assertFormal
from memory_mapped_router import RoundRobinArbiter

