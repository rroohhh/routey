#!/usr/bin/env python3

from amaranth import *
from amaranth.back.verilog import convert
from amaranth.lib.wiring import Component, In, Out

from ut import UTSignature, UTLayout
from l2 import ToAsicLayout, FromAsicLayout
from fpga import ToFPGALayout, FromFPGALayout


FatmeshyLayout = UTLayout({
    "Dummy": 64
})

NUM_PHY_FPGA = 8
NUM_PHY_ASIC = 8
NUM_PHY_SIDE = 16

class RouterTop(Component):
    ut_write_asic: Out(UTSignature(ToAsicLayout)).array(NUM_PHY_ASIC)
    ut_read_asic: In(UTSignature(FromAsicLayout)).array(NUM_PHY_ASIC)

    ut_write_fpga: Out(UTSignature(ToFPGALayout)).array(NUM_PHY_FPGA)
    ut_read_fpga: In(UTSignature(FromFPGALayout)).array(NUM_PHY_FPGA)

    ut_w_n: Out(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_r_n:  In(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_w_s: Out(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_r_s:  In(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_w_e: Out(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_r_e:  In(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_w_w: Out(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)
    ut_r_w:  In(UTSignature(FatmeshyLayout)).array(NUM_PHY_SIDE)

    def elaborate(self, _):
        m = Module()

        return m


top = RouterTop()

# print(convert(RouterTop()))
