#!/usr/bin/env python3

from ut import UTLayout
from arq import ARQLayout

from amaranth import *
from amaranth.lib import data

EVENT_WIDTH = 14
NUM_SPL1_IF = 4

class L2Event(data.Struct):
    l1_address: range(NUM_SPL1_IF)
    neuron_address: EVENT_WIDTH

Timestamp = unsigned(8)

class TimestampedEvent(data.Struct):
    timestamp: Timestamp
    event: L2Event

def EventPack(n_packed):
    return data.ArrayLayout(TimestampedEvent, n_packed)

def MADCPack(n_packed):
    return data.ArrayLayout(TimestampedEvent, n_packed)

class SystimeResp(data.Struct):
    timestamp: Timestamp
    event: L2Event

NUM_PACK_EVENT = 3
NUM_PACK_MADC = NUM_PACK_EVENT
NUM_PPU = 2

PPU_ADDRESS_WIDTH = 32
PPU_CMD_DATA_WIDTH = 128
PPU_DATA_WIDTH = 64
PPU_INSTR_WIDTH = 32

class PPUCmd(data.Struct):
    address: PPU_ADDRESS_WIDTH
    byteen: PPU_CMD_DATA_WIDTH / 8
    rnw: 1

PPUCmdData = PPU_DATA_WIDTH

class PPUInstrReq(data.Struct):
    address: PPU_ADDRESS_WIDTH

PPUInstrData = PPU_INSTR_WIDTH

FromAsicSinglePPUAlphabet = {
    "PPUCmd": PPUCmd,
    "PPUCmdData": PPUCmdData,
    "PPUInstrReq": PPUInstrReq,
}

OmnibusAddress = 32
OmnibusData = 32

class OmnibusCmd(data.Struct):
    address: OmnibusAddress
    byte_en: OmnibusData / 8
    rnw: bool

Loopback = 59

FromAsicARQAlphabet = {
    "OmnibusData": OmnibusData,
    **{
        name + f"<{n}>": layout for n in range(NUM_PPU) for name, layout in FromAsicSinglePPUAlphabet.items()
    },
    "Loopback": Loopback,
}

def arq_encoded(entries):
    return {
        name: ARQLayout(layout) for name, layout in entries.items()
    }

FromAsicLayout = UTLayout({
    **{f"MADCPack<{n}>": MADCPack(n) for n in range(1, NUM_PACK_MADC + 1)},
    **{f"EventPack<{n}>": EventPack(n) for n in range(1, NUM_PACK_EVENT + 1)},
    **arq_encoded(FromAsicARQAlphabet),
    "SystimeResp": SystimeResp
})

ToAsicSinglePPUAlphabet = {
    "PPUCmdData": PPUCmdData,
    "PPUInstrResp": PPUInstrData,
}

ToAsicARQAlphabet = {
    "OmnibusCmd": OmnibusCmd,
    "OmnibusData": OmnibusData,
    **{
        name + f"<{n}>": layout for n in range(NUM_PPU) for name, layout in ToAsicSinglePPUAlphabet.items()
    },
    "Loopback": Loopback,
}

SystimeCmd = 1

ToAsicLayout = UTLayout({
    **{f"EventPack<{n}>": EventPack(n) for n in range(1, NUM_PACK_EVENT + 1)},
    **arq_encoded(ToAsicARQAlphabet),
    "SystimeCmd": SystimeCmd,
})
