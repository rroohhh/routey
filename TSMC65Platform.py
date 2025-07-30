#!/usr/bin/env python3

from dataclasses import dataclass
from amaranth import Cat, ClockSignal, Instance, Module, Shape, Value
from amaranth.build import Platform
from amaranth.lib.memory import Memory

@dataclass
class MemoryTemplate:
    read_ports: int
    write_ports: int

    transparent: bool

    template_string: str

    async_read: bool

    max_width: int


class TSMC65Platform(Platform):
    connectors = []
    required_tools = []
    resources = []
    toolchain_prepare = []

    memories = [
        MemoryTemplate(
            read_ports = 1,
            write_ports = 1,
            transparent = False,
            template_string = "TS6N65LPLLA{depth}X{width}M2M",
            async_read = False,
            max_width = 72
        )
    ]

    def get_memory(self, mem: Memory):
        read_ports = mem.read_ports
        write_ports = mem.write_ports

        transparent = any(rp.transparent_for for rp in read_ports)
        async_read = any(rp.domain == "comb" for rp in read_ports)

        for tmpl in self.memories:
            if len(read_ports) <= tmpl.read_ports and \
               len(write_ports) <= tmpl.write_ports and \
               transparent == tmpl.transparent and \
               async_read == tmpl.async_read:
                offset = 0
                width = Shape.cast(mem.shape).width

                write_port = write_ports[0]
                read_port = read_ports[0]

                m = Module()

                while offset < width:
                    part = min(width - offset, tmpl.max_width)

                    gran = write_port.signature.granularity
                    if gran is None:
                        bwe = write_port.en.replicate(part)
                        we = write_port.en
                    else:
                        assert False

                    m.submodules[f"buffer_{offset}_{part}"] = Instance(
                        tmpl.template_string.format(width = part, depth = mem.depth),
                        i_AA = write_port.addr,
                        i_D = Value.cast(write_port.data)[offset:offset + part],
                        i_BWEB = ~bwe,
                        i_WEB = ~we,
                        i_CLKW = ClockSignal(write_port.domain),
                        i_AB = read_port.addr,
                        i_REB = ~read_port.en,
                        i_CLKR = ClockSignal(read_port.domain),
                        o_Q = Value.cast(read_port.data)[offset:offset + part]
                    )

                    offset += part

                return m

            # buffer_write.en.eq(push),
            # buffer_write.addr.eq(write_ptr),
            # buffer_write.data.eq(self.input.p),
        else:
            return mem.elaborate(None)



# module TS6N65LPLLA64X64M2M
#   (AA,
#   D,
#   BWEB,
#   WEB,CLKW,
#   AB,
#   REB,CLKR,
#   Q);
