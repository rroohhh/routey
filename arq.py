#!/usr/bin/env python3


from amaranth.lib import data

SEQ_WIDTH = 8

class ARQLayout(data.StructLayout):
    def __init__(self, contained: data.Layout):
        super().__init__({
            "seq":  SEQ_WIDTH,
            "data": contained,
        })
