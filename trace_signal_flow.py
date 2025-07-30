#!/usr/bin/env python
from amaranth import *
from amaranth.lib import stream
from amaranth.lib.data import ArrayLayout, Layout, StructLayout, ShapeCastable
import json

from debug_utils import mark_debug

def grab_from_layout_by_type(layout, signal, containee):
    if layout is containee:
        yield signal
    else:
        if isinstance(layout, ShapeCastable):
            try:
                layout = Layout.cast(layout)
                # TODO(robin): this only supports struct or array layout, because fuck you
                if isinstance(layout, (StructLayout, ArrayLayout)):
                    for name, member in layout:
                        yield from grab_from_layout_by_type(member.shape, layout(signal)[name], containee)
                else:
                    print(layout)
                    assert False
            except TypeError:
                pass
        else:
            pass

def find_valid_ready(thing, signature, path):
    def find_valid_ready_inner(thing, signature, path):
        for p in path:
            # sub signature
            if isinstance(p, str):
                member = signature.members[p]
                if member.is_port:
                    return None
                signature = member.signature
                thing = getattr(thing, p)
            # array dimension
            else:
                thing = thing[p]
        if hasattr(thing, "valid_ready"):
            return thing.valid_ready
        elif isinstance(signature, stream.Signature) or (
                hasattr(thing, "ready") and hasattr(thing, "valid")):
            return thing.valid, thing.ready
        else:
            # TODO(robin): we could recurse upwards over path here
            # but is not necessary atm
            return None

    return find_valid_ready_inner(thing, signature, path[:-1])


def grab_from_sig_by_type(thing, signature, containee):
    for path, desc, signal in signature.flatten(thing):
        valid_ready_sig = find_valid_ready(thing, signature, [*path])
        for entry in grab_from_layout_by_type(desc.shape, signal, containee):
            assert valid_ready_sig is not None
            yield desc.flow, path, entry, *valid_ready_sig

class _Visitor:
    def __init__(self, type):
        self.to_trace = type
        self.sample_points = []

    def visit_frag(self, frag, path = None):
        if path is None:
            path = []

        if hasattr(frag, "origins") and frag.origins is not None and hasattr(frag.origins[0], "signature"):
            elaboratable = frag.origins[0]
            entries = list(grab_from_sig_by_type(elaboratable, elaboratable.signature, self.to_trace))

            for info in entries:
                self.sample_points.append((path, *info))


        for frag, frag_name, src_loc in frag.subfragments:
            self.visit_frag(frag, [*path, frag_name])

def trace_signal_flow(m: Module, ty, accessor = lambda s: s):
    frag = Fragment.get(m, None)

    vis = _Visitor(ty)
    vis.visit_frag(frag)

    ports = []

    comp = frag.origins[0]
    for _, _, sig in comp.signature.flatten(comp):
        if not isinstance(sig, Const):
            ports.append(Value.cast(sig))

    for i, (path, flow, sig_path, sig, valid_sig, ready_sig) in enumerate(vis.sample_points):
        # print(path, sig_path, sig, valid_sig, ready_sig)
        strobe = Signal(name=f"trace_sample_{i}_strobe")
        sample = Signal.like(accessed := accessor(sig), name=f"trace_sample_{i}")

        strobe.attrs["signal_flow_sample_strobe"] = 1
        sample.attrs["signal_flow_sample"] = 1
        # normalize paths to string components for external consumption
        sample.attrs["module"] = json.dumps([str(p) for p in path])
        sample.attrs["interface"] = json.dumps([str(p) for p in sig_path])
        sample.attrs["direction"] = "in" if flow == flow.In else "out"

        mark_debug(strobe, sample)


        # for inputs, we generate a sample whenever valid is asserted and do not wait for ready
        # valid being asserted indicates the module will / might start processing the input
        # for outputs, we generate a sample whenever valid and ready are asserted, only then the output was actually transmitted out
        frag.add_statements("comb", [
            sample.eq(accessed)
        ])

        if flow == flow.Out:
            frag.add_statements("comb", [
                strobe.eq(valid_sig & ready_sig),
            ])
        else:
            is_old = Signal()
            frag.add_statements("sync", [
                is_old.eq(valid_sig & ~ready_sig),
            ])
            frag.add_statements("comb", [
                strobe.eq(valid_sig & ~is_old),
            ])
    return frag, ports
        # print(path, flow, sig_path, sig, strobe_sig)
