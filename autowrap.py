# amaranth: UnusedElaboratable=no

import enum
from collections import defaultdict
from amaranth.lib import wiring, stream, data
from amaranth.hdl._ir import  PortDirection
from amaranth import Shape, Value, Fragment, Elaboratable, Signal, Const, ValueCastable
from TSMC65Platform import TSMC65Platform
from wrap import pascal_case_to_snake_case, indent, EqSet, type_to_name, path_to_name

def name_for_sig(sig: wiring.Signature, field_names=list, prefix=None):
    if prefix is None:
        prefix = ""
    else:
        prefix = prefix + "_"
    if isinstance(sig, stream.Signature):
        payload_shape = sig._payload_shape
        if isinstance(payload_shape, int) or isinstance(payload_shape, range) or isinstance(payload_shape, data.ArrayLayout):
            name = prefix + field_names[0]
        else:
            name = type_to_name(payload_shape)
        return pascal_case_to_snake_case(name) + "_stream_if"
    else:
        if isinstance(sig, wiring.Signature) and type(sig) is not wiring.Signature:
            name = sig.__class__.__name__.removesuffix("Signature")
            name = pascal_case_to_snake_case(name)
        else:
            name = prefix + field_names[0]
            assert len(field_names) == 1
        return name + "_if"

def iter_flat_signature(sig: wiring.Signature, path = None):
    if path is None:
        path = []

    for name, member in sig.members.items():
        concat_path = path + [name]
        if member.is_port:
            yield concat_path, member
        else:
            yield from iter_flat_signature(member.signature, concat_path)

def polarity_to_sv_dir(polarity: bool):
    if isinstance(polarity, wiring.Flow):
        polarity = polarity == wiring.In
    if polarity:
        return "input"
    else:
        return "output"

def gen_modport_items(items):
    return ",\n".join((
        f"{indent*2}{polarity_to_sv_dir(polarity)} {name}"
        for name, polarity in items
    )) + "\n"

def gen_types(tys):
    defined_types = EqSet()

    def gen_type(ty, name=None):
        if isinstance(ty, int) or isinstance(ty, range):
            return

        if name is None:
            name = type_to_name(ty)

        typedef = ""
        if isinstance(ty, enum.EnumMeta):
            shape = Shape.cast(ty)
            typedef += f"package {name}_pkg;\n"
            typedef += f"typedef enum {type_to_name(shape)} {{\n"
            typedef += ",\n".join(f"{indent}{name.upper()} = {value.value}" for name, value in ty.__members__.items()) + "\n"
            typedef += f"}} {name}_t;\n"
            typedef += f"endpackage"
            # typedef += f"import {name}::{name};"
        else:
            layout = data.Layout.cast(ty)
            if isinstance(layout, data.StructLayout):
                packed_type = "struct"
            elif isinstance(layout, data.UnionLayout):
                packed_type = "union"
            elif isinstance(layout, data.ArrayLayout):
                type_name = type_to_name(layout.elem_shape, prefix=name)
                typedef = f"typedef {type_name}[{layout.length - 1}:0] {name};"
                gen_type(layout.elem_shape, name=type_name)
                defined_types.add(typedef)
                return
            else:
                assert False


            typedef += f"typedef {packed_type} packed {{\n"
            for field_name, item in list(layout)[::-1]:
                ty = item.shape
                type_name = type_to_name(ty, field_name=field_name, prefix=name)
                typedef += f"{indent}{type_name} {field_name};\n"
                gen_type(ty, name=type_name)
            typedef += f"}} {name};"

        defined_types.add(typedef)

    for ty in tys:
        gen_type(ty)

    return defined_types


# dut = MemoryMappedRouter()
def shape_and_value_to_literal(shape, value):
    if shape.signed:
        return f"{shape.width}'sd{value}"
    else:
        return f"{shape.width}'d{value}"

def generate(dut, include_impl, platform):
    signatures_to_gen = EqSet()
    field_names = defaultdict(list)

    module_name = pascal_case_to_snake_case(dut.__class__.__name__)
    pkg_name = module_name + "_pkg"
    generated = f"module {module_name} import {pkg_name}::*;\n (\n"

    (frag := Fragment.get(dut, None)).prepare()
    ports = []
    port_splats = []
    assigns = []
    # TODO(robin): this is wrong if we generate domains internally i guess?
    for domain in frag.domains.values():
        ports.append(f"{indent}input wire {domain.clk.name}")
        port_splats.append(f"{indent*2}.{domain.clk.name}")
        if (rst := domain.rst) is not None:
            ports.append(f"{indent}input wire {rst.name}")
            port_splats.append(f"{indent*2}.{rst.name}")

    types_to_generate = EqSet()
    sig_dupes = defaultdict(set)
    for name, member in dut.signature.members.items():
        orig_name = name
        if name == "input":
            name = "in"
        if name == "output":
            name = "out"

        assert len(member.dimensions) <= 1
        dimension_suffix = ""
        if len(member.dimensions) == 1:
            dimension_suffix = f"[{member.dimensions[0]}]"

        is_stream = False
        try:
            sig = member.signature
            is_stream = isinstance(sig, stream.Signature)
            is_flipped = False
            if isinstance(sig, wiring.FlippedSignature):
                is_flipped = True
                sig = sig.flip()
            field_names[signatures_to_gen.add(sig)].append(name)
            port_type = name_for_sig(sig, [name], prefix=module_name)
            sig_dupes[signatures_to_gen.add(sig)].add(port_type)
            port_dir = "slave" if is_flipped else "master"
            ports.append(f"{indent}{port_type}.{port_dir} {name}{dimension_suffix}")
        except AttributeError:
            type_name = type_to_name(member.shape, field_name=name)
            types_to_generate.add(member.shape)
            ports.append(f"{indent}{polarity_to_sv_dir(member.flow)} wire {type_name} {name}{dimension_suffix}")


        # have to flatten this to ports somehow
        def splat(s, i):
            a = ""
            if i is not None:
                a = f"[{i}]"

            if isinstance(s, ValueCastable) or isinstance(s, Signal):
                sig = Value.cast(s)
                port_splats.append(f"{indent*2}.{sig.name}({name}{a})")
            else:
                for path, flow, sig in member.signature.flatten(s):
                    if is_stream and path[0] == "payload":
                        path = ["p"]
                    sig = Value.cast(sig)
                    intf_name = f"{name}{a}.{'_'.join(path)}"
                    if isinstance(sig, Const):
                        assert flow.flow == wiring.Out
                        assigns.append(f"{indent}assign {intf_name} = {shape_and_value_to_literal(sig.shape(), sig.value)};")
                    else:
                        if isinstance(flow.shape, data.ArrayLayout):
                            port_splats.append(f"{indent*2}.{sig.name}({{<<{Shape.cast(flow.shape.elem_shape).width}{{{intf_name}}}}})")
                        else:
                            port_splats.append(f"{indent*2}.{sig.name}({intf_name})")

        obj = getattr(dut, orig_name)
        if len(member.dimensions) > 0:
            for i, s in enumerate(obj):
                splat(s, i)
        else:
            splat(obj, None)


    generated += ",\n".join(ports) + "\n);\n"

    fqp = dut.__class__.__module__ + "." + dut.__class__.__name__

    generated += f"{indent}// connect_rpc -exec amaranth-rpc yosys {fqp}\n"
    generated += f"{indent}\\{fqp}  {module_name}_internal (\n"
    generated += f",\n".join(port_splats) + "\n"
    generated += f"{indent});\n"
    if len(assigns) > 0:
        generated += f"\n"
        generated += "\n".join(assigns)
        generated += f"\n"

    generated += "endmodule\n"

    if include_impl:
        from amaranth.back.verilog import convert
        conv_ports = {}
        for path, member, value in dut.signature.flatten(dut):
            if isinstance(value, ValueCastable):
                value = value.as_value()
            if isinstance(value, Const):
                assert member.flow == wiring.Out
                continue
            if isinstance(value, Value):
                if member.flow == wiring.In:
                    dir = PortDirection.Input
                else:
                    dir = PortDirection.Output
                conv_ports["__".join(map(str, path))] = (value, dir)
        generated += convert(dut, name=fqp, ports=conv_ports, platform=platform)

    module_gen = generated
    generated = ""
    for i, sig in enumerate(signatures_to_gen):
        for name in sig_dupes[i]:
            # name = name_for_sig(sig, field_names[i], prefix=module_name)
            is_stream = isinstance(sig, stream.Signature)

            generated += f"interface {name} import {pkg_name}::*;;\n"

            name_polarity = []
            for path, thing in iter_flat_signature(sig):
                suffix = ""
                s = thing.shape
                if isinstance(s, data.ArrayLayout):
                    suffix = f"[{s.length}]"
                    s = s.elem_shape
                name = path_to_name(path)
                generated += f"{indent}{type_to_name(s)} {name}{suffix};\n"
                types_to_generate.add(s)

                if is_stream and name == "payload":
                    continue
                name_polarity.append((name, thing.flow == wiring.In))

            generated += "\n"

            generated += f"{indent}modport master (\n"
            if is_stream:
                generated += f"{indent*2}output .p(payload),\n"
            generated += gen_modport_items(name_polarity)
            generated += f"{indent});\n"

            generated += f"{indent}modport slave (\n"
            if is_stream:
                generated += f"{indent*2}input .p(payload),\n"
            generated += gen_modport_items(((n, not p) for n, p in name_polarity))
            generated += f"{indent});\n"

            generated += f"{indent}modport monitor (\n"
            if is_stream:
                generated += f"{indent*2}input .p(payload),\n"
            generated += gen_modport_items(((n, True) for n, p in name_polarity))
            generated += f"{indent});\n"

            generated += "endinterface\n\n"

    types = gen_types(types_to_generate)
    pkgs = []
    normal = []
    imports = []

    for type in types:
        if 'package' in type:
            pkgs.append(type)
            imports.append(type.split()[1][:-1])
        else:
            normal.append(type)

    gen = generated
    generated = "\n\n".join(pkgs) + "\n\n"
    generated += f"package {pkg_name};\n" + \
        "".join(f"import {i}::{i.removesuffix('_pkg')};\n" for i in imports) + \
        "".join(f"export {i}::{i.removesuffix('_pkg')};\n" for i in imports) + \
        "\n\n".join(normal) + "\nendpackage\n\n"
    generated += gen


    return generated + module_gen

if __name__ == "__main__":
    import sys, importlib
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--platform", action='store', help="platform", default="tsmc")
    parser.add_argument("-i", action='store_true', help="include impls")
    parser.add_argument("classes", nargs="+", help="what to generate")
    res = parser.parse_args()

    platform = {
        "tsmc": TSMC65Platform(),
        "sim": None
    }[res.platform]

    for name in res.classes:
        if "(" in name:
            name, args = name.split("(", 1)
        else:
            args = ""

        args = args.removesuffix(")")
        py_module_name, py_class_name = name.rsplit(".", 1)
        py_module = importlib.import_module(py_module_name)
        py_class = py_module.__dict__[py_class_name]
        if not isinstance(py_class, type) or not issubclass(py_class, Elaboratable):
            raise TypeError("{}.{} is not a class inheriting from Elaboratable"
                            .format(py_module_name, py_class_name))
        print(generate(eval(f"py_class({args})", globals(), {
            py_module_name: py_module,
            **locals()
        }), res.i, platform))
