# amaranth: UnusedElaboratable=no

import enum
from collections import defaultdict
from amaranth.lib import wiring, stream, data
from amaranth import Shape, Value, Fragment, Elaboratable
from memory_mapped_router import MemoryMappedRouter
from wrap import pascal_case_to_snake_case, indent, EqSet, type_to_name, path_to_name

def name_for_sig(sig: wiring.Signature, field_names=list):
    if isinstance(sig, stream.Signature):
        return pascal_case_to_snake_case(sig._payload_shape.__name__) + "_stream_if"
    else:
        assert len(field_names) == 1
        return field_names[0] + "_if"

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
        if isinstance(ty, int):
            return

        if name is None:
            name = type_to_name(ty)

        typedef = ""
        if isinstance(ty, enum.EnumMeta):
            shape = Shape.cast(ty)
            typedef += f"package {name};\n"
            typedef += f"typedef enum {type_to_name(shape)} {{\n"
            typedef += ",\n".join(f"{indent}{name.upper()} = {value.value}" for name, value in ty.__members__.items()) + "\n"
            typedef += f"}} {name};\n"
            typedef += f"endpackage"
            # typedef += f"import {name}::{name};"
        else:
            layout = data.Layout.cast(ty)
            if isinstance(layout, data.StructLayout):
                packed_type = "struct"
            elif isinstance(layout, data.UnionLayout):
                packed_type = "union"
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


dut = MemoryMappedRouter()

def generate(dut):
    signatures_to_gen = EqSet()
    field_names = defaultdict(list)

    module_name = pascal_case_to_snake_case(dut.__class__.__name__)
    pkg_name = module_name + "_pkg"
    generated = f"module {module_name} (\n"

    (frag := Fragment.get(dut, None)).prepare()
    ports = []
    port_splats = []
    # TODO(robin): this is wrong if we generate domains internally i guess?
    for domain in frag.domains.values():
        ports.append(f"{indent}input wire {domain.clk.name}")
        port_splats.append(f"{indent*2}.{domain.clk.name}")
        if (rst := domain.rst) is not None:
            ports.append(f"{indent}input wire {rst.name}")
            port_splats.append(f"{indent*2}.{rst.name}")

    for name, member in dut.signature.members.items():
        sig = member.signature
        is_flipped = False
        if isinstance(sig, wiring.FlippedSignature):
            is_flipped = True
            sig = sig.flip()
        field_names[signatures_to_gen.add(sig)].append(name)

        port_type = name_for_sig(sig, [name])
        port_dir = "slave" if is_flipped else "master"

        ports.append(f"{indent}{port_type}.{port_dir} {name}")

        # have to flatten this to ports somehow

        for path, _, sig in member.signature.flatten(getattr(dut, name)):
            sig = Value.cast(sig)
            port_splats.append(f"{indent*2}.{sig.name}({name}.{'_'.join(path)})")

    generated += ",\n".join(ports) + "\n);\n"

    fqp = dut.__class__.__module__ + "." + dut.__class__.__name__

    generated += f"{indent}// connect_rpc -exec amaranth-rpc yosys {fqp}\n"
    generated += f"{indent}\\{fqp}  {module_name}_internal (\n"
    generated += f",\n".join(port_splats) + "\n"
    generated += f"{indent});\n"

    generated += "endmodule"
    types_to_generate = set()

    module_gen = generated
    generated = ""
    for i, sig in enumerate(signatures_to_gen):
        name = name_for_sig(sig, field_names[i])
        is_stream = isinstance(sig, stream.Signature)

        generated += f"interface {name} import {pkg_name}::*;;\n"

        name_polarity = []
        for path, thing in iter_flat_signature(sig):
            name = path_to_name(path)
            generated += f"{indent}{type_to_name(thing.shape)} {name};\n"
            types_to_generate.add(thing.shape)

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
        "".join(f"import {i}::{i};\n" for i in imports) + \
        "".join(f"export {i}::{i};\n" for i in imports) + \
        "\n\n".join(normal) + "\nendpackage\n\n" + \
        gen


    return generated + module_gen

if __name__ == "__main__":
    import sys, importlib

    for name in sys.argv[1:]:
        if "(" in name:
            name, args = name.rsplit("(")
        else:
            args = ""

        args = args.removesuffix(")")
        py_module_name, py_class_name = name.rsplit(".", 1)
        py_module = importlib.import_module(py_module_name)
        py_class = py_module.__dict__[py_class_name]
        if not isinstance(py_class, type) or not issubclass(py_class, Elaboratable):
            raise TypeError("{}.{} is not a class inheriting from Elaboratable"
                            .format(py_module_name, py_class_name))
        print(eval(f"generate({py_class_name}({args}))"))
