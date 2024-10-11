# amaranth: UnusedElaboratable=no

import re, enum
from collections import defaultdict
from amaranth.lib import wiring, stream, data
from amaranth import Shape, Value, Fragment, Elaboratable
from .memory_mapped_router import MemoryMappedRouter
from .wrap import pascal_case_to_snake_case, indent, EqSet, type_to_name, path_to_name

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
            typedef += f"typedef enum {type_to_name(shape)} {{\n"
            typedef += ",\n".join(f"{indent}{name.upper()} = {value.value}" for name, value in ty.__members__.items()) + "\n"
            typedef += f"}} {name};"
        else:
            match layout := data.Layout.cast(ty):
                case data.StructLayout():
                    packed_type = "struct"
                case data.UnionLayout():
                    packed_type = "union"
                case _: # TODO(robin): how does default for match work?
                    assert False

            typedef += f"typedef {packed_type} packed {{\n"
            for field_name, item in layout:
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

    generated += "endmodule;"
    types_to_generate = set()

    module_gen = generated
    generated = ""
    for i, sig in enumerate(signatures_to_gen):
        name = name_for_sig(sig, field_names[i])

        generated += f"interface {name};\n"

        name_polarity = []
        for path, thing in iter_flat_signature(sig):
            name = path_to_name(path)
            name_polarity.append((name, thing.flow == wiring.In))
            generated += f"{indent}{type_to_name(thing.shape)} {name};\n"

            types_to_generate.add(thing.shape)

        generated += "\n"

        generated += f"{indent}modport master (\n"
        generated += gen_modport_items(name_polarity)
        generated += f"{indent});\n"

        generated += f"{indent}modport slave (\n"
        generated += gen_modport_items(((n, not p) for n, p in name_polarity))
        generated += f"{indent});\n"

        generated += "endinterface\n\n"

    generated = "\n\n".join(gen_types(types_to_generate)) + "\n\n" + generated


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
