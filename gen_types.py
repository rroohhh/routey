#!/usr/bin/env python3

import enum
from inspect import isclass
from amaranth import Shape, ShapeCastable
from amaranth.lib import data
from .tagged_union import TaggedUnion
from .wrap import EqSet, type_to_name, indent, pascal_case_to_snake_case

def shape_to_value_type(shape: Shape):
    assert not shape.signed
    return f"value<{shape.width}>"

def type_is_trivial(ty):
    if isinstance(ty, int) or isinstance(ty, Shape):
        if isinstance(ty, Shape):
            assert not ty.signed
            ty = ty.width

        match ty:
            case 1 | 8 | 16 | 32 | 64 | 128: return True

    return False

def type_to_name(ty, prefix="", field_name=""):
    if isinstance(ty, int) or isinstance(ty, Shape):
        if isinstance(ty, Shape):
            assert not ty.signed
            ty = ty.width

        match ty:
            case 1: return "bool"
            case 8: return "uint8_t"
            case 16: return "uint16_t"
            case 32: return "uint32_t"
            case 64: return "uint64_t"
            case 128: return "uint128_t"
            case _: return f"value<{ty}>"
    else:
        if hasattr(ty, "__name__"):
            return pascal_case_to_snake_case(ty.__name__)
        else:
            name = pascal_case_to_snake_case(field_name)
            if len(prefix) > 0:
                name = prefix + "_" + name

            assert len(prefix) + len(field_name) > 0
            return name

def gen_types_cpp(tys):
    defined_types = EqSet()

    defined_types.add("""template<size_t Bits, class IntegerT>
value<Bits> value_from_int(IntegerT i) {
    value<Bits> res;
    res.set(i);
    return res;
}""")
    def gen_type(ty, name=None):
        if isinstance(ty, int):
            return

        if name is None:
            name = type_to_name(ty)

        typedef = ""
        if isinstance(ty, enum.EnumMeta):
            shape = Shape.cast(ty)
            value_type = shape_to_value_type(shape)
            typedef += f"class {name} {{\n"
            typedef += f"public:\n"
            typedef += f"{indent}enum Value : uint64_t {{\n"
            typedef += ",\n".join(f"{indent*2}{name} = {value.value}" for name, value in ty.__members__.items()) + "\n"
            typedef += f"{indent}}};\n"
            # typedef += f"{indent}{name} Value() const {{ return value; }}\n"
            typedef += f"{indent}{name}(const Value & val) {{ v = val; }}\n"
            typedef += f"{indent}{name}(const {value_type} & val) {{ v = static_cast<Value>(val.template get<uint64_t>()); }}\n"
            typedef += f"{indent}operator {value_type}() const {{ {value_type} result; result.set(static_cast<uint64_t>(v)); return result; }}\n"
            typedef += f"{indent}operator Value() const {{ return v; }}\n"
            # typedef += f"auto operator<=>(const {name}&) const = default;\n"
            # typedef += f"auto operator<=>(const uint64_t& other) const {{ return v <=> other; }};\n"
            typedef += f"private:\n"
            typedef += f"{indent}Value v;\n"
            typedef += f"}};"
        else:
            layout = data.Layout.cast(ty)
            is_packed_union = False
            if isclass(ty) and issubclass(ty, TaggedUnion):
                # data_shapes = data.Layout.cast(layout['data'].shape).members
                data_layout = data.Layout.cast(layout['data'].shape)
                data_offset = layout['data'].offset
                packed_type = "struct"
                tag_field_list = [
                    (tag, data.Field((f := data_layout[tag.name]).shape, f.offset + data_offset))
                    for tag in layout['tag'].shape.__members__.values()
                ]
                is_packed_union = True
            else:
                match layout:
                    case data.StructLayout():
                        packed_type = "struct"
                    case data.UnionLayout():
                        packed_type = "union"
                    case _: # TODO(robin): how does default for match work?
                        assert False

            typedef += f"{packed_type} {name} {{\n"
            if is_packed_union:
                typedef += f"private:\n"
            for field_name, item in layout:
                item_ty = item.shape
                type_name = type_to_name(item_ty, field_name=field_name, prefix=name)
                typedef += f"{indent}{type_name} {field_name};\n"
                gen_type(item_ty, name=type_name)
            if is_packed_union:
                typedef += f"public:\n"

            def read_field(field):
                suffix = ""
                if type_is_trivial(field.shape):
                    type_name = type_to_name(field.shape)
                    suffix = f".template get<{type_name}>()"
                return f"val.template slice<{field.offset + field.width - 1}, {field.offset}>().val(){suffix}"
            def write_field(field, name):
                suffix = f" = {name}"
                if type_is_trivial(field.shape):
                    suffix = f" = value_from_int<{field.width}>({name})"
                return f"template slice<{field.offset + field.width - 1}, {field.offset}>(){suffix}"

            if packed_type == "struct" and not is_packed_union:
                shape = Shape.cast(ty)
                value_type = shape_to_value_type(shape)
                typedef += f"{indent}{name} & operator=(const {value_type} & val) {{\n"
                member_inits = [f"{indent*2}{field_name} = {read_field(item)};\n" for field_name, item in layout]
                typedef += "".join(member_inits)
                typedef += f"{indent*2}return *this;\n"
                typedef += f"{indent}}}\n"
                typedef += f"{indent}operator {value_type}() const {{\n"
                typedef += f"{indent*2}{value_type} result;\n"
                for field_name, item in layout:
                    typedef += f"{indent*2}result.{write_field(item, field_name)};\n"
                typedef += f"{indent*2}return result;\n"
                typedef += f"{indent}}}\n"
            if is_packed_union:
                shape = Shape.cast(ty)
                tag_field = layout['tag']
                tag_type_name = type_to_name(tag_field.shape)
                value_type = shape_to_value_type(shape)

                for tag, field in tag_field_list:
                    typedef += f"{indent}{name}(const {type_to_name(field.shape)} & val) : tag({tag_type_name}::{tag.name}), data{{.{tag.name} = val}} {{}}\n"

                typedef += f"{indent}operator {value_type}() const {{\n"
                typedef += f"{indent*2}{value_type} result;\n"
                typedef += f"{indent*2}result.{write_field(tag_field, 'tag')};\n"
                typedef += f"{indent*2}switch(tag) {{\n"
                for tag, field in tag_field_list:
                    typedef += f"{indent*3}case {tag_type_name}::{tag.name}: {{ result.{write_field(field, 'data.' + tag.name)}; break; }}\n"
                typedef += f"{indent*3}default: std::unreachable();\n"
                typedef += f"{indent*2}}}\n"
                typedef += f"{indent*2}return result;\n"
                typedef += f"{indent}}}\n"

                # typedef += f"{indent}{name}(const {value_type} & val) {{\n"
                # typedef += f"{indent*2}tag = {read_field(tag_field)};\n"
                # typedef += f"{indent*2}switch(tag) {{\n"
                # for tag, field in tag_field_list:
                #     typedef += f"{indent*3}case {tag_type_name}::{tag.name}: {{ data.{tag.name} = {read_field(field)}; break; }}\n"
                # typedef += f"{indent*3}default: std::unreachable();\n"
                # typedef += f"{indent*2}}}\n"
                # typedef += f"{indent*2}return result;\n"
                # typedef += f"{indent}}}\n"

                typedef += f"{indent}std::variant<{', '.join(type_to_name(field.shape) for _, field in tag_field_list)}> get() const {{\n"
                typedef += f"{indent*2}switch(tag) {{\n"
                for tag, field in tag_field_list:
                    typedef += f"{indent*3}case {tag_type_name}::{tag.name}: {{ return data.{tag.name}; }}\n"
                typedef += f"{indent*3}default: std::unreachable();\n"
                typedef += f"{indent*2}}}\n"
                typedef += f"{indent}}}\n"


            typedef += f"}};"

        defined_types.add(typedef)

    for ty in tys:
        gen_type(ty)

    return defined_types

if __name__ == "__main__":
    import sys, importlib

    types = []
    for name in sys.argv[1:]:
        py_module_name, py_class_name = name.rsplit(".", 1)
        py_module = importlib.import_module(py_module_name)
        py_class = py_module.__dict__[py_class_name]
        if not isinstance(py_class, type) or not isinstance(py_class, ShapeCastable):
            raise TypeError("{}.{} is not a class inheriting from Elaboratable"
                            .format(py_module_name, py_class_name))
        types.append(py_class)
    print("\n\n".join(gen_types_cpp(types)))
