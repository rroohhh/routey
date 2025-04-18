#!/usr/bin/env python3

from amaranth import Signal, ShapeCastable, Const, Shape, Module, Format, Mux
from amaranth.lib import data
from amaranth.lib.data import View, StructLayout, UnionLayout, Layout, Const as DataConst
from amaranth.back.rtlil import convert
import amaranth.lib.enum
import contextlib
import types

class _TaggedUnionMeta(ShapeCastable, type):
    def __new__(metacls, name, bases, namespace):
        if "__annotations__" not in namespace:
            # This is a base class without its own layout. It is not shape-castable, and cannot
            # be instantiated. It can be used to share behavior.
            return type.__new__(metacls, name, bases, namespace)
        elif all(not hasattr(base, "_TaggedUnionMeta__layout") for base in bases):
            # This is a leaf class with its own layout. It is shape-castable and can
            # be instantiated. It can also be subclassed, and used to share layout and behavior.
            layout  = dict()
            default = dict()
            for field_name in {**namespace["__annotations__"]}:
                try:
                    Shape.cast(namespace["__annotations__"][field_name])
                except TypeError:
                    # Not a shape-castable annotation; leave as-is.
                    continue
                layout[field_name] = namespace["__annotations__"].pop(field_name)
                if field_name in namespace:
                    default[field_name] = namespace.pop(field_name)
            cls = type.__new__(metacls, name, bases, namespace)
            if len(default) > 1:
                raise ValueError("Initial value for at most one field can be provided for "
                                    "a union class (specified: {})"
                                    .format(", ".join(default.keys())))


            # TODO(robin): maybe switch back to functional API when it supports shape, or when it supports formatting in structs without shape0
            # amaranth.lib.enum.Enum(name + "Tag", {key: i for i, key in enumerate(layout.keys())})

            def populate(ns):
                for i, key in enumerate(layout.keys()):
                    ns[key] = i
            tag_layout = types.new_class(name=name + "Tag", bases=(amaranth.lib.enum.Enum,), kwds={"shape":range(len(layout.keys()))}, exec_body=populate)
            cls.__tag_layout = tag_layout
            cls.__field_layouts = layout
            cls.__layout  = StructLayout({
                "tag": cls.__tag_layout,
                "data": UnionLayout(layout)
            })
            cls.__default = default
            return cls
        else:
            # This is a class that has a base class with a layout and annotations. Such a class
            # is not well-formed.
            raise TypeError("Aggregate class '{}' must either inherit or specify a layout, "
                            "not both"
                            .format(name))

    def as_shape(cls):
        return cls.__layout

    def __call__(cls, target):
        # This method exists to pass the override check done by ShapeCastable.
        return super().__call__(cls, target)

    def const(cls, init):
        if isinstance(init, DataConst):
            if Layout.cast(init.shape()) != Layout.cast(cls.__layout):
                raise ValueError(f"Const layout {init.shape()!r} differs from shape layout "
                                 f"{cls.__layout!r}")
            return init
        # print(init, isinstance(init, Const), type(init))
        if init is not None and len(init) > 1:
            raise ValueError("Initializer for at most one field can be provided for "
                                "a union class (specified: {})"
                                .format(", ".join(init.keys())))
            return cls.as_shape().const(init or cls.__default)
        else:
            fields = cls.__default.copy()
            fields.update(init or {})
            return cls.as_shape().const(fields)

    def from_bits(cls, bits):
        return cls.as_shape().from_bits(bits)

    # TODO(robin): this is extremely hacky, but works for now
    def format(cls, value, format_spec):
        def str_val(s):
            s = s.encode()
            return Const(int.from_bytes(s, "little"), len(s) * 8)

        tags = cls.__tag_layout.__members__
        member_formats = {field: Format("{}", value.data[field]) for field in cls.__field_layouts.keys()}

        total_format = Format("{}", value.tag)
        scrub_out = 0
        for key, fmt in member_formats.items():
            tag_value = tags[key]
            is_selected = value.tag == tag_value
            new_fmt = Format("")
            for chunk in fmt._chunks:
                if isinstance(chunk, str):
                    new_fmt += Format("{:s}", Mux(is_selected, str_val(chunk), str_val("")))
                else:
                    chunk_value, spec = chunk
                    zero_width = len(format(0, spec))
                    new_fmt += Format("{:" + spec + "}", Mux(is_selected, chunk_value, 0))
                    new_fmt += Format("{:s}", Mux(is_selected, str_val(""), str_val("\x08" * zero_width)))
                    scrub_out = max(scrub_out, zero_width)
            total_format += new_fmt
        return total_format + Format(" " * scrub_out)

    def _value_repr(cls, value):
        return cls.__layout._value_repr(value)

    def __getattr__(cls, name):
        try:
            return type.__getattribute__(cls, name)
        except AttributeError as e:
            tag_layout =  type.__getattribute__(cls, "_TaggedUnionMeta__tag_layout")
            if name in tag_layout.__members__:
                ret = tag_layout[name]
                return ret
            else:
                raise e

class TaggedUnion(View, metaclass=_TaggedUnionMeta):
    _match_stack = []

    @classmethod
    @contextlib.contextmanager
    def Match(cls, m: Module, signal):
        with m.Switch(signal.tag):
            cls._match_stack.append((m, signal, set(), False))
            yield
            m, signal, treated, have_default = cls._match_stack.pop()
            tag_values = signal.shape()._TaggedUnionMeta__tag_layout.__members__
            untreated = set(tag_values.keys()) - treated
            if len(untreated) > 0 and not have_default:
                raise KeyError(f"No default clause and missing match case for {untreated}")

    @classmethod
    @contextlib.contextmanager
    def Case(cls, kind):
        m, signal, treated, have_default = cls._match_stack[-1]

        tag_enum = signal.shape()._TaggedUnionMeta__tag_layout
        if not isinstance(kind, tag_enum):
            raise KeyError(f"Tried to match a {str(signal.__class__)} with a tag of type {type(kind)} which does not match")
        if kind.name in treated:
            raise KeyError(f"Duplicated match case for {kind} detected")
        treated.add(kind.name)

        with m.Case(kind):
            yield getattr(signal.data, kind.name)

    @classmethod
    @contextlib.contextmanager
    def Default(cls):
        m, signal, treated, have_default = cls._match_stack[-1]
        cls._match_stack[-1] = (m, signal, treated, True)
        with m.Default():
            yield

if __name__ == "__main__":
    class StructA(data.Struct):
        value_a: 32

    class StructB(data.Struct):
        value_b: 16

    class SomeTaggedUnion(TaggedUnion):
        a: StructA
        b: StructB
        c: 17

    class SomeOtherTaggedUnion(TaggedUnion):
        a: StructA
        b: StructB
        c: 17


    theSignal = Signal(SomeTaggedUnion)
    output = Signal(32)

    m = Module()
    with TaggedUnion.Match(m, theSignal):
        with TaggedUnion.Case(SomeTaggedUnion.a) as data:
            m.d.sync += output.eq(data.value_a)
        with TaggedUnion.Case(SomeTaggedUnion.b) as data:
            m.d.sync += output.eq(data.value_b)
        with TaggedUnion.Case(SomeOtherTaggedUnion.c) as data:
            m.d.sync += output.eq(data.value_b)
        with TaggedUnion.Default():
            m.d.sync += output.eq(theSignal.tag)



    print(convert(m, ports=(output, theSignal.as_value())))
