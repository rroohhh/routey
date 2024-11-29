#!/usr/bin/env python3

import enum
from inspect import isclass
from contextlib import contextmanager
from amaranth import Shape, ShapeCastable, Signal, Format
from amaranth.hdl._ast import SwitchValue, Slice, Const, Operator
from amaranth.lib import data
from .tagged_union import TaggedUnion
from .wrap import EqSet, type_to_name, indent, pascal_case_to_snake_case


def _eval_matches(test, patterns):
    if patterns is None:
        return "True"
    tests = []

    for pattern in patterns:
        if isinstance(pattern, str):
            mask  = bin(int("".join("0" if b == "-" else "1" for b in pattern), 2))
            value = bin(int("".join("0" if b == "-" else  b  for b in pattern), 2))


            tests.append(f"{value} == ({mask} & {test})")
        else:
            tests.append(f"{pattern} == test")

    return " or ".join(tests)

def _eval_matches_match(test, patterns):
    if patterns is None:
        return "_"
    tests = []

    for pattern in patterns:
        assert "-" not in pattern
        if isinstance(pattern, str):
            tests.append(f"{hex(int(pattern, 2))}")
        else:
            tests.append(f"{hex(pattern)}")

    return " | ".join(tests)

class Emitter():
    def __init__(self):
        self._buffer = []
        self._suffix = 0
        self._level  = 0
        self._cache = {}

    def append(self, code):
        self._buffer.append("    " * self._level)
        self._buffer.append(code)
        self._buffer.append("\n")

    @contextmanager
    def indent(self):
        self._level += 1
        yield
        self._level -= 1

    def gen_var(self, prefix):
        name = f"{prefix}_{self._suffix}"
        self._suffix += 1
        return name


    def add_var(self, prefix, value):
        if value in self._cache:
            return self._cache[value]
        else:
            res_var = self.gen_var(prefix)
            self.append(f"{res_var} = {value}")
            self._cache[value] = res_var
            return res_var

def assert_int(v):
    if v == "the_signal":
        return v
    else:
        return f"assert_int({v})"

def eval_value(value, emitter):
    match value:
        case SwitchValue():
            test = assert_int(eval_value(value.test, emitter))

            res_var = emitter.gen_var("switch_var")

            vals = []
            for _, val in value.cases:
                vals.append(eval_value(val, emitter))

            emitter.append(f'match {test}:')
            with emitter.indent():
                for val, (patterns, _) in zip(vals, value.cases):
                    emitter.append("case " + _eval_matches_match(test, patterns) + ":")
                    with emitter.indent():
                        emitter.append(f"{res_var} = {val}")
            return res_var

            # prefix = "if "
            # for val, (patterns, _) in zip(vals, value.cases):
            #     emitter.append(prefix + _eval_matches(test, patterns) + ":")
            #     with emitter.indent():
            #         emitter.append(f"{res_var} = {val}")
            #     prefix = "elif "
            # return res_var
        case Operator():
            assert len(value.operands) == 2

            match value.operator:
                case "==": return emitter.add_var("op_eq", "(" + eval_value(value.operands[0], emitter) + " == " + eval_value(value.operands[1], emitter) + ")")
                case _: assert False
        case Const():
            try:
                v = value.value
                msg = bytearray()
                while v:
                    byte = v & 0xff
                    v >>= 8
                    if byte:
                        msg.append(byte)
                msg = msg.decode()
                # print(msg, all(c.isascii() for c in msg))
                if msg.isprintable() and len(msg) > 0:
                    return repr(msg)
            except:
                ...

            return str(value.value)
        case Slice():
            start = 0
            l = 1<<64
            while True:
                # print(value, type(value))
                if isinstance(value, Slice):
                    start += value.start
                    l = min(l, value.stop - value.start)
                    # print(l)
                    value = value.value
                else:
                    break

            v = assert_int(eval_value(value, emitter))
            if start != 0:
                return emitter.add_var('sliced', f"({v} >> {start}) & {hex((1<<l) - 1)}")
            else:
                return emitter.add_var('sliced', f"{v} & {hex((1<<l) - 1)}")
        case Signal():
            return "the_value"
        case _: assert False, f"{type(value)}"

def gen_translators(types):
    defined_trans = EqSet()
    defined_trans_names = EqSet()

    def gen_type(ty, name=None):
        sig = Signal(ty)
        # HACK(robin): this relies on amaranth internals

        emitter = Emitter()
        result_var = emitter.gen_var("fmt_result")
        name = ty.__name__
        emitter.append(f"class {name}(surfer.BasicTranslator):")
        with emitter.indent():
            emitter.append(f"name = '{name}'")
            emitter.append(f"@staticmethod")
            emitter.append(f"def basic_translate(num_bits: int, value: str):")
            with emitter.indent():
                emitter.append("the_value = int(value)")
                emitter.append(f"{result_var} = ''")

                for chunk in Format("{}", sig)._chunks:
                    if isinstance(chunk, str):
                        emitter.append(f"{result_var} += '{chunk}'")
                    else:
                        value, spec = chunk

                        res_var = eval_value(value, emitter)
                        if spec == "s":
                            emitter.append(f"{result_var} += int_to_str({res_var})")
                        else:
                            emitter.append(f"{result_var} += format({res_var}, '{spec}')")
                emitter.append(f"while '\\x08' in {result_var}: {result_var} = re.sub('[^\\x08]\\x08', '', {result_var})")
                emitter.append(f"return {result_var}, surfer.ValueKind.Normal()")

        defined_trans.add("".join(emitter._buffer))
        defined_trans_names.add(name)

    for ty in types:
        gen_type(ty)
    return defined_trans, defined_trans_names

if __name__ == "__main__":
    import sys, importlib

    types = []
    for name in sys.argv[1:]:
        py_module_name, py_class_name = name.rsplit(".", 1)
        py_module = importlib.import_module(py_module_name)
        py_class = py_module.__dict__[py_class_name]
        if not isinstance(py_class, type) or not isinstance(py_class, ShapeCastable):
            raise TypeError("{}.{} is not a class inheriting from ShapeCastable"
                            .format(py_module_name, py_class_name))
        types.append(py_class)

    defs, names = gen_translators(types)
    print("""#!/usr/bin/env python
try:
    import surfer
except:
    class surfer:
        class BasicTranslator:
            ...

        class ValueKind:
            class Normal:
                ...
""")
    print("import re")
    print(f"translators = [{','.join(repr(name) for name in names)}]")
    print("""
def assert_int(v):
    if type(v) == int:
        return v
    if type(v) == bool:
        return 1 if v else 0
    return int.from_bytes(v.encode(), "little")
def int_to_str(v):
    if v == 0:
        return ''
    if type(v) == str:
        return v
    len = (v.bit_length() + 7) // 8
    return v.to_bytes(len, "little").decode()
""")
    print("\n\n".join(defs))
    print(f"""
if __name__ == "__main__":
    import sys
    while (line := sys.stdin.readline()):
        v = int(line, 16)
        sys.stdout.write({next(iter(names))}.basic_translate(0, v)[0] + "\\n")
        sys.stdout.flush()

    sys.exit(0)
""")
