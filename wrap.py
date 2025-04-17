import re
from amaranth import Shape
from amaranth.lib import data

class EqSet:
    def __init__(self):
        self._data = []

    def add(self, item):
        if item not in self._data:
            self._data.append(item)
            return len(self._data) - 1
        else:
            return self._data.index(item)

    def __iter__(self):
        return self._data.__iter__()


def pascal_case_to_snake_case(name: str):
    return re.sub(r"[A-Z]+", lambda m: "_" + m.group(0).lower(), name).removeprefix("_")

def path_to_name(path: list):
    return "_".join(path)

def type_to_name(ty, prefix="", field_name=""):
    if isinstance(ty, range) or isinstance(ty, int) or isinstance(ty, Shape):
        ty = Shape.cast(ty)
        if isinstance(ty, Shape):
            assert not ty.signed
            ty = ty.width

        if ty > 1:
            return f"logic [{ty - 1}: 0]"
        else:
            return "logic"
    else:
        if hasattr(ty, "__name__"):
            return pascal_case_to_snake_case(ty.__name__)
        elif isinstance(ty, data.StructLayout):
            return pascal_case_to_snake_case(ty.__class__.__name__.removesuffix("Layout"))
        else:
            name = pascal_case_to_snake_case(field_name)
            if len(prefix) > 0:
                name = prefix + "_" + name

            assert len(prefix) + len(field_name) > 0
            return name

indent = " " * 4
