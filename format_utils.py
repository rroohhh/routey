#!/usr/bin/env python3

from amaranth import *
from amaranth.hdl._dsl import SwitchValue, Slice, Operator, SignalDict
from amaranth.hdl._ast import _StatementList, Assign, Part, Concat, Property, Switch
import json

def formatter_for(signal):
    class _FormatEncoder(json.JSONEncoder):
        def default(self, obj):
            match obj:
                case Format():
                    return obj._chunks
                case SwitchValue():
                    return {"type": "SwitchValue", "test": obj.test, "cases": obj.cases}
                case Slice():
                    return {"type": "Slice", "start": obj.start, "stop": obj.stop, "value": obj.value}
                case Signal():
                    assert obj is Value.cast(signal)
                    assert obj.shape().signed == False
                    return {"type": "Signal"}
                case Const():
                    assert obj.shape().signed == False
                    return {"type": "Const", "value": hex(obj.value)}
                case Operator():
                    return {"type": "Operator", "operator": obj.operator, "operands": obj.operands}
                case _:
                    return super().default(obj)
    fmt = Format("") + signal._format
    if len(chunks := fmt._chunks) == 1 and chunks[0][0] is signal and chunks[0][1] == '':
        return None
    return json.dumps(fmt._chunks, cls=_FormatEncoder)

class _Visitor:
    def __init__(self):
        self.signals = SignalDict()

    def visit_frag(self, m):
        for stmt in m.statements.values():
            self.visit_stmt(stmt)

        for frag, _, _ in m.subfragments:
            self.visit_frag(frag)

    def visit_stmt(self, stmt):
        if isinstance(stmt, _StatementList):
            for s in stmt:
                self.visit_stmt(s)
        elif isinstance(stmt, Assign):
            self.visit_sentinel(stmt.lhs)
            self.visit_sentinel(stmt.rhs)
        elif isinstance(stmt, Print):
            for chunk in stmt.message._chunks:
                if not isinstance(chunk, str):
                    obj, format_spec = chunk
                    self.visit_sentinel(obj)
        elif isinstance(stmt, Property):
            self.visit_sentinel(stmt.test)
            if stmt.message is not None:
                for chunk in stmt.message._chunks:
                    if not isinstance(chunk, str):
                        obj, format_spec = chunk
                        self.visit_sentinel(obj)
        elif isinstance(stmt, Switch):
            self.visit_sentinel(stmt.test)
            for _patterns, stmts, _src_loc in stmt.cases:
                self.visit_stmt(stmts)

    def visit_sentinel(self, value):
        if isinstance(value, Operator) and value.operator in ("u", "s"):
            self.visit_sentinel(value.operands[0])
        elif isinstance(value, (Signal)):
            fmt = formatter_for(value)
            if fmt is not None:
                value.attrs["formatter"] = fmt
        elif isinstance(value, Slice):
            self.visit_sentinel(value.value)
        elif isinstance(value, Part):
            self.visit_sentinel(value.value)
            self.visit_sentinel(value.offset)
        elif isinstance(value, Concat):
            for part in value.parts:
                self.visit_sentinel(part)
        elif isinstance(value, SwitchValue):
            self.visit_sentinel(value.test)
            for _patterns, elem in value.cases:
                self.visit_sentinel(elem)

def add_formatting_attrs(m: Module):
    frag = Fragment.get(m, None)

    _Visitor().visit_frag(frag)

    return frag
