"""Typed product operations erased into existing first-order relation nodes.

Products are source-stage values. Selection and equality visit their leaves in
declaration order, so these forms have the same residual graph as explicit
fieldwise operations and do not introduce a product witness or AIR component.
"""

from __future__ import annotations

from typing import Any

from s31_stdlib import Builder, Type, TypeErrorS31, Value
from language.builtin_types import BIT, SELECTABLE_KINDS
from language.syntax import RecordType, StaticRecord, StaticTuple, TupleType


def selectable_type(typ: object) -> bool:
    """Whether every leaf has a native, total constrained selector."""
    if isinstance(typ, Type):
        return typ == BIT or typ.kind in SELECTABLE_KINDS
    if isinstance(typ, TupleType):
        return all(selectable_type(item) for item in typ.elements)
    if isinstance(typ, RecordType):
        return all(selectable_type(item) for _, item in typ.fields)
    return False


def assertable_types(lhs: object, rhs: object) -> bool:
    """Match the primitive assertion rule, including scalar bit/M31 equality."""
    if isinstance(lhs, Type) and isinstance(rhs, Type):
        return lhs == rhs or ({lhs.kind, rhs.kind} == {"bit", "m31"}
                              and lhs.length == rhs.length == 1)
    if isinstance(lhs, TupleType) and isinstance(rhs, TupleType):
        return lhs == rhs and all(
            assertable_types(left, right) for left, right in zip(lhs.elements, rhs.elements))
    if isinstance(lhs, RecordType) and isinstance(rhs, RecordType):
        return lhs == rhs and all(assertable_types(left, right)
                                  for (_, left), (_, right) in zip(lhs.fields, rhs.fields))
    return False


def select_product(builder: Builder, condition: Value, on_false: Any, on_true: Any,
                   *, span: dict[str, int]) -> Value | StaticTuple | StaticRecord:
    """Select first-order leaves without allocating any product relation node."""
    if isinstance(on_false, Value) and isinstance(on_true, Value):
        if on_true.typ != on_false.typ:
            raise TypeErrorS31("if branches must have the same first-order circuit type")
        if on_true.typ == BIT:
            return builder.boolean("bool_select", on_false, on_true, condition, span=span)
        return builder.select(condition, on_false, on_true, span=span)
    if isinstance(on_false, StaticTuple) and isinstance(on_true, StaticTuple):
        if on_false.signature != on_true.signature:
            raise TypeErrorS31("if branches must have the same product type")
        return StaticTuple(on_true.signature, tuple(
            select_product(builder, condition, false, true, span=span)
            for false, true in zip(on_false.elements, on_true.elements)))
    if isinstance(on_false, StaticRecord) and isinstance(on_true, StaticRecord):
        if on_false.signature != on_true.signature:
            raise TypeErrorS31("if branches must have the same nominal struct type")
        return StaticRecord(on_true.signature, tuple(
            select_product(builder, condition, false, true, span=span)
            for false, true in zip(on_false.elements, on_true.elements)))
    raise TypeErrorS31("if result must contain only selectable circuit leaves")


def assert_product_equal(builder: Builder, lhs: Any, rhs: Any) -> None:
    """Expand product equality to the existing per-leaf AIR assertions."""
    if isinstance(lhs, Value) and isinstance(rhs, Value):
        builder.assert_equal(lhs, rhs)
        return
    if isinstance(lhs, StaticTuple) and isinstance(rhs, StaticTuple):
        if lhs.signature != rhs.signature:
            raise TypeErrorS31("assert_eq requires two values of the same product type")
        for left, right in zip(lhs.elements, rhs.elements):
            assert_product_equal(builder, left, right)
        return
    if isinstance(lhs, StaticRecord) and isinstance(rhs, StaticRecord):
        if lhs.signature != rhs.signature:
            raise TypeErrorS31("assert_eq requires two values of the same nominal struct type")
        for left, right in zip(lhs.elements, rhs.elements):
            assert_product_equal(builder, left, right)
        return
    raise TypeErrorS31("assert_eq requires matching first-order or product values")
