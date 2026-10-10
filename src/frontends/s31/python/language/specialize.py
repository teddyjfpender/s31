"""Specialize static functions into the first-order relation builder."""

from __future__ import annotations

from typing import Any

import s31_mathlib as mathlib
from s31_stdlib import Builder, INT_TYPES, P, StaticGroup, StepState, Type, TypeErrorS31, Value
from language.builtins import (INT_BINARY_CALLS, INT_CAST_CALLS, INT_COMPARE_CALLS,
                               MAX_CALL_DEPTH, STANDARD_ALIASES)
from language.syntax import Circuit, Expr, Function, FunctionType, SourceError, StaticClosure, StaticNamedFunction, StaticTuple, Statement, TupleType


class Compiler:
    def __init__(self, functions: dict[str, Function], circuit: Circuit, filename: str) -> None:
        self.functions = functions
        self.circuit = circuit
        self.filename = filename
        self.builder = Builder(circuit.name)
        self.call_stack: list[str] = []
        self.inline_count = 0
        self.source_names = {name for name, _, _ in circuit.params}
        self.source_names.update(statement.name for statement in circuit.statements
                                 if statement.kind == "let")
        self.builder.reserved_names = self.source_names

    def located(self, expr: Expr, exc: Exception) -> SourceError:
        return SourceError(f"{self.filename}:{expr.token.line}:{expr.token.column}: {exc}")

    @staticmethod
    def span(expr: Expr) -> dict[str, int]:
        return {"line": expr.token.line, "column": expr.token.column}

    def expect_value(self, thing: Any, expr: Expr) -> Value:
        if not isinstance(thing, Value):
            raise self.located(expr, "expected a circuit value")
        return thing

    @staticmethod
    def source_type(thing: Any) -> Type | FunctionType | TupleType | None:
        if isinstance(thing, (Value, StepState)):
            return thing.typ
        if isinstance(thing, (StaticClosure, StaticNamedFunction)):
            return thing.signature
        if isinstance(thing, StaticTuple):
            return thing.signature
        return None

    def eval_block(self, statements: tuple[Statement, ...], body: Expr,
                   env: dict[str, Any], wanted: str | None = None,
                   inline_prefix: str = "", allow_assert: bool = True) -> Any:
        local = env.copy()
        for statement_index, statement in enumerate(statements):
            if statement.kind == "let":
                if statement.name in local:
                    raise self.located(statement.args[0], f"duplicate local name {statement.name}")
                if inline_prefix and wanted is not None and body.kind == "name" and body.value == statement.name:
                    target = wanted
                elif inline_prefix:
                    target = f"{inline_prefix}{statement_index}"
                else:
                    target = statement.name
                value = self.eval_expr(statement.args[0], local, wanted=target)
                if not isinstance(value, (Value, StaticGroup, StaticClosure, StaticNamedFunction, StaticTuple, int)):
                    raise self.located(statement.args[0], "let requires a circuit or static value")
                local[statement.name] = value
            else:
                if not allow_assert:
                    raise self.located(statement.args[0], "pure functions cannot contain assertions")
                lhs = self.expect_value(self.eval_expr(statement.args[0], local), statement.args[0])
                rhs = self.expect_value(self.eval_expr(statement.args[1], local), statement.args[1])
                try:
                    self.builder.assert_equal(lhs, rhs)
                except TypeErrorS31 as exc:
                    raise self.located(statement.args[0], exc) from exc
        return self.eval_expr(body, local, wanted=wanted)

    def call_function(self, name: str, args: tuple[Any, ...], wanted: str | None, expr: Expr) -> Any:
        fn = self.functions[name]
        if len(args) != len(fn.params):
            raise self.located(expr, f"{name} expects {len(fn.params)} arguments")
        if name in self.call_stack or len(self.call_stack) >= MAX_CALL_DEPTH:
            raise self.located(expr, "recursive or excessively deep function expansion")
        env: dict[str, Any] = {}
        for (parameter, typ), arg in zip(fn.params, args):
            if self.source_type(arg) != typ:
                raise self.located(expr, f"{name} argument {parameter} expects {typ}")
            env[parameter] = arg
        self.call_stack.append(name)
        while True:
            self.inline_count += 1
            prefix = f"_s31_i{self.inline_count}_"
            generated = {f"{prefix}{index}" for index, statement in enumerate(fn.statements)
                         if statement.kind == "let"}
            if not generated.intersection(self.source_names | self.builder.used_names):
                break
        try:
            result = self.eval_block(fn.statements, fn.body, env, wanted=wanted,
                                     inline_prefix=prefix, allow_assert=False)
        finally:
            self.call_stack.pop()
        if isinstance(fn.result, Type):
            self.expect_value(result, fn.body)
        if self.source_type(result) != fn.result:
            raise self.located(expr, f"{name} result does not match its declared type")
        return result

    def call_closure(self, closure: StaticClosure, args: tuple[Any, ...],
                     wanted: str | None, expr: Expr) -> Any:
        if len(args) != len(closure.signature.params):
            raise self.located(expr, f"function value expects {len(closure.signature.params)} arguments")
        for index, (arg, typ) in enumerate(zip(args, closure.signature.params)):
            if self.source_type(arg) != typ:
                raise self.located(expr, f"function value argument {index + 1} expects {typ}")
        key = f"lambda:{id(closure)}"
        if key in self.call_stack or len(self.call_stack) >= MAX_CALL_DEPTH:
            raise self.located(expr, "recursive or excessively deep function expansion")
        local = closure.captured.copy()
        local.update(zip(closure.names, args))
        self.call_stack.append(key)
        try:
            result = self.eval_expr(closure.body, local, wanted=wanted)
        finally:
            self.call_stack.pop()
        if self.source_type(result) != closure.signature.result:
            raise self.located(expr, "function value result does not match its declared type")
        return result

    def eval_expr(self, expr: Expr, env: dict[str, Any], wanted: str | None = None) -> Any:
        try:
            if expr.kind == "let":
                bound = self.eval_expr(expr.args[0], env)
                if not isinstance(bound, (Value, StaticGroup, StaticClosure, StaticNamedFunction, StaticTuple, int)):
                    raise TypeErrorS31("let requires a circuit or static value")
                local = env.copy()
                local[expr.value] = bound
                return self.eval_expr(expr.args[1], local, wanted=wanted)
            if expr.kind == "lambda":
                assert expr.result_type is not None
                signature = FunctionType(tuple(typ for _, typ in expr.params), expr.result_type)
                return StaticClosure(signature, tuple(name for name, _ in expr.params),
                                     expr.args[0], env.copy())
            if expr.kind == "name":
                if expr.value in env:
                    return env[expr.value]
                if expr.value in self.functions:
                    fn = self.functions[expr.value]
                    return StaticNamedFunction(expr.value, FunctionType(
                        tuple(typ for _, typ in fn.params), fn.result))
                raise TypeErrorS31(f"unknown value {expr.value}")
            if expr.kind == "number":
                raise TypeErrorS31("field literals require the _m31 suffix")
            if expr.kind == "field":
                number = int(expr.value[:-4])
                if not 0 <= number < P:
                    raise TypeErrorS31("m31 literal must be canonical")
                return number
            if expr.kind == "array":
                values = tuple(self.eval_expr(item, env) for item in expr.args)
                if not values:
                    raise TypeErrorS31("static array cannot be empty")
                if not all(isinstance(value, (Value, StaticGroup)) for value in values):
                    raise TypeErrorS31("static array elements must be circuit values or static arrays")
                return StaticGroup(values)
            if expr.kind == "tuple":
                elements = tuple(self.eval_expr(item, env) for item in expr.args)
                types = tuple(self.source_type(item) for item in elements)
                if not all(isinstance(typ, (Type, FunctionType, TupleType)) for typ in types):
                    raise TypeErrorS31("tuple elements need declared source types")
                return StaticTuple(TupleType(types), elements)
            if expr.kind == "project":
                source = self.eval_expr(expr.args[0], env)
                index = int(expr.value)
                if not isinstance(source, StaticTuple) or index >= len(source.elements):
                    raise TypeErrorS31("tuple projection index is out of range")
                return source.elements[index]
            if expr.kind == "if":
                condition = self.expect_value(self.eval_expr(expr.args[0], env), expr.args[0])
                on_true = self.expect_value(self.eval_expr(expr.args[1], env), expr.args[1])
                on_false = self.expect_value(self.eval_expr(expr.args[2], env), expr.args[2])
                if on_true.typ == Type("bit", 1):
                    return self.builder.boolean("bool_select", on_false, on_true, condition,
                                                wanted=wanted, span=self.span(expr))
                return self.builder.select(condition, on_false, on_true,
                                           wanted=wanted, span=self.span(expr))
            if expr.kind == "binary":
                lhs = self.expect_value(self.eval_expr(expr.args[0], env), expr.args[0])
                rhs = self.expect_value(self.eval_expr(expr.args[1], env), expr.args[1])
                return self.builder.binary("add" if expr.value == "+" else "mul", lhs, rhs,
                                           wanted=wanted, span=self.span(expr))
            if expr.kind == "apply":
                callee = self.eval_expr(expr.args[0], env)
                args = tuple(self.eval_expr(arg, env) for arg in expr.args[1:])
                if isinstance(callee, StaticClosure):
                    return self.call_closure(callee, args, wanted, expr)
                if isinstance(callee, StaticNamedFunction):
                    return self.call_function(callee.name, args, wanted, expr)
                raise TypeErrorS31("applied expression must be a function value")
            if expr.kind != "call":
                raise TypeErrorS31("invalid expression")
            if expr.value in env:
                callee = env[expr.value]
                if not isinstance(callee, (StaticClosure, StaticNamedFunction)):
                    raise TypeErrorS31(f"cannot call non-function value {expr.value}")
                if expr.generic is not None:
                    raise TypeErrorS31("function values do not accept static parameters")
                args = tuple(self.eval_expr(item, env) for item in expr.args)
                if isinstance(callee, StaticNamedFunction):
                    return self.call_function(callee.name, args, wanted, expr)
                return self.call_closure(callee, args, wanted, expr)
            name = STANDARD_ALIASES.get(expr.value, expr.value)
            if name in INT_BINARY_CALLS or name in INT_COMPARE_CALLS or name in INT_CAST_CALLS or name == "std::int::limbs":
                if expr.generic is not None:
                    raise TypeErrorS31(f"{name} does not accept a static parameter")
                arity = 2 if name in INT_BINARY_CALLS or name in INT_COMPARE_CALLS else 1
                if len(expr.args) != arity:
                    raise TypeErrorS31(f"{name} expects {arity} arguments")
                values = tuple(self.expect_value(self.eval_expr(arg, env), arg) for arg in expr.args)
                if name in INT_BINARY_CALLS:
                    return self.builder.int_binary(INT_BINARY_CALLS[name], *values,
                                                   wanted=wanted, span=self.span(expr))
                if name in INT_COMPARE_CALLS:
                    lhs, rhs = values
                    if name == "std::int::ge":
                        return self.builder.int_binary("int_le", rhs, lhs, wanted=wanted, span=self.span(expr))
                    if name in {"std::int::lt", "std::int::gt"}:
                        left, right = (rhs, lhs) if name.endswith("lt") else (lhs, rhs)
                        le = self.builder.int_binary("int_le", left, right, span=self.span(expr))
                        return self.builder.boolean("bool_not", le, wanted=wanted, span=self.span(expr))
                    le = self.builder.int_binary("int_le", lhs, rhs, span=self.span(expr))
                    ge = self.builder.int_binary("int_le", rhs, lhs, span=self.span(expr))
                    equal = self.builder.boolean("bool_and", le, ge,
                                                 wanted=wanted if name.endswith("eq") else None,
                                                 span=self.span(expr))
                    return (equal if name.endswith("eq") else
                            self.builder.boolean("bool_not", equal, wanted=wanted, span=self.span(expr)))
                if name == "std::int::limbs":
                    return self.builder.int_limbs(values[0])
                if name.startswith("std::int::from_limbs_"):
                    return self.builder.int_from_limbs(values[0], name.removeprefix("std::int::from_limbs_"),
                                                       wanted=wanted, span=self.span(expr))
                if name.startswith("std::int::cast_checked_"):
                    return self.builder.int_cast_checked(values[0], name.removeprefix("std::int::cast_checked_"),
                                                         wanted=wanted, span=self.span(expr))
                return self.builder.int_reinterpret(values[0], name.removeprefix("std::int::reinterpret_"),
                                                    wanted=wanted, span=self.span(expr))
            if name == "std::array::get":
                if expr.generic is None or len(expr.args) != 1:
                    raise TypeErrorS31("std::array::get<K>(array) expected")
                value = self.eval_expr(expr.args[0], env)
                if not isinstance(value, (Value, StaticGroup)):
                    raise TypeErrorS31("std::array::get requires an array")
                return self.builder.array_get(value, expr.generic, wanted=wanted, span=self.span(expr))
            if name == "std::array::concat":
                if expr.generic is not None or len(expr.args) != 2:
                    raise TypeErrorS31("std::array::concat(a,b) expected")
                values = tuple(self.eval_expr(arg, env) for arg in expr.args)
                if not all(isinstance(value, (Value, StaticGroup)) for value in values):
                    raise TypeErrorS31("std::array::concat requires arrays")
                return self.builder.array_concat(*values, wanted=wanted, span=self.span(expr))
            if name in {"std::array::take", "std::array::drop", "std::array::reshape"}:
                if expr.generic is None or len(expr.args) != 1:
                    raise TypeErrorS31(f"{name}<K>(array) expected")
                group = self.eval_expr(expr.args[0], env)
                operation = {"std::array::take": self.builder.array_take,
                             "std::array::drop": self.builder.array_drop,
                             "std::array::reshape": self.builder.array_reshape}[name]
                if name == "std::array::reshape":
                    return operation(group, expr.generic, span=self.span(expr))
                return operation(group, expr.generic, wanted=wanted,
                                 span=self.span(expr))
            if name == "std::array::flatten":
                if expr.generic is not None or len(expr.args) != 1:
                    raise TypeErrorS31("std::array::flatten(matrix) expected")
                return self.builder.array_flatten(self.eval_expr(expr.args[0], env),
                                                  wanted=wanted, span=self.span(expr))
            if name in mathlib.BUILTINS:
                if name in {"std::math::sum_u256", "std::math::sum_u256_checked"}:
                    if expr.generic is not None or len(expr.args) != 1:
                        raise TypeErrorS31(f"{name} expects one static array")
                    group = self.eval_expr(expr.args[0], env)
                    return mathlib.sum_u256_static(
                        self.builder, group, checked=name.endswith("_checked"),
                        wanted=wanted, span=self.span(expr))
                if name == "std::math::pow":
                    if expr.generic is None or len(expr.args) != 1:
                        raise TypeErrorS31("std::math::pow<N>(value) expected")
                    value = self.expect_value(self.eval_expr(expr.args[0], env), expr.args[0])
                    return mathlib.pow_static(self.builder, value, expr.generic,
                                              wanted=wanted, span=self.span(expr))
                if expr.generic is not None:
                    raise TypeErrorS31(f"{name} does not accept a static parameter")
                if name == "std::math::matvec":
                    if len(expr.args) != 2:
                        raise TypeErrorS31("std::math::matvec expects a matrix and vector")
                    matrix, vector = (self.eval_expr(arg, env) for arg in expr.args)
                    return mathlib.matvec(self.builder, matrix, vector, span=self.span(expr))
                if name == "std::math::matmul":
                    if len(expr.args) != 2:
                        raise TypeErrorS31("std::math::matmul expects two matrices")
                    lhs, rhs = (self.eval_expr(arg, env) for arg in expr.args)
                    return mathlib.matmul(self.builder, lhs, rhs, span=self.span(expr))
                if name in {"std::math::sum", "std::math::dot", "std::math::poly_eval"}:
                    args = tuple(self.eval_expr(arg, env) for arg in expr.args)
                    arity = 1 if name == "std::math::sum" else 2
                    if len(args) != arity:
                        raise TypeErrorS31(f"{name} expects {arity} arguments")
                    if name == "std::math::sum":
                        return mathlib.sum_static(self.builder, args[0], wanted=wanted,
                                                  span=self.span(expr))
                    if name == "std::math::dot":
                        return mathlib.dot_static(self.builder, args[0], args[1],
                                                  wanted=wanted, span=self.span(expr))
                    return mathlib.poly_eval(self.builder, self.expect_value(args[0], expr), args[1],
                                             wanted=wanted, span=self.span(expr))
                if name in {"std::math::sum_lanes", "std::math::dot_lanes"}:
                    arity = 1 if name == "std::math::sum_lanes" else 2
                    if len(expr.args) != arity:
                        raise TypeErrorS31(f"{name} expects {arity} arguments")
                    values = tuple(self.expect_value(self.eval_expr(arg, env), arg)
                                   for arg in expr.args)
                    operation = (mathlib.sum_lanes if arity == 1 else mathlib.dot_lanes)
                    return operation(self.builder, *values, wanted=wanted, span=self.span(expr))
                values = tuple(self.expect_value(self.eval_expr(arg, env), arg) for arg in expr.args)
                arity = 2 if name in {"std::math::sub", "std::math::div", "std::math::add_u256", "std::math::add_u256_checked", "std::math::sub_u256", "std::math::sub_u256_checked", "std::math::le_u256", "std::math::lt_u256", "std::math::gt_u256", "std::math::ge_u256", "std::math::eq_u256", "std::math::ne_u256", "std::math::min_u256", "std::math::max_u256"} else 1
                if len(values) != arity:
                    raise TypeErrorS31(f"{name} expects {arity} arguments")
                operation = {"std::math::neg": mathlib.neg, "std::math::sub": mathlib.sub,
                             "std::math::square": mathlib.square, "std::math::inv": mathlib.inv,
                             "std::math::div": mathlib.div,
                             "std::math::add_u256": mathlib.add_u256,
                             "std::math::add_u256_checked": mathlib.add_u256_checked,
                             "std::math::sub_u256": mathlib.sub_u256,
                             "std::math::sub_u256_checked": mathlib.sub_u256_checked,
                             "std::math::le_u256": mathlib.le_u256,
                             "std::math::lt_u256": mathlib.lt_u256,
                             "std::math::gt_u256": mathlib.gt_u256,
                             "std::math::ge_u256": mathlib.ge_u256,
                             "std::math::eq_u256": mathlib.eq_u256,
                             "std::math::ne_u256": mathlib.ne_u256,
                             "std::math::min_u256": mathlib.min_u256,
                             "std::math::max_u256": mathlib.max_u256}[name]
                return operation(self.builder, *values, wanted=wanted, span=self.span(expr))
            if name == "iterate":
                if expr.generic is None or len(expr.args) != 2:
                    raise TypeErrorS31("iterate<N>(step_function, initial_value) expected")
                step = self.eval_expr(expr.args[0], env)
                start = self.expect_value(self.eval_expr(expr.args[1], env), expr.args[1])
                steps = self.step_function_value(step, start.typ, expr)
                return self.builder.repeat(expr.generic, start, steps, wanted=wanted, span=self.span(expr))
            if expr.generic is not None and name != "splat":
                raise TypeErrorS31(f"{name} does not accept a static parameter")
            args = tuple(self.eval_expr(item, env) for item in expr.args)
            if name == "splat":
                if expr.generic is None or len(args) != 1 or not isinstance(args[0], int):
                    raise TypeErrorS31("splat<N>(constant_m31) expected")
                return self.builder.splat(args[0], expr.generic)
            if name == "m31_from_u16" and len(args) == 1:
                value = self.expect_value(args[0], expr)
                if value.typ.kind != "u16":
                    raise TypeErrorS31("m31_from_u16 requires a [u16; N] value; use std::bytes::limbs_m31 for wide values")
                return self.builder.cast_m31(value, wanted=wanted, span=self.span(expr))
            if name in {"std::bytes::to_u256_le", "std::bytes::from_u256_le"} and len(args) == 1:
                target = "uint256" if name.endswith("to_u256_le") else "bytes32"
                return self.builder.bytes32_reinterpret(self.expect_value(args[0], expr), target)
            if name == "std::bytes::limbs_m31" and len(args) == 1:
                value = self.expect_value(args[0], expr)
                if value.typ.kind not in {"uint256", "bytes32"}:
                    raise TypeErrorS31("limbs_m31 requires UInt256 or Bytes32")
                return self.builder.cast_m31(value, wanted=wanted, span=self.span(expr))
            if name in {"poseidon2_leaf", "blake2s_leaf"} and len(args) == 1:
                family = "poseidon2" if name.startswith("poseidon2") else "blake2s_reduced"
                return self.builder.hash_leaf(family, self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "sha256d_header" and len(args) == 1:
                return self.builder.sha256d_header(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "block_hash" and len(args) == 1:
                return self.builder.bitcoin_block_hash(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "hash_bytes" and len(args) == 1:
                return self.builder.bitcoin_hash_bytes(self.expect_value(args[0], expr))
            if name == "parent_hash" and len(args) == 1:
                return self.builder.bitcoin_parent_hash(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "target_mainnet" and len(args) == 1:
                return self.builder.bitcoin_target_mainnet(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name in {"target_u256", "work_u256", "chainwork_u256", "chainwork_from_work"} and len(args) == 1:
                source, target = {
                    "target_u256": ("target", "uint256"),
                    "work_u256": ("work", "uint256"),
                    "chainwork_u256": ("chainwork", "uint256"),
                    "chainwork_from_work": ("work", "chainwork"),
                }[name]
                return self.builder.bitcoin_nominal_view(self.expect_value(args[0], expr), source, target)
            if name == "block_work" and len(args) == 1:
                return self.builder.bitcoin_block_work(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "accumulate_chainwork" and len(args) == 2:
                values = tuple(self.expect_value(arg, expr) for arg in args)
                return self.builder.bitcoin_accumulate_chainwork(*values, wanted=wanted, span=self.span(expr))
            if name == "pow_valid" and len(args) == 1:
                return self.builder.bitcoin_pow_valid(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "prev_hash" and len(args) == 1:
                return self.builder.header_prev_hash(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "header_bits" and len(args) == 1:
                return self.builder.header_bits(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "header_time" and len(args) == 1:
                return self.builder.header_time(self.expect_value(args[0], expr), wanted=wanted, span=self.span(expr))
            if name == "lt_u32" and len(args) == 2:
                return self.builder.lt_u32(*(self.expect_value(arg, expr) for arg in args), wanted=wanted, span=self.span(expr))
            if name == "genesis_hash_mainnet" and len(args) == 0:
                return self.builder.genesis_hash_mainnet(wanted=wanted, span=self.span(expr))
            if name == "genesis_block_hash_mainnet" and len(args) == 0:
                return self.builder.genesis_block_hash_mainnet(wanted=wanted, span=self.span(expr))
            if name in {"poseidon2_pair", "blake2s_pair"} and len(args) == 2:
                family = "poseidon2" if name.startswith("poseidon2") else "blake2s_reduced"
                return self.builder.hash_pair(family, *(self.expect_value(arg, expr) for arg in args),
                                              wanted=wanted, span=self.span(expr))
            if name == "select" and len(args) == 3:
                return self.builder.select(*(self.expect_value(arg, expr) for arg in args),
                                           wanted=wanted, span=self.span(expr))
            if name == "is_zero" and len(args) == 1:
                return self.builder.is_zero(self.expect_value(args[0], expr),
                                            wanted=wanted, span=self.span(expr))
            if name == "bool_not" and len(args) == 1:
                return self.builder.boolean(name, self.expect_value(args[0], expr),
                                            wanted=wanted, span=self.span(expr))
            if name in {"bool_and", "bool_or", "bool_xor"} and len(args) == 2:
                return self.builder.boolean(name, self.expect_value(args[0], expr),
                                            self.expect_value(args[1], expr),
                                            wanted=wanted, span=self.span(expr))
            if name == "bool_select" and len(args) == 3:
                return self.builder.boolean(name, self.expect_value(args[1], expr),
                                            self.expect_value(args[2], expr),
                                            self.expect_value(args[0], expr),
                                            wanted=wanted, span=self.span(expr))
            if name in {"merkle_path_poseidon2", "merkle_path_blake2s"} and len(args) == 3:
                family = "poseidon2" if name.endswith("poseidon2") else "blake2s_reduced"
                if not isinstance(args[1], StaticGroup) or not isinstance(args[2], StaticGroup):
                    raise TypeErrorS31("merkle_path sibling and direction lists must be static arrays")
                return self.builder.merkle_path(family, self.expect_value(args[0], expr), args[1], args[2],
                                                wanted=wanted, span=self.span(expr))
            if name in self.functions and expr.generic is None:
                return self.call_function(name, args, wanted, expr)
            raise TypeErrorS31(f"unknown builtin or wrong arity: {name}")
        except TypeErrorS31 as exc:
            raise self.located(expr, exc) from exc

    def step_function_value(self, step: Any, typ: Type,
                            site: Expr) -> tuple[dict[str, Any], ...]:
        signature = self.source_type(step)
        if (not isinstance(signature, FunctionType) or signature.params != (typ,)
                or signature.result != typ or typ.kind != "m31"):
            raise self.located(site, "iterate step must have type [m31; N] -> [m31; N]")
        seed = StepState(typ, ())
        if isinstance(step, StaticNamedFunction):
            state = self.step_call_named(step.name, (seed,), site)
        elif isinstance(step, StaticClosure):
            state = self.step_call_closure(step, (seed,), site)
        else:
            raise self.located(site, "iterate requires a static function value")
        if not isinstance(state, StepState) or not state.steps:
            raise self.located(site, "iterate step must transform its input")
        return state.steps

    def step_call_named(self, name: str, args: tuple[Any, ...], site: Expr) -> Any:
        fn = self.functions[name]
        if len(fn.params) != len(args):
            raise self.located(site, "wrong step function arity")
        for (_, typ), value in zip(fn.params, args):
            if self.source_type(value) != typ:
                raise self.located(site, "step helper argument type mismatch")
        result = self.step_block(fn, {param: value for (param, _), value in zip(fn.params, args)}, site)
        if self.source_type(result) != fn.result:
            raise self.located(site, "step helper result type mismatch")
        return result

    def step_call_closure(self, closure: StaticClosure, args: tuple[Any, ...],
                          site: Expr) -> Any:
        if (len(args) != len(closure.signature.params) or
                any(self.source_type(arg) != typ for arg, typ in zip(args, closure.signature.params))):
            raise self.located(site, "step function value argument type mismatch")
        key = f"step-lambda:{id(closure.body)}"
        if key in self.call_stack or len(self.call_stack) >= MAX_CALL_DEPTH:
            raise self.located(site, "recursive or excessively deep step function")
        local = closure.captured.copy()
        local.update(zip(closure.names, args))
        self.call_stack.append(key)
        try:
            result = self.step_expr(closure.body, local)
        finally:
            self.call_stack.pop()
        if self.source_type(result) != closure.signature.result:
            raise self.located(site, "step function value result type mismatch")
        return result

    def step_block(self, fn: Function, env: dict[str, Any], site: Expr) -> Any:
        if fn.name in self.call_stack or len(self.call_stack) >= MAX_CALL_DEPTH:
            raise self.located(site, "recursive step function")
        self.call_stack.append(fn.name)
        try:
            local = env.copy()
            for statement in fn.statements:
                if statement.kind != "let":
                    raise self.located(site, "iterate step cannot contain assertions")
                if statement.name in local:
                    raise self.located(site, f"duplicate local name {statement.name}")
                local[statement.name] = self.step_expr(statement.args[0], local)
            return self.step_expr(fn.body, local)
        finally:
            self.call_stack.pop()

    def step_expr(self, expr: Expr, env: dict[str, Any]) -> Any:
        if expr.kind == "let":
            bound = self.step_expr(expr.args[0], env)
            local = env.copy()
            local[expr.value] = bound
            return self.step_expr(expr.args[1], local)
        if expr.kind == "name":
            if expr.value in env:
                return env[expr.value]
            if expr.value in self.functions:
                fn = self.functions[expr.value]
                return StaticNamedFunction(expr.value, FunctionType(
                    tuple(typ for _, typ in fn.params), fn.result))
            raise self.located(expr, f"unknown step value {expr.value}")
        if expr.kind == "tuple":
            elements = tuple(self.step_expr(item, env) for item in expr.args)
            types = tuple(self.source_type(item) for item in elements)
            if not all(isinstance(typ, (Type, FunctionType, TupleType)) for typ in types):
                raise self.located(expr, "tuple elements need declared source types")
            return StaticTuple(TupleType(types), elements)
        if expr.kind == "project":
            source = self.step_expr(expr.args[0], env)
            index = int(expr.value)
            if not isinstance(source, StaticTuple) or index >= len(source.elements):
                raise self.located(expr, "tuple projection index is out of range")
            return source.elements[index]
        if expr.kind == "lambda":
            assert expr.result_type is not None
            return StaticClosure(FunctionType(tuple(typ for _, typ in expr.params), expr.result_type),
                                 tuple(name for name, _ in expr.params), expr.args[0], env.copy())
        if expr.kind == "apply":
            callee = self.step_expr(expr.args[0], env)
            args = tuple(self.step_expr(arg, env) for arg in expr.args[1:])
            if isinstance(callee, StaticNamedFunction):
                return self.step_call_named(callee.name, args, expr)
            if isinstance(callee, StaticClosure):
                return self.step_call_closure(callee, args, expr)
            raise self.located(expr, "cannot apply non-function step value")
        if expr.kind == "field":
            number = int(expr.value[:-4])
            if not 0 <= number < P:
                raise self.located(expr, "m31 literal must be canonical")
            return number
        if expr.kind == "call" and expr.value in env:
            callee = env[expr.value]
            args = tuple(self.step_expr(arg, env) for arg in expr.args)
            if isinstance(callee, StaticNamedFunction):
                return self.step_call_named(callee.name, args, expr)
            if isinstance(callee, StaticClosure):
                return self.step_call_closure(callee, args, expr)
            raise self.located(expr, f"cannot call non-function step value {expr.value}")
        if expr.kind == "call" and expr.value == "splat":
            if expr.generic is None or len(expr.args) != 1:
                raise self.located(expr, "splat<N>(constant_m31) expected")
            constant = self.step_expr(expr.args[0], env)
            if not isinstance(constant, int):
                raise self.located(expr, "step splat requires a static constant")
            return self.builder.splat(constant, expr.generic)
        if expr.kind == "call" and expr.value == "std::math::square":
            if expr.generic is not None or len(expr.args) != 1:
                raise self.located(expr, "std::math::square(step_state) expected")
            value = self.step_expr(expr.args[0], env)
            if not isinstance(value, StepState):
                raise self.located(expr, "iterate can square only its current state")
            if len(value.steps) >= 16:
                raise self.located(expr, "iterate body exceeds sixteen steps")
            return StepState(value.typ, value.steps + ({"op": "square"},))
        if expr.kind == "call" and expr.value == "std::math::mix4":
            if expr.generic is not None or len(expr.args) != 1:
                raise self.located(expr, "std::math::mix4(step_state) expected")
            value = self.step_expr(expr.args[0], env)
            if not isinstance(value, StepState) or value.typ != Type("m31", 4):
                raise self.located(expr, "std::math::mix4 requires the current [m31; 4] state")
            if len(value.steps) >= 16:
                raise self.located(expr, "iterate body exceeds sixteen steps")
            return StepState(value.typ, value.steps + ({"op": "mix4"},))
        if expr.kind == "call" and expr.value in self.functions and expr.generic is None:
            return self.step_call_named(expr.value,
                                        tuple(self.step_expr(arg, env) for arg in expr.args), expr)
        if expr.kind == "binary":
            lhs, rhs = (self.step_expr(arg, env) for arg in expr.args)
            if isinstance(lhs, StepState) and isinstance(rhs, StepState):
                if expr.value == ".*" and lhs == rhs:
                    if len(lhs.steps) >= 16:
                        raise self.located(expr, "iterate body exceeds sixteen steps")
                    return StepState(lhs.typ, lhs.steps + ({"op": "square"},))
                raise self.located(expr, "iterate supports squaring the same state, not two different states")
            if isinstance(lhs, Value) and lhs.constant is not None:
                lhs, rhs = rhs, lhs
            if isinstance(lhs, StepState) and isinstance(rhs, Value) and rhs.constant is not None:
                if lhs.typ != rhs.typ:
                    raise self.located(expr, "step constant and state shapes differ")
                if len(lhs.steps) >= 16:
                    raise self.located(expr, "iterate body exceeds sixteen steps")
                op = "add_const" if expr.value == "+" else "mul_const"
                return StepState(lhs.typ, lhs.steps + ({"op": op, "constant": rhs.constant},))
        raise self.located(expr, "iterate step must use square, add_const, mul_const, or mix4 operations")

    def compile(self) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
        env = {name: self.builder.input(name, typ, visibility)
               for name, typ, visibility in self.circuit.params}
        result = self.expect_value(
            self.eval_block(self.circuit.statements, self.circuit.body, env), self.circuit.body)
        relation = self.builder.finish(result, self.circuit.result,
                                       span=self.span(self.circuit.body))
        if self.circuit.proof_mode == "blinded":
            relation["proof_mode"] = "blinded"
        return relation, self.builder.source_map
