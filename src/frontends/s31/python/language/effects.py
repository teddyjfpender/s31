"""Conservative totality analysis for eager, witness-dependent conditionals.

S31 specializes both arms of ``if`` into one fixed relation. Any constraint
that can fail on an inactive arm would change the meaning of a conditional.
This pass therefore admits a branch only when all its transitively invoked
operations are total on well-typed circuit values. Unknown function values
are treated as potentially partial. No relation nodes are emitted here.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from language.builtins import BUILTINS, MAX_CALL_DEPTH, STANDARD_ALIASES
from language.syntax import Circuit, Expr, Function, FunctionType, RecordType, SourceError, Statement, TupleType


# Keep this partition exhaustive. A newly added builtin must receive a
# reviewed effect before it can appear in an inactive branch.
PARTIAL_BUILTINS = frozenset({
    "accumulate_chainwork", "block_work", "pow_valid", "target_mainnet",
    "std::int::add_checked", "std::int::sub_checked", "std::int::mul_checked", "std::int::div_rem",
    "std::int::div_checked", "std::int::rem_checked",
    "std::int::from_limbs_i8", "std::int::from_limbs_u8",
    "std::math::add_u256_checked", "std::math::sub_u256_checked",
    "std::math::sum_u256_checked", "std::math::inv", "std::math::div",
    *(f"std::int::cast_checked_{kind}" for kind in
      ("u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128")),
})

TOTAL_BUILTINS = frozenset({
    "blake2s_leaf", "blake2s_pair", "block_hash", "bool_and", "bool_not",
    "bool_or", "bool_select", "bool_xor", "chainwork_from_work", "chainwork_u256",
    "genesis_block_hash_mainnet", "genesis_hash_mainnet", "hash_bytes", "header_bits", "header_time",
    "is_zero", "iterate", "lt_u32", "m31_from_u16", "merkle_path_blake2s",
    "merkle_path_poseidon2", "parent_hash", "poseidon2_leaf", "poseidon2_pair", "prev_hash",
    "select", "sha256d_header", "splat", "std::array::concat", "std::array::drop",
    "std::array::flatten", "std::array::get", "std::array::reshape", "std::array::take", "std::bytes::from_u256_le",
    "std::bytes::limbs_m31", "std::bytes::to_u256_le", "std::int::add_wrapping", "std::int::eq", "std::int::ge",
    "std::int::gt", "std::int::le", "std::int::limbs", "std::int::lt", "std::int::mul_wrapping", "std::int::ne",
    "std::int::sub_wrapping", "std::int::bit_and", "std::int::bit_or", "std::int::bit_xor", "std::int::bit_not",
    "std::int::shl", "std::int::shr_logical", "std::int::shr_arithmetic", "std::int::rotl", "std::int::rotr",
    "std::math::add_u256", "std::math::dot", "std::math::dot_lanes", "std::math::eq_u256",
    "std::math::ge_u256", "std::math::gt_u256", "std::math::le_u256", "std::math::lt_u256", "std::math::matmul",
    "std::math::matvec", "std::math::max_u256", "std::math::min_u256", "std::math::mix4", "std::math::ne_u256", "std::math::neg",
    "std::math::poly_eval", "std::math::pow", "std::math::square", "std::math::sub", "std::math::sub_u256",
    "std::math::sum", "std::math::sum_lanes", "std::math::sum_u256", "target_u256", "work_u256",
    *(f"std::int::from_limbs_{kind}" for kind in
      ("u16", "u32", "u64", "u128", "i16", "i32", "i64", "i128")),
    *(f"std::int::reinterpret_{kind}" for kind in
      ("u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128")),
})

CANONICAL_BUILTINS = frozenset(STANDARD_ALIASES.get(name, name) for name in BUILTINS)
STEP_ONLY_BUILTINS = frozenset({"std::math::mix4"})


@dataclass(frozen=True)
class Closure:
    expr: Expr
    captured: dict[str, AbstractValue]


@dataclass(frozen=True)
class OpaqueFunction:
    pass


@dataclass(frozen=True)
class NamedFunctionRef:
    name: str


@dataclass(frozen=True)
class FirstOrder:
    pass


@dataclass(frozen=True)
class TupleValue:
    elements: tuple[AbstractValue, ...]


@dataclass(frozen=True)
class RecordValue:
    signature: RecordType
    fields: tuple[tuple[str, AbstractValue], ...]


AbstractValue: TypeAlias = Closure | OpaqueFunction | NamedFunctionRef | FirstOrder | TupleValue | RecordValue
FIRST_ORDER = FirstOrder()
OPAQUE_FUNCTION = OpaqueFunction()


@dataclass(frozen=True)
class Effect:
    value: AbstractValue
    failure: frozenset[str] = frozenset()


class TotalityChecker:
    MAX_VISITS = 200_000

    def __init__(self, functions: dict[str, Function], circuit: Circuit, filename: str) -> None:
        self.functions = functions
        self.circuit = circuit
        self.filename = filename
        self.stack: list[str] = []
        self.visits = 0

    def error(self, expr: Expr, message: str) -> SourceError:
        return SourceError(f"{self.filename}:{expr.token.line}:{expr.token.column}: {message}")

    @staticmethod
    def parameter(typ: object) -> AbstractValue:
        if isinstance(typ, TupleType):
            return TupleValue(tuple(TotalityChecker.parameter(item) for item in typ.elements))
        if isinstance(typ, RecordType):
            fields = tuple((name, TotalityChecker.parameter(field_type))
                           for name, field_type in typ.fields)
            return RecordValue(typ, fields)
        return OPAQUE_FUNCTION if isinstance(typ, FunctionType) else FIRST_ORDER

    def block(self, statements: tuple[Statement, ...], body: Expr,
              env: dict[str, AbstractValue]) -> Effect:
        local = env.copy()
        failure: frozenset[str] = frozenset()
        for statement in statements:
            if statement.kind == "let":
                result = self.expr(statement.args[0], local)
                local[statement.name] = result.value
                failure |= result.failure
            else:
                for operand in statement.args:
                    result = self.expr(operand, local)
                    failure |= result.failure
        result = self.expr(body, local)
        return Effect(result.value, failure | result.failure)

    def invoke_function(self, name: str, args: tuple[AbstractValue, ...], site: Expr) -> Effect:
        key = f"fn:{name}"
        if key in self.stack or len(self.stack) >= MAX_CALL_DEPTH:
            raise self.error(site, "recursive or excessively deep effect analysis")
        fn = self.functions[name]
        local = {parameter: value for (parameter, _), value in zip(fn.params, args)}
        self.stack.append(key)
        try:
            return self.block(fn.statements, fn.body, local)
        finally:
            self.stack.pop()

    def invoke_closure(self, closure: Closure, args: tuple[AbstractValue, ...], site: Expr) -> Effect:
        key = f"lambda:{id(closure.expr)}"
        if key in self.stack or len(self.stack) >= MAX_CALL_DEPTH:
            raise self.error(site, "recursive or excessively deep effect analysis")
        local = closure.captured.copy()
        local.update((name, value) for (name, _), value in zip(closure.expr.params, args))
        self.stack.append(key)
        try:
            return self.expr(closure.expr.args[0], local)
        finally:
            self.stack.pop()

    def expr(self, expr: Expr, env: dict[str, AbstractValue]) -> Effect:
        self.visits += 1
        if self.visits > self.MAX_VISITS:
            raise self.error(expr, "effect analysis expansion limit exceeded")
        if expr.kind == "name":
            if expr.value in env:
                return Effect(env[expr.value])
            if expr.value in self.functions:
                return Effect(NamedFunctionRef(expr.value))
            return Effect(FIRST_ORDER)
        if expr.kind in {"field", "number"}:
            return Effect(FIRST_ORDER)
        if expr.kind == "lambda":
            captured = env.copy()
            local = captured | {name: self.parameter(typ) for name, typ in expr.params}
            # Validate nested conditionals even when this closure is unused.
            self.expr(expr.args[0], local)
            return Effect(Closure(expr, captured))
        if expr.kind == "let":
            bound = self.expr(expr.args[0], env)
            body = self.expr(expr.args[1], env | {expr.value: bound.value})
            return Effect(body.value, bound.failure | body.failure)
        if expr.kind == "tuple":
            components = tuple(self.expr(item, env) for item in expr.args)
            return Effect(TupleValue(tuple(item.value for item in components)),
                          frozenset().union(*(item.failure for item in components)))
        if expr.kind == "record":
            if expr.record_type is None:
                raise self.error(expr, "invalid struct constructor")
            components = tuple(self.expr(item, env) for item in expr.args)
            fields = tuple((name, item.value)
                           for (name, _), item in zip(expr.record_type.fields, components))
            return Effect(RecordValue(expr.record_type, fields),
                          frozenset().union(*(item.failure for item in components)))
        if expr.kind == "project":
            source = self.expr(expr.args[0], env)
            index = int(expr.value)
            if not isinstance(source.value, TupleValue) or index >= len(source.value.elements):
                raise self.error(expr, "tuple projection index is out of range")
            return Effect(source.value.elements[index], source.failure)
        if expr.kind == "field_project":
            source = self.expr(expr.args[0], env)
            if not isinstance(source.value, RecordValue):
                raise self.error(expr, "named field access requires a struct value")
            if expr.record_type is not None and source.value.signature != expr.record_type:
                raise self.error(expr, f"struct pattern expects {expr.record_type.name}")
            for name, value in source.value.fields:
                if name == expr.value:
                    return Effect(value, source.failure)
            raise self.error(expr, f"unknown struct field {expr.value}")
        if expr.kind == "if":
            condition = self.expr(expr.args[0], env)
            on_true = self.expr(expr.args[1], env)
            on_false = self.expr(expr.args[2], env)
            branch_effects = on_true.failure | on_false.failure
            concrete = sorted(reason for reason in branch_effects if not reason.startswith("opaque:"))
            if concrete:
                raise self.error(expr, f"if branch may fail when inactive: {', '.join(concrete)}")
            # A generic Fn parameter is checked again at each concrete call
            # site. Circuit inputs cannot contain Fn values, so none may
            # remain unresolved at the circuit boundary.
            # Elaborated products contain only selectable first-order leaves.
            # Preserve their static shape so a later field projection remains
            # analyzable without dropping an eager branch's failure.
            return Effect(on_true.value, condition.failure | branch_effects)
        if expr.kind in {"array", "binary"}:
            results = tuple(self.expr(arg, env) for arg in expr.args)
            return Effect(FIRST_ORDER, frozenset().union(*(item.failure for item in results)))
        if expr.kind == "apply":
            callee = self.expr(expr.args[0], env)
            results = tuple(self.expr(arg, env) for arg in expr.args[1:])
            failure = callee.failure | frozenset().union(*(item.failure for item in results))
            values = tuple(item.value for item in results)
            if isinstance(callee.value, Closure):
                result = self.invoke_closure(callee.value, values, expr)
                return Effect(result.value, failure | result.failure)
            if isinstance(callee.value, NamedFunctionRef):
                result = self.invoke_function(callee.value.name, values, expr)
                return Effect(result.value, failure | result.failure)
            # Type elaboration has already checked this is a Fn. Keep the
            # effect obligation until every concrete static call is known.
            return Effect(FIRST_ORDER, failure | {"opaque:application"})
        if expr.kind != "call":
            raise self.error(expr, "unknown expression in effect analysis")

        results = tuple(self.expr(arg, env) for arg in expr.args)
        failure = frozenset().union(*(item.failure for item in results))
        values = tuple(item.value for item in results)
        if expr.value in env:
            callee = env[expr.value]
            if isinstance(callee, Closure):
                result = self.invoke_closure(callee, values, expr)
                return Effect(result.value, failure | result.failure)
            if isinstance(callee, NamedFunctionRef):
                result = self.invoke_function(callee.name, values, expr)
                return Effect(result.value, failure | result.failure)
            return Effect(FIRST_ORDER, failure | {f"opaque:{expr.value}"})
        if expr.value in self.functions:
            result = self.invoke_function(expr.value, values, expr)
            return Effect(result.value, failure | result.failure)
        name = STANDARD_ALIASES.get(expr.value, expr.value)
        if name == "iterate":
            # The step body is evaluated in every round. Resolve its effect
            # now, including when a higher-order helper passes the function.
            step = values[0]
            if isinstance(step, NamedFunctionRef):
                effect = self.invoke_function(step.name, (FIRST_ORDER,), expr)
                failure |= effect.failure
            elif isinstance(step, Closure):
                effect = self.invoke_closure(step, (FIRST_ORDER,), expr)
                failure |= effect.failure
            else:
                failure |= {"opaque:iterate"}
        if name not in TOTAL_BUILTINS | PARTIAL_BUILTINS:
            raise self.error(expr, f"builtin {name} has no reviewed effect")
        if name == "std::int::div_rem":
            return Effect(TupleValue((FIRST_ORDER, FIRST_ORDER)), failure | {name})
        return Effect(FIRST_ORDER, failure | ({name} if name in PARTIAL_BUILTINS else set()))

    def check(self) -> None:
        recognized = CANONICAL_BUILTINS | STEP_ONLY_BUILTINS
        missing = recognized - (TOTAL_BUILTINS | PARTIAL_BUILTINS)
        extra = (TOTAL_BUILTINS | PARTIAL_BUILTINS) - recognized
        if missing or extra or TOTAL_BUILTINS & PARTIAL_BUILTINS:
            raise SourceError(f"S31 builtin effect inventory is stale: missing={sorted(missing)}, extra={sorted(extra)}")
        for fn in self.functions.values():
            env = {name: self.parameter(typ) for name, typ in fn.params}
            self.block(fn.statements, fn.body, env)
        env = {name: self.parameter(typ) for name, typ, _ in self.circuit.params}
        result = self.block(self.circuit.statements, self.circuit.body, env)
        unresolved = sorted(reason for reason in result.failure if reason.startswith("opaque:"))
        if unresolved:
            raise self.error(self.circuit.body,
                             f"unresolved function effect at circuit boundary: {', '.join(unresolved)}")
