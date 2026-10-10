"""Pure, whole-program source type elaboration before relation emission.

Every declaration and every lambda body is checked, including unused code.
This pass reads the located AST and emits no witness or relation nodes.
Specialization remains the authority for compile-time evaluation, constrained
bit provenance, static repeat shape, partial constants and resource limits.
"""

from __future__ import annotations

from s31_stdlib import P, Type, TypeErrorS31
from language.builtin_types import BIT, M31_ONE, SELECTABLE_KINDS, circuit, infer_builtin
from language.builtins import MAX_CALL_DEPTH, STANDARD_ALIASES
from language.syntax import Circuit, Expr, Function, FunctionType, SourceError, Statement
from language.types import FieldLiteral, SourceType, StaticArray


class Elaborator:
    def __init__(self, functions: dict[str, Function], circuit: Circuit, filename: str) -> None:
        self.functions = functions
        self.circuit = circuit
        self.filename = filename
        self.signatures = {name: FunctionType(tuple(typ for _, typ in fn.params), fn.result)
                           for name, fn in functions.items()}
        self.edges: dict[str, set[str]] = {}
        self.step_functions: set[str] = set()

    def error(self, expr: Expr, message: str) -> SourceError:
        return SourceError(f"{self.filename}:{expr.token.line}:{expr.token.column}: {message}")

    def referenced_calls(self, expr: Expr, bound: frozenset[str]) -> tuple[set[str], set[str]]:
        """Collect lexical call edges without treating shadowed names as globals."""
        if expr.kind == "let":
            calls, steps = self.referenced_calls(expr.args[0], bound)
            body_calls, body_steps = self.referenced_calls(expr.args[1], bound | {expr.value})
            return calls | body_calls, steps | body_steps
        if expr.kind == "lambda":
            return self.referenced_calls(expr.args[0], bound | {name for name, _ in expr.params})
        calls: set[str] = set()
        steps: set[str] = set()
        if expr.kind == "name" and expr.value not in bound and expr.value in self.functions:
            calls.add(expr.value)
        if expr.kind == "call" and expr.value not in bound:
            if expr.value in self.functions:
                calls.add(expr.value)
            if expr.value == "iterate" and expr.args and expr.args[0].kind == "name":
                steps.add(expr.args[0].value)
                if expr.args[0].value in self.functions:
                    calls.add(expr.args[0].value)
        for child in expr.args:
            child_calls, child_steps = self.referenced_calls(child, bound)
            calls.update(child_calls)
            steps.update(child_steps)
        return calls, steps

    def block_references(self, statements: tuple[Statement, ...], body: Expr,
                         initial: frozenset[str]) -> tuple[set[str], set[str]]:
        bound = initial
        calls: set[str] = set()
        steps: set[str] = set()
        for statement in statements:
            for expr in statement.args:
                found_calls, found_steps = self.referenced_calls(expr, bound)
                calls.update(found_calls)
                steps.update(found_steps)
            if statement.kind == "let":
                bound = bound | {statement.name}
        found_calls, found_steps = self.referenced_calls(body, bound)
        return calls | found_calls, steps | found_steps

    def prepare_calls(self) -> None:
        for name, fn in self.functions.items():
            calls, steps = self.block_references(fn.statements, fn.body,
                                                  frozenset(param for param, _ in fn.params))
            self.edges[name] = calls
            self.step_functions.update(steps)
        _, circuit_steps = self.block_references(
            self.circuit.statements, self.circuit.body,
            frozenset(name for name, _, _ in self.circuit.params))
        self.step_functions.update(circuit_steps)
        for root in tuple(self.step_functions):
            self.step_functions.update(self.reachable(root))
        depths: dict[str, int] = {}

        def depth(name: str, stack: tuple[str, ...]) -> int:
            if name in stack or len(stack) >= MAX_CALL_DEPTH:
                raise self.error(self.functions[name].body,
                                 "recursive or excessively deep function expansion")
            if name in depths:
                return depths[name]
            height = 1 + max((depth(dependency, stack + (name,))
                              for dependency in self.edges[name]), default=0)
            if height > MAX_CALL_DEPTH:
                raise self.error(self.functions[name].body,
                                 "recursive or excessively deep function expansion")
            depths[name] = height
            return height

        for name in self.functions:
            depth(name, ())

    def reachable(self, start: str) -> set[str]:
        found: set[str] = set()
        pending = [start]
        while pending:
            name = pending.pop()
            if name not in self.edges or name in found:
                continue
            found.add(name)
            pending.extend(self.edges[name] - found)
        return found

    def block(self, statements: tuple[Statement, ...], body: Expr,
              env: dict[str, SourceType], *, allow_assert: bool,
              step_mode: bool = False) -> SourceType:
        local = env.copy()
        for statement in statements:
            if statement.kind == "let":
                if statement.name in local:
                    raise self.error(statement.args[0], f"duplicate local name {statement.name}")
                local[statement.name] = self.expr(statement.args[0], local, step_mode=step_mode)
                continue
            if not allow_assert:
                raise self.error(statement.args[0], "pure functions cannot contain assertions")
            lhs = self.expr(statement.args[0], local, step_mode=step_mode)
            rhs = self.expr(statement.args[1], local, step_mode=step_mode)
            if not isinstance(lhs, Type) or not isinstance(rhs, Type):
                raise self.error(statement.args[0], "expected a circuit value")
            bit_field = {lhs.kind, rhs.kind} == {"bit", "m31"} and lhs.length == rhs.length == 1
            if lhs != rhs and not bit_field:
                raise self.error(statement.args[0],
                                 "assert_eq requires two values of the same relation type")
        return self.expr(body, local, step_mode=step_mode)

    def expr(self, expr: Expr, env: dict[str, SourceType], *, step_mode: bool = False) -> SourceType:
        try:
            if expr.kind == "name":
                if expr.value in env:
                    return env[expr.value]
                if expr.value in self.signatures:
                    return self.signatures[expr.value]
                raise TypeErrorS31(f"unknown value {expr.value}")
            if expr.kind == "number":
                raise TypeErrorS31("field literals require the _m31 suffix")
            if expr.kind == "field":
                value = int(expr.value[:-4])
                if not 0 <= value < P:
                    raise TypeErrorS31("m31 literal must be canonical")
                return FieldLiteral(value)
            if expr.kind == "array":
                elements = tuple(self.expr(item, env, step_mode=step_mode) for item in expr.args)
                if not elements or not all(isinstance(item, (Type, StaticArray)) for item in elements):
                    raise TypeErrorS31("static array elements must be circuit values or static arrays")
                return StaticArray(elements)
            if expr.kind == "let":
                bound = self.expr(expr.args[0], env, step_mode=step_mode)
                local = env.copy()
                local[expr.value] = bound
                return self.expr(expr.args[1], local, step_mode=step_mode)
            if expr.kind == "if":
                if step_mode:
                    raise TypeErrorS31("iterate steps cannot contain witness-dependent if expressions")
                condition = self.expr(expr.args[0], env)
                on_true = self.expr(expr.args[1], env)
                on_false = self.expr(expr.args[2], env)
                if condition != BIT:
                    raise TypeErrorS31("if condition must have type bit")
                if on_true != on_false or not isinstance(on_true, Type):
                    raise TypeErrorS31("if branches must have the same first-order circuit type")
                if on_true != BIT and on_true.kind not in SELECTABLE_KINDS:
                    raise TypeErrorS31("if result type cannot be selected by the circuit")
                return on_true
            if expr.kind == "lambda":
                if expr.result_type is None:
                    raise TypeErrorS31("lambda requires a declared result type")
                local = env.copy()
                local.update(expr.params)
                result = self.expr(expr.args[0], local, step_mode=step_mode)
                if result != expr.result_type:
                    raise TypeErrorS31("function value result does not match its declared type")
                return FunctionType(tuple(typ for _, typ in expr.params), expr.result_type)
            if expr.kind == "binary":
                lhs = circuit(self.expr(expr.args[0], env, step_mode=step_mode))
                rhs = circuit(self.expr(expr.args[1], env, step_mode=step_mode))
                if lhs != rhs or lhs.kind != "m31":
                    raise TypeErrorS31("arithmetic requires equally shaped m31 arrays")
                return lhs
            if expr.kind == "apply":
                callee = self.expr(expr.args[0], env, step_mode=step_mode)
                if not isinstance(callee, FunctionType):
                    raise TypeErrorS31("applied expression must have a Fn type")
                args = tuple(self.expr(arg, env, step_mode=step_mode)
                             for arg in expr.args[1:])
                if len(args) != len(callee.params):
                    raise TypeErrorS31(f"function value expects {len(callee.params)} arguments")
                for index, (actual, expected) in enumerate(zip(args, callee.params), 1):
                    if actual != expected:
                        raise TypeErrorS31(f"function value argument {index} expects {expected}")
                return callee.result
            if expr.kind != "call":
                raise TypeErrorS31("invalid expression")
            if expr.value in env:
                fn = env[expr.value]
                if not isinstance(fn, FunctionType):
                    raise TypeErrorS31(f"cannot call non-function value {expr.value}")
                if expr.generic is not None:
                    raise TypeErrorS31("function values do not accept static parameters")
                args = tuple(self.expr(arg, env, step_mode=step_mode) for arg in expr.args)
                if len(args) != len(fn.params):
                    raise TypeErrorS31(f"function value expects {len(fn.params)} arguments")
                for index, (actual, expected) in enumerate(zip(args, fn.params), 1):
                    if actual != expected:
                        raise TypeErrorS31(f"function value argument {index} expects {expected}")
                return fn.result
            if expr.value == "iterate":
                if expr.generic is None or len(expr.args) != 2 or expr.args[0].kind != "name":
                    raise TypeErrorS31("iterate<N>(step_function, initial_value) expected")
                name = expr.args[0].value
                if name not in self.signatures:
                    raise TypeErrorS31(f"unknown step function {name}")
                start = circuit(self.expr(expr.args[1], env, step_mode=step_mode))
                signature = self.signatures[name]
                if signature.params != (start,) or signature.result != start or start.kind != "m31":
                    raise TypeErrorS31("iterate step must have type [m31; N] -> [m31; N]")
                if not 1 <= expr.generic <= 32768:
                    raise TypeErrorS31("iterate requires 1..32768 rounds")
                return start
            args = tuple(self.expr(arg, env, step_mode=step_mode) for arg in expr.args)
            if expr.value in self.signatures:
                signature = self.signatures[expr.value]
                if expr.generic is not None:
                    raise TypeErrorS31(f"{expr.value} does not accept a static parameter")
                if len(args) != len(signature.params):
                    raise TypeErrorS31(f"{expr.value} expects {len(signature.params)} arguments")
                for (parameter, expected), actual in zip(self.functions[expr.value].params, args):
                    if actual != expected:
                        if step_mode:
                            raise TypeErrorS31("step helper argument type mismatch")
                        raise TypeErrorS31(f"{expr.value} argument {parameter} expects {expected}")
                return signature.result
            name = STANDARD_ALIASES.get(expr.value, expr.value)
            return infer_builtin(name, expr.generic, args, step_mode=step_mode)
        except TypeErrorS31 as exc:
            raise self.error(expr, str(exc)) from exc

    def check(self) -> None:
        self.prepare_calls()
        for name, fn in self.functions.items():
            env = {parameter: typ for parameter, typ in fn.params}
            result = self.block(fn.statements, fn.body, env, allow_assert=False,
                                step_mode=name in self.step_functions)
            if result != fn.result:
                if isinstance(fn.result, Type) and not isinstance(result, Type):
                    raise self.error(fn.body, "expected a circuit value")
                raise self.error(fn.body, f"{name} result does not match its declared type")
        env = {name: typ for name, typ, _ in self.circuit.params}
        result = self.block(self.circuit.statements, self.circuit.body, env, allow_assert=True)
        bit_as_field = result == BIT and self.circuit.result == M31_ONE
        if result != self.circuit.result and not bit_as_field:
            raise self.error(self.circuit.body,
                             "circuit result does not match declared public output type")
        public_words = sum(typ.length for _, typ, visibility in self.circuit.params
                           if visibility == "public") + self.circuit.result.length
        if public_words > 8:
            token = self.circuit.token
            raise SourceError(f"{self.filename}:{token.line}:{token.column}: "
                              f"current public ABI allows at most eight words; "
                              f"signature declares {public_words}")
