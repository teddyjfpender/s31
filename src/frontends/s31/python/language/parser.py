"""Bounded lexer and parser for the S31 text language."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from s31_stdlib import INT_TYPES, P, STDLIB_ABI_VERSION, Type, TypeErrorS31
from language.builtins import (BUILTINS, BINARY_POWER, INT_SOURCE_TYPES,
                               MAX_EXPRESSION_DEPTH, MAX_NUMBER_DIGITS,
                               MAX_TOKENS, MAX_TYPE_DEPTH,
                               TOKEN_RE, UNARY_POWER)
from language.syntax import Circuit, Expr, Function, FunctionType, RecordType, SourceError, Statement, Token, TupleType


@dataclass(frozen=True)
class Pattern:
    """Parser-only binder; product patterns desugar before type elaboration."""

    name: str | None
    elements: tuple[Pattern, ...]
    token: Token
    record_type: RecordType | None = None
    fields: tuple[str, ...] = ()


def lex(source: str, filename: str = "<source>") -> list[Token]:
    tokens: list[Token] = []
    position, line, column = 0, 1, 1
    while position < len(source):
        match = TOKEN_RE.match(source, position)
        if match is None:
            raise SourceError(f"{filename}:{line}:{column}: unexpected character {source[position]!r}")
        kind = match.lastgroup or ""
        chunk = match.group()
        if kind in {"number", "field"}:
            digits = len(chunk) - (4 if kind == "field" else 0)
            if digits > MAX_NUMBER_DIGITS:
                raise SourceError(f"{filename}:{line}:{column}: "
                                  f"numeric literal exceeds {MAX_NUMBER_DIGITS} decimal digits")
        if kind not in {"space", "comment"}:
            tokens.append(Token(kind, chunk, line, column))
            if len(tokens) > MAX_TOKENS:
                raise SourceError(f"{filename}:{line}:{column}: token limit exceeded")
        if "\n" in chunk:
            line += chunk.count("\n")
            column = len(chunk.rsplit("\n", 1)[1]) + 1
        else:
            column += len(chunk)
        position = match.end()
    tokens.append(Token("eof", "<eof>", line, column))
    return tokens


class Parser:
    def __init__(self, source: str, filename: str) -> None:
        self.tokens = lex(source, filename)
        self.filename = filename
        self.at = 0
        self.stdlib_explicit = False
        self.expression_depth = 0
        self.type_depth = 0
        self.pattern_depth = 0
        self.pattern_serial = 0
        self.pattern_expansion = 0
        self.records: dict[str, RecordType] = {}
        self.record_layouts: dict[str, tuple[int, int]] = {}

    def peek(self) -> Token:
        return self.tokens[self.at]

    def accept(self, text: str) -> Token | None:
        if self.peek().text == text:
            token = self.peek()
            self.at += 1
            return token
        return None

    def error(self, message: str, token: Token | None = None) -> SourceError:
        token = token or self.peek()
        return SourceError(f"{self.filename}:{token.line}:{token.column}: {message}")

    def expect(self, text: str) -> Token:
        found = self.accept(text)
        if found is None:
            raise self.error(f"expected {text!r}, found {self.peek().text!r}")
        return found

    def identifier(self) -> str:
        token = self.peek()
        if token.kind != "ident" or token.text in {
            "use", "let", "in", "if", "then", "else", "fun", "Fn", "fn", "struct", "circuit", "blinded",
            "public", "private", "assert_eq",
        }:
            raise self.error("expected identifier")
        self.at += 1
        return token.text

    def number(self) -> int:
        token = self.peek()
        if token.kind != "number":
            raise self.error("expected a compile-time natural number")
        self.at += 1
        return int(token.text)

    def pattern(self) -> Pattern:
        if self.pattern_depth >= MAX_TYPE_DEPTH:
            raise self.error("tuple pattern nesting limit exceeded")
        self.pattern_depth += 1
        try:
            token = self.peek()
            if token.text in self.records and self.tokens[self.at + 1].text == "{":
                typ = self.records[token.text]
                self.at += 1
                self.expect("{")
                fields: list[str] = []
                children: list[Pattern] = []
                declared = {name for name, _ in typ.fields}
                if self.accept("}"):
                    raise self.error("struct pattern needs at least one field", token)
                while True:
                    field_token = self.peek()
                    field = self.identifier()
                    if field not in declared:
                        raise self.error(f"unknown {typ.name} pattern field {field}", field_token)
                    if field in fields:
                        raise self.error(f"duplicate {typ.name} pattern field {field}", field_token)
                    fields.append(field)
                    children.append(Pattern(field, (), field_token))
                    if self.accept("}"):
                        break
                    self.expect(",")
                    if self.accept("}"):
                        break
                return Pattern(None, tuple(children), token, typ, tuple(fields))
            if not self.accept("("):
                return Pattern(self.identifier(), (), token)
            first = self.pattern()
            if not self.accept(","):
                self.expect(")")
                return first
            elements = [first, self.pattern()]
            while self.accept(","):
                elements.append(self.pattern())
            self.expect(")")
            return Pattern(None, tuple(elements), token)
        finally:
            self.pattern_depth -= 1

    def pattern_bindings(self, pattern: Pattern, bound: Expr) -> list[tuple[str, Expr, Token]]:
        """Bind the scrutinee once; projections of its static value are free."""
        if pattern.name is not None:
            return [(pattern.name, bound, pattern.token)]
        serial = self.pattern_serial
        self.pattern_serial += 1
        hidden = f"$s31_pattern_{serial}"  # '$' is excluded from source identifiers.
        self.pattern_expansion += 1
        bindings = [(hidden, bound, pattern.token)]

        def collect(current: Pattern, path: tuple[tuple[int | str, RecordType | None], ...]) -> None:
            if current.name is None:
                for index, child in enumerate(current.elements):
                    step: int | str = current.fields[index] if current.record_type else index
                    collect(child, path + ((step, current.record_type),))
                return
            # One name, one binding and one projection per path element.
            # Count the lowered tree, not only the shorter surface pattern.
            self.pattern_expansion += len(path) + 2
            if self.pattern_expansion > MAX_TOKENS:
                raise self.error("product pattern expansion limit exceeded", current.token)
            value = Expr("name", hidden, (), current.token)
            for step, record_type in path:
                if record_type is None:
                    value = Expr("project", str(step), (value,), current.token)
                else:
                    value = Expr("field_project", str(step), (value,), current.token,
                                 record_type=record_type)
            bindings.append((current.name, value, current.token))

        collect(pattern, ())
        names = [name for name, _, _ in bindings[1:]]
        if len(names) != len(set(names)):
            raise self.error("duplicate tuple binding", pattern.token)
        return bindings

    def parse_type(self) -> Type | FunctionType | TupleType | RecordType:
        if self.type_depth >= MAX_TYPE_DEPTH:
            raise self.error("type nesting limit exceeded")
        self.type_depth += 1
        try:
            return self._parse_type()
        finally:
            self.type_depth -= 1

    def _parse_type(self) -> Type | FunctionType | TupleType | RecordType:
        token = self.peek()
        if self.accept("Fn"):
            self.expect("(")
            arguments: list[Type | FunctionType | TupleType | RecordType] = []
            if not self.accept(")"):
                while True:
                    arguments.append(self.parse_type())
                    if self.accept(")"):
                        break
                    self.expect(",")
            self.expect("->")
            return FunctionType(tuple(arguments), self.parse_type())
        if self.accept("("):
            first = self.parse_type()
            if not self.accept(","):
                self.expect(")")
                return first
            elements = [first, self.parse_type()]
            while self.accept(","):
                elements.append(self.parse_type())
            self.expect(")")
            return TupleType(tuple(elements))
        if self.accept("["):
            kind = self.identifier()
            if kind not in {"m31", "u16"}:
                raise self.error("array element type must be m31 or u16", token)
            self.expect(";")
            length = self.number()
            self.expect("]")
            try:
                return Type(kind, length)
            except TypeErrorS31 as exc:
                raise self.error(str(exc), token) from exc
        if self.accept("bit"):
            return Type("bit", 1)
        if token.text in INT_SOURCE_TYPES:
            self.at += 1
            kind = INT_SOURCE_TYPES[token.text]
            return Type(kind, max(1, INT_TYPES[kind][0] // 16))
        if self.accept("UInt256"):
            return Type("uint256", 16)
        if self.accept("Bytes32"):
            return Type("bytes32", 16)
        if self.accept("BlockHash"):
            return Type("blockhash", 16)
        if self.accept("Target"):
            return Type("target", 16)
        if self.accept("Work"):
            return Type("work", 16)
        if self.accept("ChainWork"):
            return Type("chainwork", 16)
        if self.accept("Bytes80"):
            return Type("bytes80", 40)
        if self.accept("Digest"):
            self.expect("<")
            family = self.identifier()
            self.expect(">")
            normalized = {"Poseidon2": "poseidon2", "Blake2sReduced": "blake2s_reduced"}.get(family)
            if normalized is None:
                raise self.error("digest family must be Poseidon2 or Blake2sReduced", token)
            return Type("digest", 8, normalized)
        if token.kind == "ident" and token.text in self.records:
            self.at += 1
            return self.records[token.text]
        raise self.error("expected a circuit type or a static Fn(...) -> type")

    def record_field_layout(self, typ: Type | FunctionType | TupleType | RecordType) -> tuple[int, int]:
        """Bound nested source products and exclude function-valued fields."""
        if isinstance(typ, Type):
            return 1, 1
        if isinstance(typ, RecordType):
            return self.record_layouts[typ.name]
        if isinstance(typ, TupleType):
            layouts = [self.record_field_layout(item) for item in typ.elements]
            return 1 + max(depth for depth, _ in layouts), sum(leaves for _, leaves in layouts)
        raise self.error("struct fields must contain first-order values, tuples, or earlier structs")

    def record_declaration(self, function_names: set[str]) -> None:
        token = self.expect("struct")
        name = self.identifier()
        reserved = set(INT_SOURCE_TYPES) | {
            "UInt256", "Bytes32", "BlockHash", "Target", "Work", "ChainWork", "Bytes80",
            "Digest", "Poseidon2", "Blake2sReduced", "Fn", "bit", "m31", "u16",
        }
        if (not name[0].isupper() or name in reserved or name in BUILTINS or
                name in self.records or name in function_names):
            raise self.error(f"duplicate or reserved struct type {name}", token)
        if len(self.records) >= 128:
            raise self.error("struct declaration limit exceeded", token)
        self.expect("{")
        fields: list[tuple[str, Type | TupleType | RecordType]] = []
        names: set[str] = set()
        if not self.accept("}"):
            while True:
                field_token = self.peek()
                field = self.identifier()
                if field in names:
                    raise self.error(f"duplicate struct field {field}", field_token)
                names.add(field)
                self.expect(":")
                typ = self.parse_type()
                self.record_field_layout(typ)
                fields.append((field, typ))
                if len(fields) > 64:
                    raise self.error("struct field limit exceeded", field_token)
                if self.accept("}"):
                    break
                self.expect(",")
                if self.accept("}"):
                    break
        if not fields:
            raise self.error("struct needs at least one field", token)
        self.accept(";")
        layouts = [self.record_field_layout(typ) for _, typ in fields]
        depth = 1 + max(item[0] for item in layouts)
        leaves = sum(item[1] for item in layouts)
        if depth > MAX_TYPE_DEPTH or leaves > 1024:
            raise self.error("struct nesting or flattened field limit exceeded", token)
        self.records[name] = RecordType(name, tuple(fields))
        self.record_layouts[name] = depth, leaves

    def record_literal(self, typ: RecordType, token: Token) -> Expr:
        self.expect("{")
        supplied: dict[str, Expr] = {}
        declared = {name for name, _ in typ.fields}
        if not self.accept("}"):
            while True:
                field_token = self.peek()
                field = self.identifier()
                if field not in declared:
                    raise self.error(f"unknown {typ.name} field {field}", field_token)
                if field in supplied:
                    raise self.error(f"duplicate {typ.name} field {field}", field_token)
                self.expect(":")
                supplied[field] = self.expression()
                if self.accept("}"):
                    break
                self.expect(",")
                if self.accept("}"):
                    break
        missing = [name for name, _ in typ.fields if name not in supplied]
        if missing:
            raise self.error(f"missing {typ.name} fields: {', '.join(missing)}", token)
        # Fields are evaluated in declaration order, independent of literal order.
        return Expr("record", typ.name, tuple(supplied[name] for name, _ in typ.fields),
                    token, record_type=typ)

    def parameters(self, circuit: bool) -> tuple[Any, ...]:
        self.expect("(")
        params: list[Any] = []
        if not self.accept(")"):
            while True:
                visibility = None
                if circuit:
                    token = self.peek()
                    if token.text not in {"public", "private"}:
                        raise self.error("circuit input must be public or private")
                    visibility = token.text
                    self.at += 1
                name = self.identifier()
                self.expect(":")
                typ = self.parse_type()
                if circuit and not isinstance(typ, (Type, RecordType)):
                    raise self.error("circuit inputs must be first-order values or nominal records")
                params.append((name, typ, visibility) if circuit else (name, typ))
                if self.accept(")"):
                    break
                self.expect(",")
        names = [item[0] for item in params]
        if len(names) != len(set(names)):
            raise self.error("duplicate parameter name")
        return tuple(params)

    def call_arguments(self) -> tuple[Expr, ...]:
        """Parse one call suffix for named and expression-valued callees."""
        self.expect("(")
        args: list[Expr] = []
        if not self.accept(")"):
            while True:
                args.append(self.expression())
                if self.accept(")"):
                    break
                self.expect(",")
        return tuple(args)

    def block(self) -> tuple[tuple[Statement, ...], Expr]:
        self.expect("{")
        statements: list[Statement] = []
        while self.peek().text in {"let", "assert_eq"}:
            token = self.peek()
            if self.accept("let"):
                start = self.at - 1
                pattern = self.pattern()
                self.expect("=")
                expression = self.expression()
                if self.peek().text == "in":
                    # This is an expression-level binder, not a statement.
                    self.at = start
                    break
                self.expect(";")
                statements.extend(Statement("let", name, (value,), location)
                                  for name, value, location in self.pattern_bindings(pattern, expression))
            else:
                self.expect("assert_eq")
                self.expect("(")
                lhs = self.expression()
                self.expect(",")
                rhs = self.expression()
                self.expect(")")
                self.expect(";")
                statements.append(Statement("assert", "", (lhs, rhs), token))
        result = self.expression()
        self.accept(";")
        self.expect("}")
        return tuple(statements), result

    def declaration(self) -> Function | Circuit:
        if self.accept("fn"):
            name = self.identifier()
            params = self.parameters(False)
            self.expect("->")
            result = self.parse_type()
            statements, body = self.block()
            return Function(name, params, result, statements, body)
        proof_mode = "blinded" if self.accept("blinded") else "transparent"
        token = self.peek()
        self.expect("circuit")
        name = self.identifier()
        params = self.parameters(True)
        self.expect("->")
        self.expect("public")
        result = self.parse_type()
        if not isinstance(result, (Type, RecordType)):
            raise self.error("circuit output must be a first-order value")
        statements, body = self.block()
        return Circuit(name, params, result, statements, body, token, proof_mode)

    def expression(self, min_power: int = 0) -> Expr:
        if self.expression_depth >= MAX_EXPRESSION_DEPTH:
            raise self.error("expression nesting limit exceeded")
        self.expression_depth += 1
        try:
            return self._expression(min_power)
        finally:
            self.expression_depth -= 1

    def _expression(self, min_power: int = 0) -> Expr:
        token = self.peek()
        if self.accept("let"):
            pattern = self.pattern()
            self.expect("=")
            bound = self.expression()
            self.expect("in")
            body = self.expression()
            for name, value, location in reversed(self.pattern_bindings(pattern, bound)):
                body = Expr("let", name, (value, body), location)
            lhs = body
        elif self.accept("if"):
            condition = self.expression()
            self.expect("then")
            on_true = self.expression()
            self.expect("else")
            on_false = self.expression()
            lhs = Expr("if", "", (condition, on_true, on_false), token)
        elif self.accept("fun"):
            params = self.parameters(False)
            self.expect("->")
            result_type = self.parse_type()
            self.expect("=>")
            body = self.expression()
            lhs = Expr("lambda", "", (body,), token, params=params,
                       result_type=result_type)
        elif self.accept("-"):
            operand = self.peek()
            if operand.kind == "field" and int(operand.text[:-4]) < P:
                # Fold a negated canonical literal so `splat<N>(-7_m31)` works.
                self.at += 1
                lhs = Expr("field", f"{-int(operand.text[:-4]) % P}_m31", (), token)
            else:
                lhs = Expr("call", "std::math::neg", (self.expression(UNARY_POWER),), token)
        elif self.accept("("):
            first = self.expression()
            if self.accept(","):
                elements = [first, self.expression()]
                while self.accept(","):
                    elements.append(self.expression())
                self.expect(")")
                lhs = Expr("tuple", "", tuple(elements), token)
            else:
                self.expect(")")
                lhs = first
        elif self.accept("["):
            elements: list[Expr] = []
            if not self.accept("]"):
                while True:
                    elements.append(self.expression())
                    if self.accept("]"):
                        break
                    self.expect(",")
            lhs = Expr("array", "", tuple(elements), token)
        elif token.kind in {"field", "number"}:
            self.at += 1
            lhs = Expr("field" if token.kind == "field" else "number", token.text, (), token)
        elif token.kind == "ident":
            self.at += 1
            name = token.text
            while self.accept("::"):
                name += "::" + self.identifier()
            generic = None
            if self.accept("<"):
                generic = self.number()
                self.expect(">")
            if generic is None and name in self.records and self.peek().text == "{":
                lhs = self.record_literal(self.records[name], token)
            elif self.peek().text == "(":
                lhs = Expr("call", name, self.call_arguments(), token, generic)
            elif generic is None:
                lhs = Expr("name", name, (), token)
            else:
                raise self.error("type argument requires a call")
        else:
            raise self.error(f"expected expression, found {token.text!r}")
        while True:
            if self.peek().text == ".":
                dot = self.expect(".")
                if self.peek().kind == "number":
                    index = self.number()
                    lhs = Expr("project", str(index), (lhs,), dot)
                else:
                    lhs = Expr("field_project", self.identifier(), (lhs,), dot)
                continue
            if self.peek().text == "(":
                # A parenthesized lambda, `let ... in` result, or function
                # returned by a call can be applied directly. Named calls
                # above retain their existing builtin/generic dispatch.
                call_token = self.peek()
                lhs = Expr("apply", "", (lhs, *self.call_arguments()), call_token)
                continue
            operator = self.peek()
            power = BINARY_POWER.get(operator.text)
            if power is None or power < min_power:
                break
            self.at += 1
            rhs = self.expression(power + 1)
            if operator.text == "-":
                # Same lowering, types and errors as the library call.
                lhs = Expr("call", "std::math::sub", (lhs, rhs), operator)
            else:
                lhs = Expr("binary", operator.text, (lhs, rhs), operator)
        return lhs

    def check_expression_tree(self, root: Expr) -> None:
        """Bound left-associated ASTs as well as recursive parser nesting."""
        pending = [(root, 1)]
        while pending:
            expression, depth = pending.pop()
            if depth > MAX_EXPRESSION_DEPTH:
                raise self.error("expression tree depth limit exceeded", expression.token)
            pending.extend((child, depth + 1) for child in expression.args)

    def parse(self) -> tuple[dict[str, Function], Circuit]:
        if self.accept("use"):
            package = self.identifier()
            self.expect("@")
            version = self.number()
            self.expect(";")
            if package != "std" or version != STDLIB_ABI_VERSION:
                raise self.error("only the compiler-owned standard library std@1 is supported")
            self.stdlib_explicit = True
        functions: dict[str, Function] = {}
        while self.peek().text in {"fn", "struct"}:
            if self.peek().text == "struct":
                self.record_declaration(set(functions))
            else:
                fn = self.declaration()
                assert isinstance(fn, Function)
                if fn.name in functions or fn.name in BUILTINS or fn.name in self.records:
                    raise self.error(f"duplicate or reserved function {fn.name}")
                functions[fn.name] = fn
        circuit = self.declaration()
        if not isinstance(circuit, Circuit):
            raise self.error("expected one circuit")
        if circuit.name in self.records:
            raise self.error(f"circuit name conflicts with struct type {circuit.name}", circuit.token)
        if self.peek().kind != "eof":
            raise self.error("expected end of file after circuit")
        for declaration in (*functions.values(), circuit):
            for statement in declaration.statements:
                for operand in statement.args:
                    self.check_expression_tree(operand)
            self.check_expression_tree(declaration.body)
        return functions, circuit
