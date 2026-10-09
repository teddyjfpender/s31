"""Bounded lexer and parser for the S31 text language."""

from __future__ import annotations

from typing import Any

from s31_stdlib import INT_TYPES, P, STDLIB_ABI_VERSION, Type, TypeErrorS31
from language.builtins import (BUILTINS, BINARY_POWER, INT_SOURCE_TYPES,
                               MAX_EXPRESSION_DEPTH, MAX_TOKENS, MAX_TYPE_DEPTH,
                               TOKEN_RE, UNARY_POWER)
from language.syntax import Circuit, Expr, Function, FunctionType, SourceError, Statement, Token


def lex(source: str, filename: str = "<source>") -> list[Token]:
    tokens: list[Token] = []
    position, line, column = 0, 1, 1
    while position < len(source):
        match = TOKEN_RE.match(source, position)
        if match is None:
            raise SourceError(f"{filename}:{line}:{column}: unexpected character {source[position]!r}")
        kind = match.lastgroup or ""
        chunk = match.group()
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
            "use", "let", "in", "if", "then", "else", "fun", "Fn", "fn", "circuit", "blinded",
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

    def parse_type(self) -> Type | FunctionType:
        if self.type_depth >= MAX_TYPE_DEPTH:
            raise self.error("type nesting limit exceeded")
        self.type_depth += 1
        try:
            return self._parse_type()
        finally:
            self.type_depth -= 1

    def _parse_type(self) -> Type | FunctionType:
        token = self.peek()
        if self.accept("Fn"):
            self.expect("(")
            arguments: list[Type | FunctionType] = []
            if not self.accept(")"):
                while True:
                    arguments.append(self.parse_type())
                    if self.accept(")"):
                        break
                    self.expect(",")
            self.expect("->")
            return FunctionType(tuple(arguments), self.parse_type())
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
        raise self.error("expected a circuit type or a static Fn(...) -> type")

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
                if circuit and isinstance(typ, FunctionType):
                    raise self.error("circuit inputs must be first-order values")
                params.append((name, typ, visibility) if circuit else (name, typ))
                if self.accept(")"):
                    break
                self.expect(",")
        names = [item[0] for item in params]
        if len(names) != len(set(names)):
            raise self.error("duplicate parameter name")
        return tuple(params)

    def block(self) -> tuple[tuple[Statement, ...], Expr]:
        self.expect("{")
        statements: list[Statement] = []
        while self.peek().text in {"let", "assert_eq"}:
            token = self.peek()
            if self.accept("let"):
                start = self.at - 1
                name = self.identifier()
                self.expect("=")
                expression = self.expression()
                if self.peek().text == "in":
                    # This is an expression-level binder, not a statement.
                    self.at = start
                    break
                self.expect(";")
                statements.append(Statement("let", name, (expression,), token))
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
        if isinstance(result, FunctionType):
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
            name = self.identifier()
            self.expect("=")
            bound = self.expression()
            self.expect("in")
            body = self.expression()
            lhs = Expr("let", name, (bound, body), token)
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
            lhs = self.expression()
            self.expect(")")
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
            if self.accept("("):
                args: list[Expr] = []
                if not self.accept(")"):
                    while True:
                        args.append(self.expression())
                        if self.accept(")"):
                            break
                        self.expect(",")
                lhs = Expr("call", name, tuple(args), token, generic)
            elif generic is None:
                lhs = Expr("name", name, (), token)
            else:
                raise self.error("type argument requires a call")
        else:
            raise self.error(f"expected expression, found {token.text!r}")
        while True:
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
        while self.peek().text == "fn":
            fn = self.declaration()
            assert isinstance(fn, Function)
            if fn.name in functions or fn.name in BUILTINS:
                raise self.error(f"duplicate or reserved function {fn.name}")
            functions[fn.name] = fn
        circuit = self.declaration()
        if not isinstance(circuit, Circuit):
            raise self.error("expected one circuit")
        if self.peek().kind != "eof":
            raise self.error("expected end of file after circuit")
        for declaration in (*functions.values(), circuit):
            for statement in declaration.statements:
                for operand in statement.args:
                    self.check_expression_tree(operand)
            self.check_expression_tree(declaration.body)
        return functions, circuit
