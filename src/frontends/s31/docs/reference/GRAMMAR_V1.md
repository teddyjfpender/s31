# S31 text grammar v1

This is the accepted source grammar for the current compiler. It describes
syntax; [types and operation preconditions](TEXT_LANGUAGE.md) and the
[conditional effect rule](../functional-language.md#witness-dependent-conditionals)
further restrict well-formed programs. The handwritten parser in
`python/language/parser.py` is authoritative if this document and the parser
disagree. The [generated source gate](../../tests/python/generated/README.md)
checks a deterministic grammar subset against independent evaluation and
perturbed input.

## Lexical tokens

```text
identifier    = ASCII letter or "_", followed by ASCII letters, digits or "_"
natural       = one or more ASCII digits
field_literal = natural, "_m31"
comment       = "//", any characters through the end of the line
```

Whitespace and comments separate tokens and otherwise have no meaning.
`field_literal` is one token and must denote a canonical integer in
`0..2147483646`. Numeric tokens have at most 64 decimal digits, including
leading zeroes; the lexer reports the source location when that limit is
exceeded. The lexer recognizes `->`, `=>`, `::`, and `.*` before
their one-character prefixes. The reserved words are `use`, `let`, `in`,
`if`, `then`, `else`, `fun`, `Fn`, `fn`, `circuit`, `blinded`, `public`,
`private`, `struct`, and `assert_eq`.

## Declarations and types

The notation below uses `{…}` for repetition, `[…]` for optional syntax,
and `|` for alternatives. Quoted punctuation is literal source text.

```text
file          = ["use", "std", "@", "1", ";"], {struct | function}, circuit, EOF
struct        = "struct", type_identifier, "{", field, {",", field}, [","], "}", [";"]
field         = identifier, ":", struct_field_type
struct_field_type = first_order_type | type_identifier
                  | "(", struct_field_type, ",", struct_field_type,
                    {",", struct_field_type}, ")"
type_identifier = identifier beginning with an uppercase ASCII letter
function      = "fn", identifier, function_parameters, "->", type, block
circuit       = ["blinded"], "circuit", identifier,
                circuit_parameters, "->", "public", first_order_type, block

function_parameters = "(", [identifier, ":", type,
                      {",", identifier, ":", type}], ")"
circuit_parameters  = "(", [visibility, identifier, ":", first_order_type,
                      {",", visibility, identifier, ":", first_order_type}], ")"
visibility    = "public" | "private"

type          = first_order_type | type_identifier
              | "Fn", "(", [type, {",", type}], ")", "->", type
              | "(", type, ",", type, {",", type}, ")"
              | "(", type, ")"
first_order_type = "bit" | "u8" | "u16" | "u32" | "u64" | "u128"
                | "i8" | "i16" | "i32" | "i64" | "i128"
                | "UInt256" | "Bytes32" | "Bytes80" | "BlockHash"
                | "Target" | "Work" | "ChainWork"
                | "Digest", "<", ("Poseidon2" | "Blake2sReduced"), ">"
                | "[", ("m31" | "u16"), ";", natural, "]"
```

Array lengths and type arguments are checked after parsing. `Fn`, tuples, and
struct records exist only during specialization; circuit inputs and outputs
require first-order types. A struct field may contain a first-order value, an
earlier declared struct, or a tuple recursively built from those types.
Function-valued fields and forward or recursive struct references are rejected.
Struct type names are nominal: equal field shapes with different names are
different source types. Functions may return or accept structs, `Fn`, and
tuple values. `Digest`
families and the fixed-width integer names are exact and case sensitive.

## Blocks and expressions

```text
block         = "{", {statement}, expression, [";"], "}"
statement     = "let", binding_pattern, "=", expression, ";"
              | "assert_eq", "(", expression, ",", expression, ")", ";"
binding_pattern = identifier
              | type_identifier, "{", identifier, {",", identifier}, [","], "}"
              | "(", binding_pattern, ")"
              | "(", binding_pattern, ",", binding_pattern,
                {",", binding_pattern}, ")"
expression    = prefix, {postfix_call | postfix_projection | binary_operator, prefix}
postfix_call  = "(", [expression, {",", expression}], ")"
postfix_projection = ".", (natural | identifier)
prefix        = "let", binding_pattern, "=", expression, "in", expression
              | "if", expression, "then", expression, "else", expression
              | "fun", function_parameters, "->", type, "=>", expression
              | "-", expression
              | atom
atom          = identifier
              | type_identifier, "{", named_field, {",", named_field}, [","], "}"
              | qualified_name, ["<", natural, ">"], "(", [expression,
                {",", expression}], ")"
              | field_literal
              | natural
              | "(", expression, ")"
              | "(", expression, ",", expression, {",", expression}, ")"
              | "[", [expression, {",", expression}], "]"
qualified_name = identifier, {"::", identifier}
named_field    = identifier, ":", expression
binary_operator = "+" | "-" | ".*"
```

The parser's block lookahead distinguishes a `let …;` statement from a final
`let … in …` expression. A bare `natural` is parsed so diagnostics can name
it, but the type checker rejects it as a circuit value. Static natural
arguments are used in calls such as `splat<4>(7_m31)`.

Tuple expressions and tuple types have at least two elements. `(x)` is
grouping; `(x, y)` is a tuple; `pair.0` selects its first element. Indexing is
zero-based and statically checked. Tuple construction evaluates every
component, even if a later projection selects only one. Tuples add no relation
node of their own, but their component computations are retained.
Tuple patterns destructure a source tuple in a block or `let … in`, for
example `let (square, double) = powers(x);` or
`let ((a, b), c) = nested in a + b + c`. The bound expression is evaluated
once. The parser uses a source-inaccessible temporary name and lowers the
pattern to ordinary `let` bindings and static projections. A repeated name
within one tuple pattern is rejected. No pattern node reaches elaboration,
relation JSON or AIR.

`struct Powers { square: [m31; 4], doubled: [m31; 4] }` declares a nominal
static product. `Powers { doubled: x + x, square: x .* x }` constructs one with
all fields named exactly once; `p.square` selects a field. Literal fields may
appear in any order. Their expressions are evaluated in declaration order,
including fields never projected later. Construction and projection add no
normalized relation node; the field expressions still contribute their normal
nodes and partial effects. A tuple projection remains numeric (`p.0`), while
named projection requires a struct value. Witness-dependent selection of a
whole record or tuple is accepted when both branches have the same type and
every leaf has a constrained selector. The compiler emits both branches and
then one selector per leaf in declaration order. A function-valued leaf is
rejected. `assert_eq` over equal nominal records or equally typed tuples
expands to one assertion per first-order leaf. This gives the same relation
as writing those selectors or assertions field by field.

`let Powers { square, doubled } = powers(x);` binds named fields without
creating a relation node. A record pattern may list a subset of fields but
must list at least one. It requires the exact nominal type, rejects repeated
or unknown names, and can nest inside a tuple pattern. Like tuple patterns,
it evaluates the source expression once and works in both block statements
and `let … in` expressions. Unbound fields still retain their computations
and partial effects.

The parser uses left-associative Pratt binding powers: unary `-` is 30,
lane-wise `.*` is 20, and `+` and `-` are 10. Postfix application binds more
tightly than arithmetic and may follow any expression whose type is `Fn`.
Postfix projection has the same precedence and can be chained or followed by
application, as in `pair.0(value)`.
For example, `add_to(a)(b)` applies a function returned by `add_to(a)`, and
`(fun(x: [m31; 1]) -> [m31; 1] => x)(value)` applies a lambda immediately.
An unshadowed bare top-level function name is a compile-time `Fn` value, so
`apply(square, x)`, `(square)(x)`, and `let f = square in f(x)` are valid when
the declared types match. Local names take precedence over top-level names.
`iterate<N>(step, initial)` accepts a static `Fn([m31; K]) -> [m31; K]`
expression, including a named function passed through a parameter or a
constant-capturing `fun`. A `Fn` returned by a named factory or a local
`let` bound closure is also accepted when specialization yields a supported
step. The specialized step body must reduce to one to
sixteen supported recurrence operations; no witness-dependent capture,
conditional, inverse, or helper call that cannot reduce to supported steps is
admitted.
`if`, expression `let`, and `fun` are prefix forms; parenthesize them when
embedding them in a larger arithmetic expression or applying their result.
Calls, types, shapes and builtins receive separate
type/effect checks. `assert_eq` is allowed only in circuit blocks.

## Resource and diagnostic contract

The lexer accepts at most **100,000 tokens**. Recursive expression parsing
and the resulting expression tree each have a **128-level** limit; recursive
type parsing and tuple patterns each have a **32-level** limit. Static function expansion has a
**32-call** limit, and effect analysis has a **200,000-expression-visit**
limit. Each parser limit reports the file, line and column at the offending
token. Product-pattern lowering is capped at **100,000 generated AST nodes**
across the source file, including hidden bindings and projection paths.
Struct declarations are capped at 128 types, 64 fields per type, 32 levels of
nested product layout, and 1,024 flattened first-order fields per type. These
limits bound parser work and reject deep source trees before later
recursive compiler passes.

The grammar does not assert that all well-typed programs are cheap to prove.
Use `s31 explain` and the package cost report to inspect the actual selected
AIR and row counts.
