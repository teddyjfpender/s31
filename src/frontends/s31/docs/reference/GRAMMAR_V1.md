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
`0..2147483646`. The lexer recognizes `->`, `=>`, `::`, and `.*` before
their one-character prefixes. The reserved words are `use`, `let`, `in`,
`if`, `then`, `else`, `fun`, `Fn`, `fn`, `circuit`, `blinded`, `public`,
`private`, and `assert_eq`.

## Declarations and types

The notation below uses `{…}` for repetition, `[…]` for optional syntax,
and `|` for alternatives. Quoted punctuation is literal source text.

```text
file          = ["use", "std", "@", "1", ";"], {function}, circuit, EOF
function      = "fn", identifier, function_parameters, "->", type, block
circuit       = ["blinded"], "circuit", identifier,
                circuit_parameters, "->", "public", first_order_type, block

function_parameters = "(", [identifier, ":", type,
                      {",", identifier, ":", type}], ")"
circuit_parameters  = "(", [visibility, identifier, ":", first_order_type,
                      {",", visibility, identifier, ":", first_order_type}], ")"
visibility    = "public" | "private"

type          = first_order_type | "Fn", "(", [type, {",", type}], ")", "->", type
first_order_type = "bit" | "u8" | "u16" | "u32" | "u64" | "u128"
                | "i8" | "i16" | "i32" | "i64" | "i128"
                | "UInt256" | "Bytes32" | "Bytes80" | "BlockHash"
                | "Target" | "Work" | "ChainWork"
                | "Digest", "<", ("Poseidon2" | "Blake2sReduced"), ">"
                | "[", ("m31" | "u16"), ";", natural, "]"
```

Array lengths and type arguments are checked after parsing. `Fn` values
exist only during specialization; circuit inputs and outputs require
first-order types. Functions may return or accept `Fn` values. `Digest`
families and the fixed-width integer names are exact and case sensitive.

## Blocks and expressions

```text
block         = "{", {statement}, expression, [";"], "}"
statement     = "let", identifier, "=", expression, ";"
              | "assert_eq", "(", expression, ",", expression, ")", ";"
expression    = prefix, {binary_operator, prefix}   // Pratt precedence below
prefix        = "let", identifier, "=", expression, "in", expression
              | "if", expression, "then", expression, "else", expression
              | "fun", function_parameters, "->", type, "=>", expression
              | "-", expression
              | atom
atom          = identifier
              | qualified_name, ["<", natural, ">"], "(", [expression,
                {",", expression}], ")"
              | field_literal
              | natural
              | "(", expression, ")"
              | "[", [expression, {",", expression}], "]"
qualified_name = identifier, {"::", identifier}
binary_operator = "+" | "-" | ".*"
```

The parser's block lookahead distinguishes a `let …;` statement from a final
`let … in …` expression. A bare `natural` is parsed so diagnostics can name
it, but the type checker rejects it as a circuit value. Static natural
arguments are used in calls such as `splat<4>(7_m31)`.

The parser uses left-associative Pratt binding powers: unary `-` is 30,
lane-wise `.*` is 20, and `+` and `-` are 10. `if`, expression `let`, and
`fun` are prefix forms; parenthesize them when embedding them in a larger
arithmetic expression. Calls, types, shapes and builtins receive separate
type/effect checks. `assert_eq` is allowed only in circuit blocks.

## Resource and diagnostic contract

The lexer accepts at most **100,000 tokens**. Recursive expression parsing
and the resulting expression tree each have a **128-level** limit; recursive
type parsing has a **32-level** limit. Static function expansion has a
**32-call** limit, and effect analysis has a **200,000-expression-visit**
limit. Each parser limit reports the file, line and column at the offending
token. They bound parser work and reject deep source trees before later
recursive compiler passes.

The grammar does not assert that all well-typed programs are cheap to prove.
Use `s31 explain` and the package cost report to inspect the actual selected
AIR and row counts.
