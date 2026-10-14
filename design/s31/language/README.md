# S31 language design

The [functional v0.1 contract](FUNCTIONAL_V01.md) defines the static
specialization and dynamic circuit boundary. The
[formal semantics](FORMAL_SEMANTICS.md),
[compiler correspondence](COMPILER_CORRESPONDENCE.md), and
[general correspondence matrix](GENERAL_COMPILER_CORRESPONDENCE_MATRIX.md)
state what the source language means and which compiler-to-verifier joins
are proved. The [standard and math library](STDLIB_MATHLIB.md),
[fixed-width integers](FIXED_WIDTH_INTEGERS.md), and
[record ABI](RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md) describe user-facing
types and operations.

The executable syntax guide and worked examples are in the
[frontend documentation](../../../src/frontends/s31/docs/README.md). Keep
new language design notes with the relevant topic and link them from this
index. Security reviews belong under [security/reviews](../security/reviews/README.md).
