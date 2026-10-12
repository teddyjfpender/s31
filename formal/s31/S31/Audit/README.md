# Optional Lean source/relation/IR audit

`AliasRelationCheck.lean` exposes the proved bounded alias-fragment checker as
an executable. It reads **exact file bytes** from a `.s31` source and its
normalized `.s31.json` relation, plus optional compact canonical IR bytes.
It calls `SSAAliasTextBytes.checkAliasRelation` or
`AliasCanonicalIrBytes.checkAliasCanonical` directly, then prints one JSON line.
On acceptance, that line includes the certificate's arithmetic gates and
output wire; exit status is zero. Rejection has `"accepted": false` and exit
status one. Usage or file errors return status two.

From `formal/s31`:

```sh
lake build s31-alias-relation-check
.lake/build/bin/s31-alias-relation-check source.s31 normalized.s31.json
.lake/build/bin/s31-alias-relation-check source.s31 normalized.s31.json canonical-ir.json
python3 -m unittest discover -s tests -p 'test_alias_relation_check.py' -q
```

The supported source subset is one public four-lane M31 input and output,
one to sixteen distinct canonical add/multiply producers, and optional alias
lets or redundant parentheses. Aliases add no gates. The normalized JSON
must match the Lean encoder byte for byte, including formatting and names.
When provided, the compact canonical IR must also match its Lean encoder byte
for byte, including optional null fields and producer output name and ID.
The focused test compares the handwritten alias fixture with production
lowering, then checks generated 1–16-gate sources with exact normalized and
compact IR bytes. It also rejects the independent checker's 25 reserved
builtin circuit names and overlong relation names. These are differential
regressions, not a general parser equivalence proof.

This is **optional audit evidence** for the Lean theorems
`checked_alias_relation_sound` and `checked_alias_canonical_bytes_sound`.
The native release verifier does not execute
this adapter or independently replay its proof. Acceptance here alone does
not establish AIR/PCS soundness or production compiler correspondence.

## Named-function source and exact relation bytes

`SourceFunctionCheck.lean` checks one pure named binary function over
`[m31; N]`, with `1 ≤ N ≤ 8`, called once by a circuit with two private inputs
and one public output. Addition, subtraction, and pointwise multiplication
are supported. The checker resolves parameter order and call order, then
requires the full canonical normalized relation file to match the Lean
encoder byte for byte. This audit subset requires ASCII bytes, including in
comments; the general text frontend has a broader source grammar. For an
accepted pair,
`SourceFunctionBytes.checked_relation_air_iff` proves that its packed AIR row
relation accepts exactly the function's result on every active lane. This
includes the final short row and arbitrary inactive input values.

From `formal/s31`:

```sh
lake build s31-source-function-check
.lake/build/bin/s31-source-function-check source.s31 source.s31.json
python3 -m unittest discover -s tests/audit -p 'test_source_function_check.py' -q
```

The executable prints `accepted`, array length, operation, and packed row
count as one JSON line. The 96 positive differential cases cover every length
1–8, all three operations, and four helper/call operand orders. Mutated source,
relation, formatting, reserved names, and function shadowing must fail. This
is an optional bounded audit; the production verifier does not run Lean, and
the test is not a general compiler-refinement proof.
