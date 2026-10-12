# Record ABI v2 statement semantics

The [Lean model](RecordStatementV2.lean) covers the public-claim loop after a
record type descriptor has been validated against the relation. For any number
of relation wires and named leaves, `admitStatement_iff` characterizes a
successful claim by three conditions:

1. Every claim appears in descriptor order with its exact tagged path, declared
   width, and allowed word range. An M31 word is below `2147483647`; a public
   bit word is `0` or `1`.
2. Every pair of claims for the same relation wire has identical words. The
   path may differ; aliasing does not add a new wire.
3. Looking up the public input wires and distinct result wires in relation
   order yields 1–8 words, followed by zero padding to eight slots.

`firstWireWords_admitted` proves that first occurrence lookup returns the
payload of **every** claim for that wire after the alias check. That is why
the model's immutable lookup and the native parser's mutable map have the
same intended semantic result for admitted claims. `admitStatement_sound`
also proves that accepted output has exactly eight slots.

## Hand-written example

```s31
struct Request { flag: bit, data: [m31; 2] }
struct Result { copy: [m31; 2] }
circuit copy(public req: Request) -> public Result {
    Result { copy: req.data }
}
```

Suppose `req.flag = 1` and `req.data = [4, 5]`. The compiled result leaf
references the same relation wire as `req.data`.

| Claim order | Tagged path | Wire | Claimed words |
| --- | --- | --- | --- |
| 1 | `root(req) / field(flag)` | `flag` | `[1]` |
| 2 | `root(req) / field(data)` | `data` | `[4, 5]` |
| 3 | `root(result) / field(copy)` | `data` | `[4, 5]` |

The named statement contains all three rows. The proof word vector is
`[1, 4, 5, 4, 5, 0, 0, 0]`: public input words first, then the one distinct
result wire, then zero padding. A result claim `[4, 6]` has the right width and
canonical M31 range but fails alias consistency. A bit claim `[2]` fails the
bit range check. A reordered path or extra leaf fails the positional check.

The result wire appears in both public input and result sections of the proof
vector because those sections are separate relation projections. Repeated
named result fields pointing to that one wire consume only one result section
slot.

## Source-to-model corpus

[`general_statement_refinement_v2.py`](../../../../../src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py)
compiles 13 deterministic S31 programs. They vary M31 leaf widths, nested
tuples, public bit leaves, private record roots, and input/result or
result/result aliases. For each program the script constructs a canonical
statement, checks the Python ABI decoder, independently walks the compiled
descriptors and projects proof words, and emits an exact Lean case in
[`GeneratedRecordStatementCorpusV2.lean`](GeneratedRecordStatementCorpusV2.lean).
The generated Lean file checks the 13 accepted statements, 13 valid changed
claims with changed proof words, and 65 malformed claim rejections. The
malformed classes are wrong path, width, range, missing leaf, and split alias.

From the repository root:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py --native
cd formal/s31
lake build S31.Gadgets.Functional.RecordStatementV2
lake env lean S31/Gadgets/Functional/GeneratedRecordStatementCorpusV2.lean
```

The optional native command checks 26 accepted and 65 rejected cases in Zig's
production record statement parser across all 13 layouts. It is a finite
source/decoder/model/native correspondence corpus, not a general parser
refinement. It does not prove that Zig parses all JSON bytes like the Lean
model, that the descriptor digest is computed correctly for every input, or
that a native proof authenticates these claim words. The existing nested
proof acceptance covers one concrete layout; a general parser refinement and
proof-verifier theorem remain open.
