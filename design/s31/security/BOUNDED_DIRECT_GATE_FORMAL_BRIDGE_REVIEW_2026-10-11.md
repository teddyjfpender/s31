# Independent bounded direct-Gate bridge review, 2026-10-11

## Verdict and exact scope

The bounded alias source, canonical-IR byte model, and conditional raw-Gate
argument are coherent at their stated level. The reviewed theorems have no
project-specific Lean axioms: `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for the source/AIR composition, false-claim
bound, full fixed/main literal equality, and two source-row arithmetic proofs.
This is **not** an end-to-end proof of native verifier soundness. No reviewed
theorem derives its physical trace or ideal Gate-balance premises from a
verified proof.

`AliasCanonicalIrBytes.checkAliasCanonical` reparses the accepted bounded
source bytes and checks that its *modeled* normalized and canonical serializers
produce the supplied bytes. `canonical_alias_balanced_implies_claim` then
assumes a `PhysicalTraceContext` and exact `GateLookup.balanced` for a decoded
512-row trace. The context requires the 512-row partition, exact selected
source/public fixed cells, all nine local arithmetic roots on every row,
unique produced values per Gate address, specified zero/basis/inverse events,
and four external input and output pin events. Under these conditions the
public result equals the parsed source denotation. The ideal fixed-trace
challenge bound additionally assumes canonical event addresses and use/yield
counts below the base-field modulus. It does not model an adversary choosing a
trace after challenges, Fiat–Shamir sampling, PCS/FRI authentication, or a
native verifier return value.

The byte model does not itself prove that Python, Zig, native JSON
serialization, or SHA-256 implements the Lean functions. Differential tests
and native package admission supply executable evidence for the deliberately
small 1–16-gate fragment. They do not establish full-language compiler
correspondence.

## Square4 fixture and negative control

`PinnedFullFixedRoster` proves equality to a 512×8 **Lean literal** and
canonicality of its 4096 field cells. A separate Python comparison checks
the entire native fixed-column export against that literal and the pinned
key-root fixture. `PinnedNativeSquare4Witness` proves canonicality and literal
equality of 512×12 main cells. It proves the two source-product rows satisfy
their installed local arithmetic equations and that eight public copy rows
yield the specified words. The Python report checker evaluates all 4608 local
arithmetic roots and pins. It now checks exact ideal Gate event balance for
this one fixture using nine pinned external uses: the unit at address 2 and
eight public scalar words at addresses 3–10, with no external yields. It
checks each active output address has one produced value. The fixture does
not prove all-row arithmetic or Gate balance in Lean, nor any commitment
opening.

The local arithmetic equations cannot infer the exact native main trace.
Row 11 has fixed tuple `[1, 0, 0, 0, 0, 0, 0, 11]`: it is an add operation
with both input addresses and its output address zero, and **output
multiplicity 11**. The captured main tuple is all zero. Replacing its first
input with `1`, second input with `2`, and output with `3` leaves `1 + 2 = 3`,
all 4608 roots, all fixed cells, both source rows, and all eight public pins
valid. This is arithmetic padding, but it is not lookup-inactive: the change
alters Gate uses and eleven output tuples. The new ideal Gate check rejects
the alternative. The test in
`formal/s31/tests/test_square4_native_witness_scope.py` fixes this
counterexample and also runs the original four invalid-mutation controls.

Formal CI checks the committed JSON and regenerates the Lean literal from it;
it does not rerun a native `writeBase` export. Regenerating the report from a
fresh, source-bound package is the executable provenance check for a particular
run. The Lean kernel cannot establish that the committed 6144 main words are
the unique native prover output, and the local equations do not make them
unique. The theorem name `all_native_cells_exact` means equality to the
checked-in fixed and main literals, not equality to authenticated proof rows.

## Remaining proof obligations

1. Bind *all* fixed, main, and interaction evaluations and the public
   statement to the native verifier's accepted commitments and openings.
2. Derive the exact Gate feeder events and ideal balance, or a sound
   probabilistic substitute, from the installed native interaction AIR and
   verifier checks. The Python checker models nine feeder uses; the Lean
   fixture still sets external event lists to empty.
3. Connect the model's independent ideal challenge pairs to the actual
   Fiat–Shamir transcript, including challenge order and adaptive trace
   commitments, and discharge PCS/FRI soundness.
4. Establish a checked bridge from the production Zig compiler and verifier
   to the Lean byte, row, and AIR semantics. The current package and
   differential tests remain executable evidence for the bounded fragment.
5. If the fixture is used as a release provenance claim, regenerate its main
   values from a fresh native build under a pinned toolchain and compare all
   6144 cells. This check would establish reproducibility for that build, not
   verifier authentication or uniqueness from local AIR constraints.

## Checks performed

- `python3 formal/s31/scripts/check_square4_native_witness.py --report
  formal/s31/fixtures/square4-native-physical.json --controls`: 512 rows,
  4096 fixed cells, 6144 main cells, 4608 local roots, eight pins, two source
  rows, 1033 ideal uses and yields, 321 unique active producer addresses, and
  five rejected mutations.
- `python3 -m unittest formal/s31/tests/test_square4_native_witness_scope.py
  -q`: two tests pass, including rejection of the locally valid row-11 mutation
  by ideal Gate balance.
- `lake env lean /tmp/s31-bridge-review-axioms.lean`: the four named theorem
  checks above report only the three standard Lean axioms.
- Source inspection found no `axiom`, `sorry`, `admit`, or `unsafe` declaration
  in the reviewed correspondence modules, alias/canonical byte models, or
  square4 witness literal.
