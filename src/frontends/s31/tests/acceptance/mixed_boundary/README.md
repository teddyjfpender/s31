# Mixed boundary command acceptance

`record_general_v2.py` is the admitted public-record ABI v2 proof gate for
the source-pinned N=1 and N=8 `direct-mixed-general` family. It compiles each
source, checks the generated component manifest and registry digest, proves,
checks the exact typed statement bytes, and verifies with the corresponding
native verifier. It also rejects modified public words, malformed typed
claims, changed proof envelope identities and lookup sums, wrong source or
renamed ABI replay, and cross-profile proof replay.

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/record_general_v2.py
```

The focused run against working-tree HEAD `40bddbcb280f` on 2026-10-11
passed for both profiles. The N=1 proof was **69,488 bytes** and the N=8
proof was **163,853 bytes**. These are actual proof acceptance results for
the admitted source family. The separate eight-word alias/bit example in the
[record ABI guide](../record_abi/README.md) checks text, statement and native
parser correspondence and is not claimed to enter this proof profile.

`source_pinned.py` builds the experimental fixed N=3 mixed binaries from a
source file. It checks an honest proof, the generated component manifest,
changed public claims and proof fields, a separately built verifier with
changed embedded source, and build rejection of a valid two-call program.

Run from any directory:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
```

This is a black-box command test. The AIR equations and STARK core have their
own focused tests and review; passing this script does not establish a general
mixed boundary or witness confidentiality.

`preprocessed_root_binding.py` checks the native verifier's fixed-column
commitment boundary for N=1 and N=8. It first verifies both original proofs,
then swaps only the 32-byte preprocessed commitment root inside each proof's
serialized PCS body with the other valid package's root. Each generated verifier
must reject the structurally intact proof specifically with
`InvalidMixedPreprocessedRoot`. The source-derived inspector supplies the
expected roots; the test confirms each root occurs once in the original PCS
body before changing it.

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/preprocessed_root_binding.py
```

This establishes a concrete native rejection path for these two packages.
It is not a formal proof of the commitment scheme, collision resistance, or
the compiler's fixed-column semantics; those require separate arguments.

`arithmetic_chip_input.py` exercises every admitted four-lane arithmetic
feeder (`add`, `mul`, `add_const`, `mul_const`) with independently computed M31
claims, native proofs and mutation controls. Its source-pin check uses a
whitespace-only change, checks that the compiled IR, endpoint calls and fixed
root are identical, then reseals both statement and proof-envelope identities.
The old one-to-eight-call proof-byte compatibility procedure is in
[PROOF_BYTE_COMPATIBILITY.md](PROOF_BYTE_COMPATIBILITY.md); its baseline has
not yet been recorded.

`source_pinned_general.py` builds and proves the experimental mixed roster for
each count from one through eight. Its independent source/manifest projection
checks that each inspected call has the source repeat's ID, input node,
round count and constant; that consecutive calls use the preceding call's
four output addresses; and that circuit, chip and bridge slots carry the
declared Gate/chip relation IDs. It also checks each diagnostic source kind
against the versioned registry constructor and the proof and claimed-sum
indices. It rejects 20, 24 and 34 manifest mutations for one, three and eight
calls respectively, plus a changed source constant at each count. Every slot
gets a source-kind relabel mutation. A synthetic digest control shows that
relabeling the unhashed `source_kind` report field leaves the diagnostic registry digest
unchanged while the independent projection still rejects it. Run the
projection alone during a short edit loop:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static
```

The projection is an independent check of the public inspection report for
this chain family. It cannot derive absolute circuit endpoint addresses from
source text alone: its static control deliberately accepts a coordinated,
fresh address retarget while rejecting broken continuity and duplicate
addresses. Native source reinspection checks the generated topology;
fixed-column commitments and proof verification carry authority for the
package. The Python check does not authenticate trace values or prove the
source-to-Lean event correspondence.

For the native N=3 and N=8 profiles, the same acceptance also moves one unit
of a QM31 claimed sum from the first pair bridge to the final many bridge,
and separately between their chip components. Each mutation keeps the
**total** lookup sum unchanged. The generated verifier must still reject it
after the envelope and total lookup-sum checks, because each slot's claim is
bound to its AIR and to the transcript. This is a proof-header mutation, not
a forged witness or a complete soundness proof.

`semantic_source_reseal.py` can target a chosen call, including a later many
chip. It changes only that source repeat's constant, builds both generated
verifiers, proves both programs, then rewrites the old proof and statement's
source, registry-manifest and circuit-identity hashes to match the changed
program. The changed verifier must reject that structurally valid replay
beyond the transport identity checks. To exercise the N=3 many-chip call:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/semantic_source_reseal.py --counts 3 --changed-call 2
```

This checks source-to-fixed-root replay resistance for one selected later
call. It does not establish that every possible chip relation or bridge
trace is sound; the separate queried-opening and trace-mutation tests cover
other parts of that argument.

`typed_boundary_correspondence.py` checks the N=1..8 chain family against the
typed event model in
`formal/s31/S31/Gadgets/Air/SourceMixedPath.lean`. It derives the expected
absolute circuit addresses by hand from the reviewed compiler allocation:
reserved variables 0–10, private input words 11–14, input-packing temporaries
15–22, first chip outputs 23–26, and ten more variables per later call. It
compares those addresses, source rounds and constants, and relation IDs with
the native inspector. This detects the coordinated fresh-address retarget that
the shape-only projector above deliberately accepts. The static loop runs in
under a second:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/typed_boundary_correspondence.py
```

`formal/s31/S31/Gadgets/Air/SourceMixedAddressSchedule.lean` proves the
modeled address schedule is canonical for every admitted count up to eight,
that each later input block equals the previous output block, and that
different calls allocate distinct output blocks. It checks the first and
eighth concrete bridge address lists by kernel reduction. Under exact Gate
balance and producer uniqueness, it also proves that adjacent calls carry
identical values across their shared addresses. Equality of this model to the
production compiler still comes from the native inspector test.

`formal/s31/S31/Gadgets/Air/SourceMixedChainSemantics.lean` then proves an
inductive source meaning for every call up to eight: starting from the four
private input words, call `c` applies `w ↦ w² + (13+c)` exactly 16 times, and
the result is the next call's input. Its joint-event theorem derives every
call's source prefix from exact Gate/chip event balance, the chip row rules,
the reviewed address schedule, and unique Gate producers. Those premises are
visible in the theorem statement; an accepted native proof is not yet shown
to imply them.

`formal/s31/S31/Gadgets/Air/SourceMixedPublicClosure.lean` adds the source
tail: two packed Gate rows compute the sum and product, eight lane paths
extract the scalar words, and eight add-with-zero rows bind them to public
addresses 3–10. The theorem derives the public words from local AIR
acceptance, exact event balance, and unique Gate values without assuming row
operands or results. `SourceMixedPackCorrespondence.lean` derives the packed
wire values from scalar bridge events and selected six-row `simd.pack` paths.
`SourceMixedProducerCheck.lean` derives value uniqueness from a successful
scan of every logical producer address. The selected compiler rows, the exact
native producer roster, and proof authentication remain premises.
Its [worked example](../../../../../../formal/s31/S31/Gadgets/Air/SourceMixedPublicClosure.md)
shows the addresses and the arithmetic. The compiler-to-model and native
proof-to-event reductions remain explicit requirements.

Its native mode defaults to source-embedded N=1 and N=8 packages, checks the
exact inspected endpoints, emits an honest proof, checks the native public
statement, and runs the generated verifier. Pass `--counts 1 2 3 4 5 6 7 8`
to exercise the complete family:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/typed_boundary_correspondence.py --native
```

The focused Zig fixture checks the actual N=1 and N=8 circuit Gate lists:
both six-row packing paths, packed arithmetic operand order, eight lane
mask/inverse paths, eight public copy rows, zero permutation rows, and unique
declared-variable producers. It also checks bridge and chip base columns and
proves and verifies both pinned packages:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-correspondence -j1
```

For one call with private `x = [1, 2, 3, 4]`, the bridge's first four modeled
Gate reads are `[Gate,11,1,0,0,0,0]` through
`[Gate,14,4,0,0,0,0]`. Its next four Gate tuples use addresses 23–26 and the
four words after sixteen `w := w² + 13 mod 2147483647` rounds. The chip start
tuple is `[Chip,0,0,1,2,3,4]`; its finish tuple is
`[Chip,0,16,r0,r1,r2,r3]`. Eight public output Gate reads use addresses 3–10
for `r+x` and `r*x`, followed by fixed `u` at address 2 with QM31 coordinates
`[0,0,1,0]`. Every Gate tuple has a seventh zero coordinate because the joint
Gate/chip lookup uses seven coordinates.

This executable projection checks the native manifest and accepted public
statement against a source-shaped model for this source family. It constructs
the modeled Gate/chip tuples from source arithmetic and inspected addresses;
it does not compare them with an exported native trace. The native proof check
does not independently read bridge trace values or derive Lean event-list
hypotheses from proof acceptance. Those remain the
native AIR/PCS and formal correspondence obligations documented in the typed
boundary review.
