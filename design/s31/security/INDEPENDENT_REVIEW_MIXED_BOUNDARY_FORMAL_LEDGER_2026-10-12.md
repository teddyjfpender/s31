# Independent review: mixed boundary and new Gate correspondence checks

Scope: the source-embedded `direct-mixed-general` verifier for one to eight
square/add-constant calls, the generated registry manifest, and the direct-Gate
Lean modules `AcceptedPublicFixedCells`, `CheckedGateAddressLedger`,
`PinnedGateAddressLedger`, `NativeConstantIslandCertificate`, and the pinned
square4 constant instance. I read the verifier, engine, preprocessor, bridge,
fixture generators, and theorem statements. This is a focused source and
fixture review. I found no concrete path for accepting a false public claim
through the source-embedded entrypoint. I did not construct a forged proof or
prove the STARK/PCS implementation sound.

## Authentication path checked

The actual CLI in
[`general_verifier_main.zig`](../../../src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig)
embeds source and official AIR bytes at build time. The package's
[`verifySourceBoundWithWitness`](../../../src/frontends/s31/runtime/mixed_boundary/general_package.zig)
re-inspects that source and rebuilds the registry-derived plan, topology,
fixed root, and native geometry before bounded proof deserialization. It
checks the call/slot counts, source hash, manifest digest, circuit identity,
canonical public words, and exact proof byte consumption. The V2 alias path
also checks the admitted public bit domain at this raw package boundary.

The source inspector compiles endpoint addresses from the source, checks
fresh output ports and exact slot order, obtains live pair/many constructors,
checks the preprocessed root, and caps Gate rows, call rounds, and lookup
weight. The
[`direct_arithmetic.zig`](../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig)
preprocessor increments committed output multiplicity once **per endpoint
occurrence**; repeated input addresses across calls therefore require
repeated bridge reads. The bridge AIR constrains each endpoint word equal
across its 16 rows and contributes Gate and tagged chip endpoint terms. The
chip AIR constrains each lane's square/add step. In the native
[`verifySourceBoundBorrowed`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig),
the preprocessed commitment is compared with the rebuilt commitment, the
source/manifest/circuit identity and public words enter the transcript, the
ordered circuit/chip/bridge claimed sums must close, runtime handles are
checked, and the STARK verifier runs. The lower-level engine adapter accepts
a caller-selected `Selected`; the source-embedded package is the proof-byte
admission API reviewed here.

The registry manifest is regenerated from that inspected source. Its digest
binds call IDs, exact endpoint addresses, ordered roles and claim slots,
relation IDs, column spans, AIR/program bindings, and the selected schedule
digest. The latter covers live PCS geometry, mask-point digest, and a seven
file local AIR dependency digest. The JSON inspector is an audit report,
not a verifier key. The seven file digest is not a transitive import hash.

## Exact scope of the new Lean checks

| Module | What its theorem establishes | Premise or missing native join |
| --- | --- | --- |
| [`AcceptedPublicFixedCells.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/AcceptedPublicFixedCells.lean) | For arbitrary checked direct functional source bytes and input, constructs one 512-row modeled trace with all local arithmetic roots zero, exact fixed words for projected source and public cells, and the selected output denotation. Its `List UInt8` corollary states literal-byte admission. | Other rows are synthetic zero-add padding. The theorem does not say their fixed words equal the production roster, or that a proof opens to this trace. It is a direct functional slice, not a correspondence theorem for every mixed chip program. |
| [`CheckedGateAddressLedger.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedGateAddressLedger.lean) | An executable fixed-address multiset check implies exact ideal Gate event balance for **any one coherent** `wire : Nat → Quad`. The checker caps 512 rows and 2048 total output multiplicity before expanding `List.replicate`; a hostile M31-sized count is rejected. | It does not derive address coherence from native committed main columns, or compressed LogUp balance from verifier acceptance. Its external uses/yields are caller arguments. |
| [`PinnedGateAddressLedger.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/PinnedGateAddressLedger.lean) | The complete pinned square4 fixed roster passes that address check: 512 rows and 1033 uses/yields with nine external feeder addresses. | A single fixture does not establish the ledger for every admitted source. It does not authenticate feeder values or the proof's main/interaction openings. |
| [`NativeConstantIslandCertificate.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/NativeConstantIslandCertificate.lean) | A checked certificate covers all constant/padding row positions with one-hot selectors, isolated/canonical addresses, coherent supplied values, local arithmetic, unique island outputs, and required seed/basis/inverse values. | `check_sound` extracts properties of a supplied certificate and value table. The production compiler must still be shown to emit those fixed cells, and native committed main values must agree with the table. |
| [`PinnedSquare4ConstantIslandCertificate.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/PinnedSquare4ConstantIslandCertificate.lean) | Finite nonvacuity for all 485 square4 constant rows under the pinned native value table. | It is tied to a generated concrete fixture, not to arbitrary source or a PCS opening. |

I found no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` token in these
five modules or their generated square4 value table. This textual check is
not a kernel replay; the final `leanchecker`/axiom audit remains the release
gate. The address-ledger proof is not circular at the model level: its
`check_sound` conclusion is `balanced`, derived from `List.isPerm` of fixed
addresses, with no `balanced` hypothesis. Its coherent-wire hypothesis is
the soundness-relevant bridge still missing from native verification.

## Fixture provenance and limits

The checked-in
[`square4-native-physical.json`](../../../formal/s31/fixtures/square4-native-physical.json)
has SHA-256 `4a46c07ee65f1b0a10e1cb57c75cd32770d922dc09855d1d678f8570925397d4`.
The value-table generator reads its eight fixed and twelve main columns,
requires canonical 512-row cells and a permutation of output addresses
`0..511`, then maps each native main output tuple to its fixed output
address. The Lean value-table source records that physical JSON hash.

There are two separate comparison paths. `check_square4_native_witness.py`
compares the JSON fixed columns to the checked-in native-key fixed-column
fixture and checks all 512 local arithmetic rows, eight public pins, exact
value-level Gate balance, and five mutations. `fixed_columns.py` compares all
4096 Lean fixed-row literals to the column-major native-key fixture, which
records preprocessed root
`c0ea49c8f9027d5bdf9ce7a59ded3fb3a1f6b541a0ed1bb6c65b3c7d1175570a`.
`check_fresh_square4_native_witness.py` is the clean-checkout regeneration
path: it rebuilds the source-bound native package into a fresh temporary
directory and compares its fixed columns, physical JSON, and Lean main-row
fixture byte for byte. I did not run this native rebuild during the parallel
formal build. The pinned JSON and Lean value table alone do not recompute a
Merkle root or authenticate a proof's main-column openings. In particular,
the constant-island Lean theorem does not prove that its supplied value
table is extracted from the PCS commitment.

Focused local checks:

```text
python3 -B src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static
  passed: N=1/3/8 source projections; 20/24/34 roster mutations and four
  geometry-report mutations rejected. Its coordinated fresh absolute-address
  retarget intentionally remains accepted by this static projector; the
  native source recompiler, not this test, authenticates absolute addresses.
python3 -B src/frontends/s31/tools/formal/pinned_constant_values.py --check
  passed: generated Lean value table matches the checked-in physical JSON.
check_square4_native_witness.render_lean(report) == TextSquare4NativeWitness.lean
  passed: all pinned Lean main rows match the same physical JSON.
python3 -B formal/s31/scripts/check_square4_native_witness.py --report formal/s31/fixtures/square4-native-physical.json --controls
  passed: 4096 fixed, 6144 main, 4608 local arithmetic roots,
  1033 ideal Gate uses/yields, five mutations rejected.
fixed_columns.read_fixture(); fixed_columns.check_formal_rows(columns)
  passed: all 4096 formal/native fixed cells match the pinned fixture.
```

## Remaining soundness obligations

1. Prove or independently check for **every admitted source** that the full
   production fixed row roster, including constants/padding and endpoint
   multiplicities, equals the source-derived Lean certificate and its
   preprocessed commitment. The square4 finite instance is a useful
   nonvacuity check, not that universal result.
2. Derive one coherent address-to-value map and exact external feeder events
   from authenticated native main rows. Then connect the address ledger to
   Gate/Chip bridge lookup closure without assuming exact event balance as a
   premise. Account for tuple compression, denominator failures, challenge
   sampling, and the PCS/FRI error terms in the actual profile.
3. Complete compiler refinement from accepted S31 text/IR to all native
   fixed/main/interaction rows and public claims for the mixed 1..8-call
   profile. Current `AcceptedPublicFixedCells` covers a modeled direct
   functional slice; it does not prove the bounded chip lowering correct.
4. Run final kernel replay and source-binding parity after the new modules
   are frozen. Fresh fixture regeneration must remain a separate native
   diagnostic gate; neither it nor the Lean finite checks establish verifier
   acceptance or witness confidentiality.

The reviewed boundary uses `private` to omit witness values from the public
statement. Bridge endpoint values occur in committed columns; no secrecy
claim follows from this review.
