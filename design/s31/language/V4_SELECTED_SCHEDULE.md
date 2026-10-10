# One selected schedule for the bounded V4 proof

Status: source implementation in progress; the selected native path has not
yet passed build, proof, or proof-byte comparison after its refactor.
`direct_many_schedule.selectGeometry` selects typed manifest slots against the
live verifier handles, fixed circuit root, and PCS profile. S31 binds the
unchanged V4 manifest digest and passes the result to selected prover and
verifier adapters. Their selected branches now take column order, claimed-sum
positions, verifier tree logs, and component handles from those slots. The
legacy Plan path remains for existing engine tests; the selected adapters
project calls to a Plan only for the current fixed-circuit constructor,
witness endpoint extraction, and transcript helper signatures. This
projection is derived from the selected calls, not a second caller input.

## The authority split today

`bounded_compiled_binding.inspectMany` derives the typed manifest from
authenticated source, compiled endpoints, the selected circuit AIR, and live
chip/bridge preflight. It compares manifest entries with
`private_many_boundary.expectedRoster` and `direct_many_preflight.inspect`.
`many_native_package.verifySourceBound` repeats this before decoding a proof.
The source-pinned package accepts no caller geometry.

The engine then takes a separate `Request.plan`. Both
`direct_many_arithmetic.prove` and `verifyBorrowed` reconstruct the
preprocessed circuit, call `expectedRoster`, and independently assemble the
main tree, interaction tree, claimed sums, and prover/verifier component
arrays in three hardcoded circuit/chip/bridge passes. `fillLogs` reads that
roster; `mixProfile` and `identityHash` read the Plan. The component arrays
determine quotient coefficient order and PCS openings. Matching digests
and preflight checks protect the current bounded path, but a new component
kind would create several places where schedules could diverge.

## Selected schedule contract

Keep the S31 manifest as the source-derived, canonical public description.
Map its ordered calls and components to an engine-neutral **candidate** that
contains no proof bytes. The candidate includes source and manifest digests,
call parameters and compiled endpoint addresses, typed component source
kinds and program bindings, proof and claim indices, tree spans, trace and
evaluation logs, preprocessed indices, relation IDs, constraint counts and
offsets, fixed root, and fixed PCS profile. This is an internal typed value,
never geometry loaded from a proof or unauthenticated package field.

An engine selector validates the candidate against the pinned AIR bundle,
the compiled direct circuit, and instantiated chip/bridge handles. The
selector must reject unknown source kinds or versions, noncanonical call
IDs, a missing/duplicate/reordered slot, noncontiguous spans or coefficient
offsets, unsupported logs/degrees/relations/fixed indices, endpoint or AIR
source disagreement, and any unsupported PCS/composition geometry. S31
checks the complete program-binding digest against its source lowering;
the engine checks the call and AIR facts it can observe independently.
Offsets and widths come from the admitted kind's reviewed factory and live
AIR, with checked prefix sums; candidate numbers are equality assertions,
not allocation instructions. The selector returns a `SelectedSchedule`
containing the validated ordered slots, one canonical call list, live
geometry, PCS configuration, and transcript identities. It owns no separate
Plan. Only this selected value may enter the native prove/verify adapters.

The authenticated source and pinned AIR remain the root of authority. An
engine API cannot certify that a caller's source is authentic; the
source-pinned wrapper must construct and select the candidate internally.
The selected value is a validated in-process capability, not an external
verification key or a zero-knowledge claim.

## One consumer path

All indexed operations iterate the selected slots in proof order:

| Operation | Selected field and check |
| --- | --- |
| Fixed circuit | Derive the boundary from selected calls; check the compiled topology and fixed Merkle root. |
| Main and interaction commitments | Append each slot's columns at its checked span; check exact width and column log before committing. |
| Claimed sums | Place each component sum at its selected claim index; require a bijection over `0..1+2N`. |
| Transcript and identity | Mix the selected source/manifest digest, selected calls, fixed PCS, public words, roots, nonce, and selected ordered sums in the existing V4 order. |
| Quotient and openings | Instantiate prover/verifier handles from selected slots in that same order; check runtime handle facts against selection before calling the core engine. |
| PCS preflight | Use selected tree logs, widths, masks, composition split/degree, and fixed FRI parameters before postcard allocation or decoding. |

Challenges and claimed sums are runtime values, so the selector can build
dummy-challenge handles for preflight and later instantiate challenged
handles from the same slot constructors. The later handles must repeat
geometry and observable call, endpoint, and AIR-source checks. A selected
schedule cannot reuse a handle built for a different challenge, claim, or
witness. The V4 manifest digest includes live preflight geometry, so selection
has two phases: `selectGeometry` first supplies that geometry; S31 inserts it
into its regenerated manifest and hashes the existing typed precommitment;
`bindManifestDigest` then produces the transcript-ready selected value. This
preserves the V4 digest and proof bytes. Binding the digest is only sound in
the source-pinned caller, which checks the regenerated manifest and selected
geometry; the engine cannot authenticate arbitrary source bytes on its own.

## Minimal code change sequence

1. In the engine, add `CandidateSchedule` and `SelectedSchedule` beside
   `direct_many_preflight.zig`. Make a single bounded kind factory return
   chip/bridge dimensions and construct their handles. Move the current
   live geometry checks into `selectGeometry`, derive checked prefix sums
   from those factories, and compare every candidate entry. Keep V3 untouched.
2. In S31, make `inspectMany` map its generated manifest to the candidate
   and call `selectGeometry`, then bind the digest. Store the result in `ManyInspection`.
   Build it only after source lowering, endpoint rebinding, selected AIR
   binding, and fixed-root comparison. Retain the independent manifest
   equality check as a review guard.
3. Add `proveSelected` and `verifySelectedBorrowed` engine adapters. Replace
   their separate `Request.plan`, `expectedRoster`, `fillLogs`, column-copy,
   sum-index, and component-construction branches with selected-slot loops.
   Derive the preprocessed boundary, `mixProfile`, and `identityHash` from
   selected calls. Do not regenerate a Plan as a second input. Keep legacy
   experimental entrypoints temporarily as test adapters around selection;
   the source-pinned package must never call them.
4. Have `many_native_package` pass the selected value from `inspectMany` to
   proving and verification. Derive envelope count and header length from
   its selected slots; reject out-of-range wire counts cheaply, then compare
   them with that selected count. The source-pinned verifier must select before
   postcard decoding. Delete the duplicate runtime preflight once the new
   adapter has equal checks.
5. Remove the old V4 Plan/roster-based adapter after the native acceptance
   matrix passes. Keep `expectedRoster` only as a test oracle or a checked
   invariant inside selection, never as a second execution schedule.

This is a bounded refactor: at most 17 slots, no per-row dynamic dispatch,
and no JSON in the engine hot path. The current selected adapter revalidates
live geometry after S31 inspection because `SelectedSchedule` is a public
mutable Zig value. That intentionally retains a second witness-free
preflight. A later single-preflight optimization needs a stronger sealed
in-process API or a private adapter, not an unchecked trust in mutable
geometry. The refactor should preserve V4 wire and transcript bytes; any
intended protocol change needs a new version.

## Acceptance after the timed study

Run native N=1–8 proof/verify and one-call black-box source-pinned acceptance
in Debug and ReleaseFast. Compare the same-source transcript roots and
envelope bytes before and after the refactor where deterministic. Mutate
every sum index; swap or duplicate components; alter call order, endpoint,
kind, source binding, fixed index, degree, width, log, relation, coefficient
offset, PCS geometry, and public word. Reseal source/manifest digests for
the semantic mutations so byte-hash checks alone cannot explain rejection.
Check V3 pair proof bytes separately.

The relation-ID list still comes from a reviewed per-kind assignment in
`direct_many_preflight`, not from evaluator formula introspection. Selection
must preserve that conditional boundary; admitting a new kind requires a
separate relation/lookup review and compiler-to-AIR correspondence argument.
