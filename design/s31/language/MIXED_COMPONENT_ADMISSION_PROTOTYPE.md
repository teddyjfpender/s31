# Mixed circuit-to-chip admission prototype

Status: **source-bound selected schedule inspection API**. This API does not
consume or produce proof bytes. The separate [experimental mixed N=3
profile](MIXED_NATIVE_N3_PROFILE.md) now proves this exact roster through a
source-embedded verifier. The existing V3 pair and V4 bounded proofs are
unchanged. This inspection path tests the scheduler boundary with two
source-distinct native AIR families that share lower-level arithmetic and
boundary code.

## Concrete program and roster

The test program applies three private four-lane `square; add_const` repeats:

```text
r0 = repeat(x, 16, square_then_add(13))
r1 = repeat(r0, 16, square_then_add(14))
r2 = repeat(r1, 16, square_then_add(15))
public sum = r2 + x
public product = r2 * x
```

The source compiler assigns call IDs `0, 1, 2` and eight input/output circuit
addresses per call. The version-1 policy assigns the existing **pair** chip
and bridge AIR sources to calls 0 and 1, then the existing **many** chip and
bridge AIR sources to call 2. All four native kinds have distinct pinned
source hashes; the pair chip accepts IDs 0–1, while the many chip accepts
IDs 0–7. The selected N=3 component order is interleaved:

| Proof index | Source kind | Main columns | Interaction columns | Constraints |
| ---: | --- | ---: | ---: | ---: |
| 0 | Bound circuit | 0–12 | 0–8 | 0–C |
| 1 | Pair chip 0 | 12–21 | 8–16 | C–C+6 |
| 2 | Pair bridge 0 | 21–29 | 16–36 | C+6–C+19 |
| 3 | Pair chip 1 | 29–38 | 36–44 | C+19–C+25 |
| 4 | Pair bridge 1 | 38–46 | 44–64 | C+25–C+38 |
| 5 | Many chip 2 | 46–55 | 64–72 | C+38–C+44 |
| 6 | Many bridge 2 | 55–63 | 72–92 | C+44–C+57 |

`C` is the selected circuit AIR's live constraint count. The full main and
interaction widths are 63 and 92 columns. The chip slots each list the
tagged chip relation; bridge slots list both the circuit Gate and tagged chip
relations. These are reviewed registry dependencies, **not** dependencies
extracted from evaluator formulas.

## What the executable admission establishes

[`direct_mixed_admission.zig`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_admission.zig)
instantiates each selected pair or many native verifier handle and checks its
live trace widths, height, degree, constraint count, preprocessed indices,
composition split, and pinned AIR source hash. It refuses a pair source at
call ID 2 and any call ID above 7.

[`inspection.zig`](../../../src/frontends/s31/runtime/mixed_boundary/inspection.zig)
reparses and recompiles the supplied S31 source without witness values using
the existing V4 inspector. It obtains canonical source node IDs, exact
compiled endpoint addresses, fixed preprocessed root, bound circuit AIR, and
the source-derived V4 manifest. It then derives the fixed mixed source-kind
policy and interleaved offsets, checks each native handle against the source
component's width, degree, constraint count, and lookup dependency list, and
hashes every call and slot under a separate prototype domain. A comparison
API reconstructs all fields from source; re-sealing a forged slot digest does
not make it admissible. Tests mutate source kind, relation ID, endpoint, native
program binding, and source constant, then require rejection.

The next inspection gate is
[`direct_mixed_schedule.zig`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_schedule.zig).
It constructs the **combined** circuit/pair/many verifier handles in the
interleaved order. It asks those live handles for column log sizes,
mask sample points, composition degree/split, and exact tree widths. It checks
every PCS lifting height against the extended column logs and records a
canonical digest of sample-point coordinates at a deterministic audit point.
This does not establish mask behavior for every verifier challenge. S31 recompiles the source,
recreates the fixed circuit and these handles, compares every slot with its
source-derived call and endpoint addresses, and hashes the complete selected
schedule under the prototype domain. Re-sealed mutations of FRI queries,
lifting height, sample width/points, native AIR source hash, and local AIR
dependency digest are rejected.

The local AIR dependency digest binds the seven-file import closure of the
pair/many chip and bridge implementations: their four tagged AIR files,
`repeated_step_chip.zig`, and both private boundary modules. Its expected hash
is pinned in the engine adapter. The selected circuit program and AIR bundle
are independently bound by the V4 source inspection; core and prover library
code is pinned by the engine revision used to build the verifier. The lookup
relation IDs remain a reviewed registry contract rather than automatically
extracted evaluator dependencies. Independent formula review is still a
release obligation.

This is a real increase in **component-source composition**: the roster
contains both pair and many native AIR implementations in one program. The
separate N=3 profile establishes proof acceptance for this exact roster in one
STARK. Neither path adds a new arithmetic function or establishes arbitrary
component interchangeability. This inspection API itself consumes and
produces no proof bytes.

## Native proof gate

A proof-backed profile now uses distinct magic, transcript and manifest
domains. Its source-embedded verifier regenerates this selected schedule
**before proof decoding** and binds the manifest digest before the first
commitment. The prover commits matching interleaved base and interaction
columns, mixes seven claimed sums in that order, and uses one lookup challenge
pair. Focused native tests accept an honest three-call proof and reject
changed source, call order, endpoint, claimed sums (including compensating
chip/bridge deltas), commitment roots, and cross-profile replay. The
inspection tests separately reject changed source kind, relation ID, and AIR
dependency hash. Independent full AIR equation review and end-to-end compiler
correspondence remain required.

The fixed-profile implementation follows this narrow sequence:

1. Freeze a new profile/version and derive one selected schedule from source,
   the AIR bundle, and live verifier handles. The schedule owns component
   order, tree widths and heights, mask geometry, lookup relation closure,
   claimed-sum indices, and source hashes. A caller-supplied projection is
   never proof authority.
2. Make the native prover fill base and interaction trees in that schedule's
   interleaved order. Use the schedule's offsets for each evaluator and the
   same challenge pair across both chip families. Reject if any emitted tree
   width differs from the selected schedule before commitment.
3. Give the verifier the source and AIR bundle first. Rebuild the schedule,
   check resource bounds and a distinct public statement, then decode proof
   bytes. Commit the new manifest digest into the transcript before the first
   tree commitment; derive quotient/PCS composition and claimed-sum order
   solely from this schedule.
4. Run honest and mutation tests in Debug and ReleaseFast, preserve existing
   V4 proof bytes, and obtain [independent admission review](../security/INDEPENDENT_REVIEW_MIXED_N3_2026-10-11.md).
   A frozen mixed proof-byte fixture and full independent pair/many lookup
   equation review remain open.

The prototype reuses V4's source-derived circuit slot as an audit anchor,
but it cannot reuse V4's grouped component manifest as the new proof
manifest: interleaving changes claimed-sum order and PCS column offsets.

The current bridge commits endpoint values without blinding. A source field
marked `private` is hidden from the public ABI, but this design makes **no
witness-confidentiality claim**.

The refreshed formal source inventory pins the mixed wrapper, engine schedule,
and engine revision. It does not contain a Lean theorem about this mixed
inspection path or the mixed
proof. The [N=3 profile](MIXED_NATIVE_N3_PROFILE.md) describes the supported
proof-byte entrypoint and its limits.

Run the prototype controls with:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-composition-admission -Doptimize=Debug -j1
```
