# Mixed square/add and Mix4 source admission V2

Status: **source-only draft**, 2026-10-11. This module issues no verification
key, does not select an AIR, and accepts no proof bytes. It lives alongside
`language/bounded_call_admission.zig`; the existing V1 admission, V4 bounded
proof envelope, transcript, and verifier are unchanged. The separate
`language/bounded_call_admission_v2.zig` API returns an in-memory plan with
`schema_version = 2` so future native wiring cannot silently treat a V1
square/add call as a coupled Mix4 call.

## The two admitted transitions

Each call acts on four M31 lanes. With `c` a canonical field element:

| Source body | V2 kind | One round |
| --- | --- | --- |
| `square; add_const(c)` | `square_add` | `yᵢ = xᵢ² + c` |
| `square; add_const(c); mix4` | `square_add_mix4` | `tᵢ = xᵢ² + c`; `yᵢ = tᵢ + Σⱼ₌₀³ tⱼ` |

The second transition couples all four lanes. It requires a distinct native
AIR and relation domain. Reusing the per-lane square/add chip would fail to
constrain the sum. A normalized source example is:

```json
{
  "version": 1,
  "name": "coupled_once",
  "inputs": [{"name": "x", "kind": "m31", "length": 4, "visibility": "private"}],
  "nodes": [
    {"name": "mixed", "op": "repeat", "lhs": "x", "rounds": 32,
     "body": [{"op": "square"}, {"op": "add_const", "constant": 7}, {"op": "mix4"}]},
    {"name": "claimed", "op": "sum_lanes", "lhs": "mixed"}
  ],
  "assertions": [],
  "public_outputs": ["claimed"]
}
```

The source plan records call ID 0, canonical input node ID 0, canonical repeat
node ID 1, kind `square_add_mix4`, 32 rounds, and constant 7. The public
output is canonical node ID 2, one M31 word. This is a compiler plan, not a
claim that a proof of that output exists. `mix4` means adding the same
four-lane sum to each lane; it is not a lane permutation or an unconstrained
host computation.

## Admission policy

The module parses at most 1 MiB of normalized source. It accepts version-1
transparent programs with one to eight private `m31[4]` inputs and one to
eight canonical repeat calls. Each repeat has 16–32768 power-of-two rounds;
the checked sum of rounds is at most 2¹⁸. It also limits canonical IR to
65,536 nodes, public output names to eight, and their total width to nine
M31 words. Assertions, public inputs, a declared public-record ABI, and
other node kinds are outside this draft profile.

Call IDs follow literal source order. Every source repeat must survive as
its own canonical node in the same order; folding or deduplicating two source
calls into one node fails admission. Each input to a call must be a private
input node or an earlier repeat node. Arithmetic between calls may be
computed in the surrounding circuit but cannot feed a chip until a
constrained scalar extraction path exists. Every repeat and every declared
input must be reachable from an admitted public result. A public result
cannot be an exposed input or raw repeat endpoint; it must be a later
arithmetic node such as `sum_lanes` or `add_const` that depends on a call.

The returned plan includes the canonical IR SHA-256 and, for each call, its
kind, canonical source/input IDs, round count, and constant. It contains no
witness, scalar circuit address, AIR selector, component manifest, PCS
geometry, or source-derived verifier key. Two source texts with matching
arithmetic can canonicalize to the same IR; native admission must still pin
the literal source and normalized compiler version according to its own
versioned key protocol.

## Work needed before native admission

1. Teach value and topology compilation to materialize **four constrained
   scalar addresses** for every input and output of either chip kind. The
   packed four-lane vector must be extracted to those scalars and repacked
   without a free witness choice. Compare both compiler modes and reject an
   address with no unique producer, a reserved public slot, or missed
   multiplicity.
2. Construct a typed roster from the selected AIR handles: one circuit,
   every call's distinct chip kind, and each matching tagged bridge. Bind
   kind, source/call IDs, constants, rounds, endpoint addresses, relation
   domains, component order, geometry, claimed sums, preprocessed root, and
   native program digests into a **new** manifest and transcript version.
   The existing V1/V4 manifests cannot identify heterogeneous Mix4 calls.
3. Make the native verifier reconstruct that roster from embedded source and
   official AIR constructors before decoding a versioned proof envelope.
   Check all PCS/FRI settings and complete commitment/opening order against
   live handles; reject unknown kinds, changed source, proof bytes, claims,
   or trailing bytes. Prover-only plan validation is insufficient.
4. Run focused native honest and mutation proofs, review the full lookup and
   Fiat–Shamir soundness budget for the new relation, and measure whole-prover
   cost against the generic circuit on frozen, held-out Mix4 workloads.

The engine's experimental `mix4_coupled_*` primitives are a separate draft.
Their scalar boundary, selected component roster, and proof admission have
not been connected to this source plan. The focused **source-only** test step
is `zig build --build-file src/frontends/s31/build.zig test-mixed-call-source-v2`;
its existence does not imply the native proof gates above have passed.
