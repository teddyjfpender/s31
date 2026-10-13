# PCS/FRI proof boundary

The Lean files in this directory establish small parts of the native PCS/FRI
argument. They are imported by `S31.Gadgets`, so normal builds and axiom
audits include their theorems.

## One lifted Merkle opening by hand

Suppose a two-level tree authenticates an opened row `R` at leaf index `1`.
Let `L = leafHash(R)` and let its two siblings, from the leaf upward, be
`S₀` and `S₁`. The verifier computes:

```text
position = 1       (odd):   P = parentHash(S₀, L)
position = 1 / 2 = 0 (even): root = parentHash(P, S₁)
```

[`MerkleOpening.lean`](MerkleOpening.lean) expresses this as `pathRoot` and
records the two actual compression inputs with `pathInputs`. Its theorem
`conflicting_openings_produce_collision` says that if a different row `R'`
is also accepted at the **same root and leaf index**, with a path of the same
height, then one of these concrete events must occur:

1. `R ≠ R'` but `leafHash(R) = leafHash(R')`; or
2. two different ordered child pairs from the compared paths have the same
   `parentHash` output.

No global injectivity assumption is made. A finite cryptographic hash cannot
be globally injective on every possible input. The theorem produces a
collision witness on the compared openings, which is the form needed for a
cryptographic reduction.

For a lifted tree, the row at index `q` contains one value from each column.
`projectedPosition` models the native index map. For a raw query on a
`2^k` domain and a column on a smaller `2^l` domain, it uses

```text
q_l = 2 * floor(q / 2^(k-l+1)) + (q mod 2).
```

For `k=5`, `l=3`, `q=7`, this selects column index `1`. The low bit keeps
the conjugate-circle half. `projectedRow` gathers these values in an agreed
column order. `accepted_row_refines_projected_commitment` says an accepted
opening of this committed row and an accepted opening of a different native
row under the same root and index produce one of the witnessed collisions.

The pinned native test in `deps/stwo-zig/src/core/vcs_lifted/verifier.zig`
replays a captured two-level path to its root and checks rejection after
changing the row, sibling or queried index under that same root. The native
projection test in `deps/stwo-zig/src/core/pcs/utils.zig` checks the
smaller- and larger-domain mappings against canonical circle-group indices.

## From compressed proof to full paths

The native verifier sorts and deduplicates query indices, then processes each
layer in ascending index order. A chunk is either two adjacent siblings from
the current frontier, or one node plus a supplied witness hash. It records
the opposite child as each queried node's next captured sibling. The
[`MultiproofCapture.lean`](MultiproofCapture.lean) model represents these as
`paired` and `witnessed` chunks and computes the same per-query edge walk.

Here is the two-query example checked as executable Lean examples. Let the
four leaf hashes be `L₀,L₁,L₂,L₃`; query positions `1` and `3`.

```text
Layer 0 frontier: (1,L₁), (3,L₃)
  (1,L₁) consumes witness L₀  → (0,P₀₁), captures sibling L₀
  (3,L₃) consumes witness L₂  → (1,P₂₃), captures sibling L₂
  where P₀₁=H(L₀,L₁), P₂₃=H(L₂,L₃)

Layer 1 frontier: (0,P₀₁), (1,P₂₃)
  paired siblings              → (0,root), root=H(P₀₁,P₂₃)
  query 1 captures P₂₃; query 3 captures P₀₁

Captured path for query 1: [L₀,P₂₃]
Captured path for query 3: [L₂,P₀₁]
```

`follow_replays` proves for any successful modeled chunk sequence that its
captured path recomputes the final hash, has exactly one sibling per layer,
and ends at index `floor(q/2^height)`. The native range guard introduced in
stwo-zig PR #244 rejects `q ≥ 2^height`, so the modeled final index is zero.
`successful_capture_is_accepted` feeds that full path into the previous
Merkle-opening predicate; `successful_capture_refines_projected_row` then
applies the witnessed-collision theorem to identify the opened row.

[`MultiproofDecoder.lean`](MultiproofDecoder.lean) adds a deterministic
one-layer decoder for the sorted frontier. It makes the native XOR sibling
test equivalent to an even index followed by its odd successor. For any
successful decode with strictly increasing input indices,
`buildLayer_structure` proves that chunks cover the input frontier exactly,
the emitted parents are precisely the chunk parents, the consumed hashes are
exactly a prefix of the supplied witnesses, and paired chunks start at even
indices. `decoded_layer_has_edge` proves every input node has an event in
`MultiproofCapture.layerEdges`; `decoded_layer_follows` selects that event
through the existing `follow` function, checks the captured one-layer
parent hash, and proves that the reached node is in the emitted parent
frontier. Executable Lean examples cover a paired branch, two sparse
witness branches, a short witness, and a surplus witness suffix.

The [pinned source control](../../../../../scripts/s31_formal_lib/pcs_fri_capture.py)
now checks sorting, deduplication, chunk advancement, witness cursor, and
ancestor matching in addition to the existing root and publication checks.
Mutation tests require each changed stage to be rejected. These checks pin
source structure; they are not a semantics or refinement proof for Zig.
The [focused native regression](../../tests/pcs_fri_decoder_native.zig) runs
against the pinned `stwo_core` module. It authenticates an unsorted input
with a duplicate through the paired and witnessed branches, checks the
captured sibling paths, and requires short, extra, or changed witnesses and
inconsistent duplicate rows to fail without publishing a capture. Run it
from the repository root with:

```sh
zig test -O ReleaseSafe --dep stwo_core -Mroot=formal/s31/tests/pcs_fri_decoder_native.zig -Mstwo_core=deps/stwo-zig/src/core/mod.zig
```

## One FRI fold's field algebra

[`FoldAlgebra.lean`](FoldAlgebra.lean) defines the inverse-butterfly pair
operation `(left + right) + α (left - right) / x`. For affine evaluations at
`x` and `-x`, `pairFold_affine` proves that this equals `2(c₀ + α c₁)` when
`x ≠ 0`. The factor two reflects the native inverse butterfly, which does
not divide by two. `circleAccumulate_affine` adds the native `α²`-weighted
previous value, and `challengeAt_succ` proves that repeated squaring gives
successive powers `α^(2^step)`.

The [native algebra regression](../../../tests/pcs_fri_fold_native.zig) compares
the pinned engine's circle-to-line fold and four line halvings with a separate
formula that never calls the engine butterfly or single-step fold. It uses
bit-reversed native domain coordinates and explicit challenge powers. The
[source guard](../../../../../scripts/s31_formal_lib/pcs_fri_fold.py) binds
the inverse butterfly, coordinate inversion, challenge squaring, sparse fold
helpers, and both verifier call sites; mutation controls reject changes to
each critical step. Run the native regression from the repository root with:

```sh
zig test -O ReleaseSafe --dep stwo_core -Mroot=formal/s31/tests/pcs_fri_fold_native.zig -Mstwo_core=deps/stwo-zig/src/core/mod.zig
```

## What remains to join

The Lean decoder model starts with a strictly sorted frontier and a committed
projected row. It proves the deterministic one-layer decode inside that model.
A machine-checked refinement of Zig's sorting, deduplication, witness cursor
and capture copy loops to that decoder remains open, as does a proof that the
tree was built from precisely those columns in that order. It
does not prove BLAKE2s collision resistance, Fiat–Shamir sampling, the
nonzero-coordinate condition for all production domains, all FRI fold inputs,
low-degree proximity, or a whole-proof security bound. See the
[published-bound audit](../../../../../design/s31/security/PCS_FRI_PUBLISHED_BOUND_AUDIT.md)
for the parameter and reduction gaps.
