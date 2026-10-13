# Lifted Merkle committed-column origin

This note connects the pinned lifted Merkle **prover's columns** to the root
and rows consumed by the native verifier. The formal statement is an ideal
complete-tree theorem. A source guard and native differential test cover the
reviewed Zig path. They do not make the installed Zig binary or BLAKE2s
collision resistance a Lean theorem.

## The row committed at a position

The prover accepts columns in caller order, validates power-of-two lengths of
at least two, and sorts references by ascending log size, breaking ties by
original column index. A leaf at lifted height `h` and position `q` absorbs
one canonical M31 word from each sorted column. If a column has log size `c`
with `1 ≤ c ≤ h`, its source index is

```text
project(h,c,q) = 2 · floor(q / 2^(h-c+1)) + (q mod 2).
```

For caller columns `[A, S, B]` with logs `[4, 2, 4]` and lifted height `5`,
the Merkle row at position `31` is `[S[3], A[15], B[15]]`. In particular,
`S` comes first even though it is caller column 1. At position `23`, the row
is `[S[3], A[11], B[11]]`. The short column keeps the low circle bit as its
coset index is reduced.

The lifted prover first hashes these rows at natural height `4`, replicates
the finished leaf layer to height `5`, and hashes pairs of children upward.
The reviewed S31 CPU backend names `MerkleProverLifted` as its tree type;
the PCS revision calls `liftTo` before publishing the root. Direct
`commitLifted` performs the same expansion. The new native test checks the
CPU backend, direct commitment, and post-commit lift, including the
constant-column fast path. It builds an independent 32-leaf tree from the
formula above and compares **every** retained prover leaf and parent, not
just the final root.

The direct circuit integration also has compact-storage **tiled** and
**streaming** commit routes before that lift. The compact origin fixture below
tests both routes and the retained columns on a mixed-height S31 profile.
Their all-input equivalence to the complete-tree model remains part of P06.

## What Lean proves

[`MultiproofCommittedColumns.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofCommittedColumns.lean)
defines `layerHash(0,q) = leafHash(projectedRow(h,q,columns))` and
`layerHash(d+1,q) = parentHash(layerHash(d,2q), layerHash(d,2q+1))`.
`committedRoot` is `layerHash(h,0)`. `committedPath` selects the sibling at
each level using the same low-bit child order as the verifier.

`committedOpening` proves that **every** `q < 2^h` has a path of length `h`
that reconstructs this one root. The proof works for any leaf and parent
hash functions. It does not need an injective hash.

`verifyRaw_refines_constructed_commitment` combines that result with the
raw-query decoder model. If a captured opening verifies against this computed
root, its row equals the projected committed row unless those two concrete
openings exhibit a leaf-hash or parent-hash collision. The local collision
assumption is explicit; it does not assert global injectivity of a 256-bit
hash. `verifyRaw_all_rows_refine` applies the same statement to every caller
slot, including repeated positions.

For a hand-sized example, use one height-1 column `[10,11]`, a leaf hash
equal to its row sum, and `parentHash(left,right)=100·left+right`:

```text
leaf 0 = 10             leaf 1 = 11
          \             /
             root = 1011

opening at 0: row [10], sibling [11], 100·10+11 = 1011
opening at 1: row [11], sibling [10], 100·10+11 = 1011
```

The Lean file evaluates this root and both paths. The raw-query model uses
the same numbers and caller queries `(1,[11]), (0,[10]), (1,[11])`, returning
paths `[10], [11], [10]` in caller order.

## Native evidence and remaining boundary

[`pcs_fri_prover_column_origin_native.zig`](../../../formal/s31/tests/pcs_fri_prover_column_origin_native.zig)
uses the actual pinned `MerkleProverLifted(Blake2sPlainMerkleHasher)` for
natural-height, explicit-lift, CPU-backend, and constant-column trees. It compares every
node to an independently projected and hashed tree, asks the actual prover
for unsorted duplicate openings, checks every queried value against the
source columns, then checks the verifier's captured paths against the
independent tree. A changed projection, changed verifier column logs, and a
changed public root each fail verification without publishing a capture.

[`pcs_fri_prover_origin.py`](../../../scripts/s31_formal_lib/pcs_fri_prover_origin.py)
pins the reviewed source stages: column sort, leaf builders including the
four-way path, final lift, parent construction, CPU backend and PCS lift
handoff, compact commit routing, decommit projection, and verifier row
assembly. Mutation tests show that
removing or changing representative stages fails the guard. This is a source
change detector, and the native test samples a finite set of trees.

### Compact tiled and streaming fixture

[`pcs_fri_compact_column_origin_native.zig`](../../../formal/s31/tests/pcs_fri_compact_column_origin_native.zig)
uses the S31 `Blake2sM31MerkleChannel`, configured CPU backend, one-bit
blowup, source column log sizes `[9,3,9,5,7,8]`, compact threshold `6`, and
lifted height `11`. Thus the first extended column has log size `10`; the
second has log size `4` and keeps its evaluation. The five larger columns
retain coefficient buffers and discard their extended evaluations. The
fixture checks both the borrowed and owned tiled routes, plus the streaming
route, including transcript bytes.

The expected value at every extended-domain position is computed by
**barycentric evaluation of the original source column** at the circle-domain
point. That calculation does not read the tiled blocks, streaming buffers,
retained coefficients, or opening code. It checks every reconstructed
coefficient polynomial against those expected values and checks the small
retained evaluation directly. It then projects the expected values to every
lifted row, hashes every leaf and parent independently, and compares every
prover node. Finally it checks unsorted duplicate openings and all captured
siblings against this complete tree. A changed root, queried value, or
verifier column-log order is rejected.

For one row `q`, the committed input is the ordered list
`[C1[project(11,4,q)], C3[project(11,6,q)], C4[project(11,8,q)],
C5[project(11,9,q)], C0[project(11,10,q)], C2[project(11,10,q)]]`.
The index is in the **extended** column, whose values came from the source
polynomial. This is why an opening from a compact coefficient buffer must
reconstruct exactly that extended value; merely comparing two compact
committers would not establish source-column origin.

The remaining P06 bridge must prove the relevant Zig paths refine the Lean
tree for all valid inputs, including tile boundary, pruned-layer, and cached
tree cases; connect the reviewed source to the installed binary; and provide
a quantitative binding/collision bound for the pinned plain BLAKE2s layout.
The fixture covers one finite shape and only the direct uncached CPU route.
Until those obligations close, P06 is open and native proven security bits
remain unset.
