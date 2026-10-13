# PCS/FRI proof boundary

The Lean files in this directory establish small parts of the native PCS/FRI
argument. They are imported by `S31.Gadgets`, so normal builds and axiom
audits include their theorems.

[`ConservativeEnvelope.lean`](ConservativeEnvelope.lean) proves an arithmetic
limit of one **published upper-bound expression**: in Circle STARKs Remark 26,
its leading commitment/folding term exceeds `2^-96` whenever the candidate
degree parameter has at least 256 rows, blowup is at least 2, Johnson
multiplicity is at least 3, and batch width is at least 1. The proof uses a
lower floor for `sqrt(blowup)` and exact arithmetic. It does not prove that
the native protocol matches the paper or that an adversary can succeed with
that probability.

The [BCS transcript epoch model](BcsTranscriptEpoch.lean) proves that a
verified nonce starts a fresh query-input epoch with nine distinct pre-hash
messages for the sealed 70-query schedule, conditional on an injective u32
counter encoding. The [native and independent-model replay](../../../../../design/s31/security/PCS_FRI_BCS_TRANSCRIPT_REFINEMENT.md)
checks the direct Gate's actual Blake2s-M31 bytes and challenge order. These
results leave the cryptographic Fiat–Shamir/BCS reduction open.

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
`projectedPosition_compose` proves that projecting from a lifted tree to a
natural-height tree and then to a column equals direct column projection for
arbitrary `column ≤ tree ≤ lifting` heights. The sealed gate height-21 case is
`gate21_tree_column_position`. The
[`PCS_FRI_GATE_LIFTED_PROJECTION.md`](../../../../../design/s31/security/PCS_FRI_GATE_LIFTED_PROJECTION.md)
diagnostic records key-derived column logs and native source guards. This
integer-index identity does not establish that Zig's opened values come from
the projected committed column oracles.

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

The [finite native decoder refinement check](../../../../../design/s31/security/PCS_FRI_MULTIPROOF_DECODER_REFINEMENT.md)
goes further: an independent complete eight-leaf tree supplies every one of
the 255 nonempty query subsets. The test compares all three captured sibling
levels for each query against the original tree, including reverse query order
and a duplicate, under S31's plain BLAKE2s Merkle hasher. It also checks the
log-size ordering of a two-column leaf and five malformed inputs. This covers
the pinned native implementation on that finite domain; a general Zig
semantics theorem, committed-column origin and collision bound are still
required for P06.

## Packed FRI leaves bind the modeled layer oracle

[`FriMerkleBinding.lean`](FriMerkleBinding.lean) identifies the exact leaf for
an absolute FRI evaluation position `a`: leaf index `a / 2^leafLog` and slot
`a % 2^leafLog`. It defines the leaf row by taking consecutive evaluations
from a fixed putative oracle. For each queried subset slot, it assumes the
native row and that committed-oracle row have accepted paths at the same root,
height, and leaf index. The existing Merkle collision reduction then proves
the rows equal unless those particular openings witness a leaf or parent hash
collision. The row-slot equation gives the equality needed by
`OperationalExtraction.oracleBoundLayer`. Induction supplies
`oracleBoundSchedule` for any layer count and partial final fold; the
conditional composition theorem joins this with raw DEEP answer custody and
operational admission to derive modeled FRI acceptance.

The native-success implication to these `authenticatedSlot` certificates is
still an explicit premise. In particular, Lean has not extracted the Zig
`merkle_queries.build` row materialization, `verifyWithPathCapture` control
flow, or `buildFriLayerQueryCapture` suffix copy into the model. The committed
tree must actually be built from the fixed oracle rows. BLAKE2s collision
resistance, Fiat–Shamir sampling, and FRI proximity also remain unproved.
The [source guard](../../../../../scripts/s31_formal_lib/pcs_fri_merkle_binding.py)
pins the packed coordinate order, subset-to-leaf index, upper path suffix, and
root check; seven mutations must fail. The [native regression](../../../tests/pcs_fri_merkle_binding_native.zig)
rehashes every captured slot of an honest two-layer proof under the actual
S31 Blake2sM31 transcript profile. Its first layer has packed width-four
leaves and its partial inner fold uses unpacked leaves. Changed values,
siblings, and group positions fail independent root replay. Run the focused
checks with:

```sh
bash formal/s31/tests/run_pcs_fri_merkle_binding_native.sh
python3 -B -m unittest scripts.tests.test_pcs_fri_merkle_binding -v
cd formal/s31 && lake build S31.Gadgets.PcsFri.FriMerkleBinding
```

### Post-verification FRI Merkle admission

S31's [`fri_merkle_admission.zig`](../../../../../src/frontends/s31/runtime/fri_merkle_admission.zig)
now independently rehashes every raw FRI subset after the core verifier and
operational capture gate succeed, before any of the four generic runtime
verifier paths returns success or publishes a converted witness. It checks the transcript
query position at each layer, the exact packed or unpacked row shape, each
QM31 value's four M31 coordinates in native order, the complete subset
subtree, every captured upper sibling, and equality with the layer's recorded
commitment. Malformed dimensions and out-of-domain positions reject. An
honest S31 Blake2sM31 proofs with fold steps two and four, each with a packed
first layer and an unpacked partial inner fold, pass; changing a value,
sibling, group position, commitment, or
path length rejects. The [source guard](../../../../../scripts/s31_formal_lib/pcs_fri_merkle_admission.py)
pins the checker, both native layer-packing choices, proof-root capture, and
all four generic call sites, with fourteen hostile mutations. The SHA
release verifier paths use a separate shared replay gate described in the
[SHA release capture note](../../../../../design/s31/security/SHA_RELEASE_CAPTURE_ADMISSION_2026-10-13.md).
Both families still have open P04/P05/P06 theorem obligations.

[`FriLeafEncoding.lean`](FriLeafEncoding.lean) proves that flattening a list
of QM31 values into their `(a,b,c,d)` M31 coordinates is injective. Thus a
leaf collision on unequal QM31 rows is a collision on distinct encoded
M31 rows, conditional on the native hasher receiving that encoding. This
remains a source-pinned correspondence, not a formal execution proof.

The new runtime gate gives executable evidence for the native-opening side of
`authenticatedSlot`; a Lean proof that Zig success implies that relation is
still open. The committed opening for a fixed putative oracle, BLAKE2s
collision resistance, Fiat–Shamir sampling, and FRI proximity remain explicit
premises. The proven-profile preflight still fails closed.

## One DEEP quotient row by hand

For a sampled point with y-coordinate `s` and its conjugate with y-coordinate
`s'`, let a column's two sampled values be `v` and `v'`, and let `α` be its
random mixing weight. The native line coefficients are

```text
a = α(v' − v)
c = α(s' − s)
b = α(v(s' − s) − (v' − v)s)
```

At a queried circle row `(x,y)` with opened column value `w`, this column's
line residual is `c w − (a y + b)`. Substituting `(s,v)` or `(s',v')` makes
the residual zero. For a numeric illustration over the integers, take
`s=2`, `s'=5`, `v=7`, `v'=11`, `α=3`. Then `a=12`, `c=9`, `b=39`:
the residual at the first sample is `9·7−(12·2+39)=0`, and at the conjugate
sample it is `9·11−(12·5+39)=0`. Field arithmetic uses the same identities.

For several columns sampled at the same point, native code first sums each
`c·w`, and separately sums the `a` and `b` coefficients. The batch numerator
is `Σ(c·w) − ((Σa)y + Σb)`. The
[`DeepQuotientAlgebra.lean`](DeepQuotientAlgebra.lean) theorem proves this
equals the sum of individual line residuals. The denominator for the sample
point `(prx+j·pix, pry+j·piy)` and queried base-circle point `(x,y)` is
`(prx−x)piy − (pry−y)pix`. The native workspace uses the equivalent expanded
form `prx·piy−pry·pix−x·piy+y·pix`; a Lean theorem equates the two. Native
batch inversion rejects a zero denominator, and the Lean cross-multiplication
theorem assumes exactly that nonzero condition.

The [source contract](../../../../../scripts/s31_formal_lib/pcs_fri_quotient_algebra.py)
checks these expression sites, sample-value and random-weight wiring, the
per-column contribution plan, the zero-rejecting CM31 inversion path, and
the final quotient accumulation. The tests mutate each of those paths and
require rejection. This gives local algebra
and source custody. It does not prove Zig operational semantics, that the
opened `w` comes from the committed oracle, the batched polynomial degree,
or the published OODS/DEEP soundness theorem. P05 remains open.

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

## Authenticated layer transitions and the terminal check

The [native layer regression](../../../tests/pcs_fri_layer_native.zig) checks
width-four sparse reconstruction across three query groups against an explicit
queried-value/witness map, including witness count and bit-reversed domain
indices. It then generates a small affine circle column with one inner FRI
layer and replays
the pinned verifier with the same transcript. The honest proof passes. A
changed first queried value fails first-layer authentication; changing the
first folding challenge after transcript replay fails authentication of the
next layer's queried value. An extra inner-layer witness value fails exact
witness consumption. Changing the final polynomial coefficient fails its
queried evaluation check, and an oversized terminal polynomial fails the
degree check during commitment replay. The first layer uses two folds; the
inner layer uses the remaining one fold.

The [layer source guard](../../../../../scripts/s31_formal_lib/pcs_fri_layer.py)
binds query/witness reconstruction, Merkle verification, current-to-next
query and value updates, layer schedule, and the terminal degree and
evaluation gates. Mutation controls reject removal or rewiring of the
critical stages. Formal CI runs the test with the pinned prover, CPU backend,
and verifier modules:

```sh
bash formal/s31/tests/run_pcs_fri_layer_native.sh
python3 -B -m unittest scripts.tests.test_pcs_fri_layer -v
```

This is an adversarial native regression and source contract. It does not
establish a machine-checked refinement of the full verifier, prove that all
opened rows are low degree, or give a FRI proximity bound.

The [independent terminal evaluator](../../../../../design/s31/security/PCS_FRI_OPERATIONAL_TERMINAL_REFINEMENT.md)
strengthens the post-verification capture gate: it reduces adjacent terminal
coefficients with the native basis factors, independently of the verifier's
pending-stack `LinePoly.evalAtPoint` implementation. A hand-calculated
four-coefficient example, randomized differential checks, raw-slot capture
tests, and source mutations cover the evaluator. The gate reuses its scratch
buffer across raw queries. The Zig-success-to-Lean operational extraction
premise remains open.

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
