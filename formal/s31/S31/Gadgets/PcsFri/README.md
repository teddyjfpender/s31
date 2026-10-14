# PCS/FRI proof boundary

The Lean files in this directory establish small parts of the native PCS/FRI
argument. They are imported by `S31.Gadgets`, so normal builds and axiom
audits include their theorems.

[`NativeM31Arithmetic.lean`](NativeM31Arithmetic.lean) proves the integer
arithmetic in the engine's scalar M31 and four-lane AArch64 paths. For every
`u64` input, two 31-bit folds and the wrapping unsigned minimum return the
canonical residue modulo `p=2³¹−1`; for a product of canonical operands, one
fold suffices. Scalar add/sub and AArch64 vector add/sub/mul lanes agree with
the same M31 result. The proof also bounds the precast values below `2³²`,
the scalar add/sub intermediates below `2³²`, and the doubled product below
`2⁶³`, excluding signed `SQDMULH` saturation for canonical operands. The
[source pin](../../../../../scripts/s31_formal_lib/pcs_fri_native_m31_arithmetic.py)
checks thirteen reviewed Zig function bodies and has twelve hostile mutation
controls. The correspondence depends on Zig's specified wrapping, vector
lane, and AArch64 instruction semantics. `fromU32Unchecked` can create a
noncanonical value; all add/sub/mul theorems require canonical operands, so
native callers still need a checked boundary. This proof does not establish
the PCS/FRI soundness bound or validate the Fiat–Shamir transcript.

[`OodRationalMap.lean`](OodRationalMap.lean) proves the algebra of the native
seed-to-circle formulas over any field of characteristic other than two:
for a regular seed `t`, the output lies on the circle and `t` is recovered
from its coordinates by `y/(1+x)`. Conversely, every circle point with
`1+x ≠ 0` has exactly one regular preimage. `rationalCircleEquiv` packages
this exact image as an equivalence of types; in a finite field, a uniform
regular seed therefore gives a uniform point on this image. A field
embedding also preserves both coordinates, so a seed in an embedded
subfield stays in that subfield. The
`guardedRationalCircleEquiv` theorem further shows that any guard depending
only on the output y-coordinate preserves this one-to-one map: each accepted
circle point has exactly one accepted seed. Applying it to CAS05's concrete
`y.c1 != 0` check still requires the QM31 coordinate and inverse refinement.
The
[pinned OOD geometry audit](../../../../../design/s31/security/PCS_FRI_OOD_SEED_GEOMETRY.md)
counts the exceptional and subfield seeds for the current native field sizes.
These results do not prove how the native transcript distributes seeds, a
Zig-to-Lean refinement, or the PCS soundness bound.

[`ConcreteCircleCount.lean`](ConcreteCircleCount.lean) counts the actual
modeled CM31 and QM31 affine circles using the rational map and its one
exceptional point. It constructs an injective embedding of the CM31 circle
into the QM31 circle and proves that the complement has exactly
`q⁴−q²` points for `q=2³¹−1`. The already-proved CM31 guard accepts
`(q²−1)²` seeds, leaving a cardinality difference of `q²−1`.
These are the cardinalities of concrete modeled fields and a concrete set
difference. [`GuardedCircleImage.lean`](GuardedCircleImage.lean) proves that
the modeled successful rational-map image lies in that complement; the
field-coordinate count bridge is in [`OodGuardFieldCount.lean`](OodGuardFieldCount.lean).
None of these results proves a two-point OOD bad-set bound or the adaptive
transcript draw uniform.

[`OodAcceptedSupport.lean`](OodAcceptedSupport.lean) checks the exact M31
arithmetic for the experimental paired verifier's `y.c1 != 0` early guard.
Its passing support is `(q²−1)²`, smaller than the paper's `q⁴−q−2` OOD
set; conditioning a fixed bad event can inflate its mass by the exact factor
`(q⁴−q−2)/(q²−1)² < 1+2⁻⁶⁰`.
[`OodGuardFiniteCount.lean`](OodGuardFiniteCount.lean) proves the rejected
regular-seed count `2Q−3` and accepted count `(Q−1)²` for a finite lower
field of size `Q`, assuming a nonsquare tower parameter and a square root
of `−1` in that lower field. The modeled CM31 pair has size `q²`, a square
root of `−1`, and a nonsquare `2+i`; the field instance below instantiates
the generic count. Native Zig refinement is still needed.
Native seed uniformity and adaptation to the published OOD theorem remain
separate obligations. [`PairedDenominator.lean`](PairedDenominator.lean)
proves the local nonvanishing step: if the QM31 point has circle coefficient
equations over CM31, its quadratic-extension parameter is nonsquare, and its
`y.c1` component is nonzero, then the exact determinant used by CAS05's
own-quotient formula is nonzero at **every** base-circle row. The theorem is
uniform in the row, including rows the prover did not open. A rational
counterexample shows why nonsquareness is essential; a base-field point
shows why the native `y.c1` guard matters. Proving the native tower parameter
is nonsquare is reduced to an explicit pair calculation: quadratic reciprocity
proves `5` is nonsquare in M31, so no CM31 coordinate pair can square to
`2+i` under the stated `i²=-1` multiplication. Deriving the circle
coefficient equations from the Zig point type, matching the actual CM31 pair
arithmetic, and showing the channel enforces the guard are still refinement
steps.

[`PairedTowerCircle.lean`](PairedTowerCircle.lean) models the two coefficients
of a QM31 point over CM31. Its square operation is
`(x₀ + u x₁)² = (x₀² + d x₁²) + u(2x₀x₁)`, with `u²=d=2+i` in the native
tower. The model derives both circle coefficient equations from a single
pair-valued circle equation and composes them with the previous theorem.
Thus an accepted *modeled* circle point with nonzero `y.c1` has a nonzero
quotient denominator at every base-circle row. A general Zig-to-Lean field
arithmetic refinement and the guarded sampler correspondence are still open.
The full [CAS05 theorem ledger](../../../../../design/s31/security/PCS_FRI_CAS05_THEOREM_BRIDGE.md)
lists the remaining theorem joins.

[`NativeTowerFormulas.lean`](NativeTowerFormulas.lean) checks the CM31
Karatsuba multiplication, CM31 square, multiplication by `2+i`, and QM31
square, including its base-field fast path, against schoolbook formulas over a
commutative ring. It also exposes
the four base-field equations entailed by the native-shaped circle test.
The formal gate pins the corresponding Zig function bodies and OOD rational
map call site. These checks still assume that native M31 operations implement
field arithmetic and do not constitute a Zig operational-semantics proof.
[`ConcreteCM31Tower.lean`](ConcreteCM31Tower.lean) gives the modeled M31
coefficient pair exactly `p²` elements, checks that its imaginary unit
squares to `-1`, and specializes the prior nonresidue result to show that
no modeled pair squares to `2+i`. This coefficient model is not identified
with the compiled Zig representation.

[`CM31FieldInstance.lean`](CM31FieldInstance.lean) now transports the field
structure from the AIR formalization's quadratic algebra to the modeled CM31
coefficient pair. It proves that transported addition, multiplication, and
squaring equal the coefficient formulas used by the native-shaped model. In
this field, `i²=-1` and `2+i` is nonsquare. The generic finite count therefore
specializes without free field assumptions: with `p=2147483647` and lower
field size `Q=p²`, precisely `2Q-3` regular seeds fail the upper-coordinate
guard and `(Q-1)²` pass. The
modeled circle equation and `y.c1 ≠ 0` also imply a nonzero quotient
denominator at every base-circle row. This does not prove the compiled Zig
operations implement the modeled field, nor that Fiat–Shamir samples seeds
uniformly from it.

[`QM31FieldInstance.lean`](QM31FieldInstance.lean) transports the field laws
from the AIR's four-coordinate quadratic tower to the native-shaped QM31
coefficient structure. Its addition, one, and square agree with the explicit
native-shaped formulas. Consequently, a field-level `x²+y²=1` circle equation
implies all four coefficient equations used by the OOD argument. This is an
algebraic bridge between models; compiled Zig execution and the channel's
sampling distribution remain separate obligations.
The `denominator_ne_zero_of_field_circle` theorem now converts that same
modeled field circle equation into the paired quotient denominator guarantee
for every base-circle row, assuming the sampled point has `y.c1 ≠ 0`.

[`NativeTowerInverse.lean`](NativeTowerInverse.lean) proves the checked
quadratic inverse formula for both modeled native towers. A nonzero CM31
coefficient pair has denominator `a²+b² ≠ 0`; a nonzero QM31 pair over the
modeled CM31 field has denominator `c₀²−(2+i)c₁² ≠ 0`. Multiplying each
modeled inverse by its input gives one. The formal source guard now pins the
corresponding Zig zero checks, denominators, `2+i` multiplication and returned
conjugate coefficients. Native M31 execution and compiled inverse behavior
are still separate refinements.

[`ShortTerminalGeometry.lean`](ShortTerminalGeometry.lean) checks the exact
shape of the experimental cascade against S-two's variable-round Protocol 3.
With largest domain `2^k`, blowup `2^β`, and `H` folds, the published indices
are `n=k−β` and `r=H−1`. The plain terminal has `2^(k−H−β)` coefficients on
`2^(k−H)` points. Thus the 8-fold, `k=22`, `B=2` example has 8192
coefficients on 16384 points and satisfies the published terminal shape.
The published theorem still needs a proof that CAS05's authenticated values,
challenge timing, and fold operations implement its Protocol 3 relation.

[`M31RejectionSampler.lean`](M31RejectionSampler.lean) proves the exact
two-preimage arithmetic of the pinned BLAKE2s channel's 32-bit word filter:
for each `r < p`, the accepted words reducing to `r` are exactly `r` and
`r+p`, and these words are distinct. The
[source-bound sampler audit](../../../../../design/s31/security/PCS_FRI_OOD_SEED_GEOMETRY.md)
pins the channel implementation and explains why independent uniform hash
blocks would give a uniform QM31 seed on successful draw. This Lean file
does not prove that ideal-random-oracle premise, the Zig refinement, or the
adaptive BCS reduction.

[`FriCascadeNormalization.lean`](FriCascadeNormalization.lean) relates the
experimental native multi-height insertion butterfly to the normalized
butterfly in the published multi-domain FRI protocol. If the carried native
layer has accumulated a factor `2^i`, its next insertion equals `2^(i+1)`
times the normalized insertion **only after** the newly inserted height-`i`
batch is scaled by `2^-i`. For example, with zero carried pair, inserted pair
`(1,0)`, coordinate `1`, and challenge `1`, the native output is `2`;
the unscaled normalized output is `1`, so multiplying it by the expected
second-layer factor `4` would give the wrong value. Scaling that inserted
pair by `1/2` gives the correct normalized output `1/2`. The Lean module
proves the identity over any field where `2` is nonzero and includes the
counterexample. It does not prove the paper's FRI soundness theorem applies
to the native oracle and query schedule.

[`PairedProtocolRecurrence.lean`](PairedProtocolRecurrence.lean) extends that
local identity to every height of the experimental CAS05 accepted-row
relation. Its `native_batch_eq_protocol3` theorem checks the exact sequence
`f₀ + λq₀ + λ²f₁ + λ³q₁ + ⋯`, with each quotient paired with its own
original column. `line_residual_eq_interpolation` equates the native
cross-multiplied two-point line residual with the independent direct
interpolation expression, assuming distinct OOD y-coordinates.
`accepted_rows_refine_protocol3` says that if every forwarded native row
passes the stated fold equation, then every queried row satisfies the
normalized Eq. 68 recurrence after the explicit `2^i` rescaling. The
stronger `accepted_slots_refine_protocol3` composes those results in one
statement, starting with each sampled row's list of `(original, own quotient)`
pairs and ending at its normalized forwarded value. The
`scaled_height_batch` theorem also shows that dividing an inserted batch by
`2^i` is the same as scaling every original and its own quotient by that
factor before batching; `conjugateInterpolant_scale` proves the corresponding
claimed-value interpolation scales linearly. The
experimental native [source guard](https://github.com/teddyjfpender/stwo-zig/blob/codex/paired-degree-protocol-20261013/scripts/check_cas05_relation_extractor.py)
pins the corresponding batch-power and fold call order. These are algebra
and source-shape checks; they do not prove that Zig executes the model, that
the derived source batch is a degree-bounded committed oracle, or that
Protocol 3's proximity theorem applies to the native query/transcript game.

[`PairedBatchSourceBinding.lean`](PairedBatchSourceBinding.lean) starts one step
earlier: for a fixed row, it derives each own quotient from that column's
original word and fixed conjugate-line claim metadata. It packages the ordered
pair sequence into a formal challenge polynomial
`f₀ + λq₀ + λ²f₁ + λ³q₁ + ⋯`, then proves that evaluating it equals the
native batch loop and Protocol 3's row batch. Its even coefficients recover
the original source columns, so two different fixed-width source rows cannot
have the same batch polynomial. Over any finite candidate challenge set,
their batches can agree at at most `2n` challenges for `n` columns; this is a
conservative polynomial-degree bound. A one-column example over `ZMod 7`
shows a real collision at `λ=6`, so one cannot treat a sampled batch as an
unconditionally injective encoding. The acceptance-facing theorem requires
`CheckedRecipes`, an explicit nonzero denominator at every column; the
native OOD guard and tower/circle refinement must discharge that premise.
The theorem assumes the source row and claim metadata were fixed before
`λ`; it does not establish source Merkle binding, global oracle degree, or
adaptive Fiat–Shamir independence.

[`PairedBatchNativeRefinement.lean`](PairedBatchNativeRefinement.lean) gives
the concrete modeled M31/CM31/QM31 row join for the experimental CAS05 draft.
It proves that the coordinate implementations of `QM31.mulM31` and
`QM31.mulCM31` equal extension-field multiplication, and that embedding a
CM31 inverse into QM31 agrees with inversion there. For a QM31 circle point,
a base-circle row, and the native `point.y.c1 != 0` guard, the row determinant
`(point.x.c0−row.x)·point.y.c1−(point.y.c0−row.y)·point.x.c1` is nonzero.
The resulting accepted-row theorem checks each original word's own quotient
and equates the full native-shaped `f₀+λq₀+λ²f₁+λ³q₁+⋯` batch with the
fixed-source polynomial evaluation, for any number of columns. The source
contract is the exact hashed
[`transposed_paired_sparse.zig`](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/transposed_paired_sparse.zig)
draft checked by [`pcs_fri_cas05_source_profile.py`](../../../../../scripts/release/pcs_fri_cas05_source_profile.py).
This remains algebra plus a source pin: the Lean theorem does not execute
Zig, prove authenticated source openings, fix OOD claims before `λ`, bound
the global derived oracle degree, or provide native security bits.

[`PairedBatchSourceCustody.lean`](PairedBatchSourceCustody.lean) joins the next
local boundary. It models a tagged height-zero leaf or inserted source node
followed only by upper Merkle parents. In the actual multi-height XDM04 tree,
this path shape directly describes the **bottom inserted source height**.
Rows at earlier heights pass through more tagged inserted source nodes before
reaching the upper-only part of the tree. The model's binary path position must also be converted
from XDM04's transposed native index: above level one, the native sibling
toggles bit 1 rather than bit 0.
For two different rows accepted at the same source root, level, and position,
it constructs a collision in those exact node or upper-path hash inputs.
Given the native and committed openings and absence of such a collision,
the opened M31 row equals the committed row in the original column order.
The CAS05 statement match then replaces proof-supplied claims with the
public claim roster; its sampled OOD y-coordinate determines every line
coefficient, independent of the batch challenge. The combined theorem
checks the conjugate y-span, nonzero quotient denominator, and equality of
the native-shaped batch with the committed source-row polynomial. The
[CAS05 source audit](../../../../../scripts/release/pcs_fri_cas05_source_profile.py)
pins XDM04's row-fill, duplicate, leaf/inserted/upper hash, root-check and
publication order, plus statement matching, claim absorption before the
batch draw, and the `opened.at` handoff. Hostile source mutations are tested.
The Lean theorem still takes native-success-to-modeled-opening and
prover-tree construction as premises, including the missing mixed inserted
paths for all earlier source heights; it does not prove compiled Zig
semantics, hash collision resistance, global oracle degree, or adaptive
Fiat–Shamir sampling.

[`PairedBatchXdm04Topology.lean`](PairedBatchXdm04Topology.lean) models those
mixed paths. Each step carries a sibling digest and either an inserted row or
`none` for an upper parent. It proves, for every finite depth, that replay
using XDM04's transposed parent/side schedule equals replay using the binary
path position. Two conflicting accepted rows at the same root and position
therefore yield either a collision in their tagged starting nodes or in one
of the tagged inserted/upper parent inputs. Under absence of such a local
collision, the original row equals the committed row and the public-claim
paired-batch theorem applies at any modeled source height. Native verifier
success and committed prover-tree construction remain explicit premises;
these theorems do not establish the Zig-to-Lean correspondence or BLAKE2s
collision resistance.

For example, with largest log size `k=5`, three source heights, and raw query
`5`, XDM04 opens these native nodes (the `j=0` member of each pair):

| Source height | Native level/index | Binary path position | Parents above it |
|---|---:|---:|---|
| `0`, tagged leaf | `5 / 4` | `2` | inserted height 1, inserted height 2, then upper |
| `1`, tagged inserted | `4 / 2` | `1` | inserted height 2, then upper |
| `2`, tagged inserted | `3 / 0` | `0` | upper only |

At native level 4/index 2, the first sibling is selected by bit 1, so this
node is the right child. Reading bit 0 would put it on the left and produce a
different root. The focused [draft native test](../../../tests/pcs_fri_xdm04_topology_draft.zig)
replays all three heights against the actual committed tree and accepted
XDM04 wire, checks that wrong orientation, and corrupts a compressed witness.
The [source audit](../../../../../scripts/release/pcs_fri_cas05_source_profile.py)
now pins the native topology file as well as the verifier and prover files.

[`PairedBatchXdm04Certificate.lean`](PairedBatchXdm04Certificate.lean) makes two
path premises checkable without fixing a profile size. First, a checked
opening certificate records the tagged starting row, native index, converted
binary path position, sibling and inserted-row steps, and root. Its theorem
turns a successful check into `acceptedMixedOpening` and proves that native
transposed replay reaches the same root. Second, an all-node tree recurrence
implies that the path derived from any recorded node reaches the committed
root. This supplies a modeled committed opening once the starting tagged node
and terminal root index are identified.

The [audit-only Zig checker](../../../tests/lib/pcs_xdm04_mixed_certificate.zig)
applies these conditions to the experimental XDM04 draft: it calls
`verifyAndCollect`, independently parses the accepted wire and query rows,
rebuilds the sparse opening tree, checks every returned row and its full mixed
path, and checks every node of a committed prover tree against its source
columns. The [focused test](../../../tests/pcs_fri_xdm04_certificate_draft.zig)
exercises three profile shapes, duplicate queries, inserted and upper edges,
and mutations of accepted rows, path siblings, source columns, and tree nodes.
Run it with `formal/s31/tests/run_pcs_fri_xdm04_certificate_draft.sh
<path-to-exact-draft-checkout>` from the repository root. The audit shares
native hash and topology helpers. Its borrowed source-column check is a
point-in-time check; later mutation requires a new audit. It does not
independently establish hash framing, nor is it installed in the production
CAS05 verifier. A formal
Zig-to-Lean semantic relation for the audit and concrete BLAKE2s assumptions
remain prerequisites for replacing the explicit native opening premises.

[`PairedBatchXdm04Framing.lean`](PairedBatchXdm04Framing.lean) specializes that
certificate to the exact XDM03 node preimages used by XDM04. A leaf hashes
`"S31XDL03" || u16le(column_count) || u32le(each canonical M31)`. An upper
node hashes `"S31XDU03" || left_digest || right_digest`. An inserted source
node hashes `"S31XDI03" || upper_digest(left,right) || encoded_row`: the
inner upper digest is part of the preimage. For a two-column row `[1,256]`,
the leaf preimage in hex is
`53333158444c3033 0200 01000000 00010000` (spaces mark fields only).
The Lean digest is abstract and constrained to 32 output bytes; the theorem
turns a successful framed certificate check into the mixed-opening predicate
and native-index replay equation. It does not claim a formal BLAKE2s or Zig
implementation equivalence.

The independent [Python framing audit](../../../../../scripts/release/pcs_fri_xdm04_framing.py)
uses `hashlib.blake2s`, its own preimage builders, and its own transposed
parent/sibling/children formulas. It rehashes every node from native-generated
source columns, parses the XDM04 wire, reconstructs the compressed witness,
and compares every opening field emitted by the native Zig audit. At level
`4`/native index `2`, it checks binary position `1`: native bit 1 selects the
right child even though native bit 0 is zero. The fixture also compares
parent, sibling, ordered children, and converted binary path position for all
62 non-root nodes of its depth-five transposed tree. The checked-in
[native fixture](../../../tests/fixtures/xdm04-native-framing.json) contains
the accepted wire and 18 captured openings for duplicate and overlapping
queries. Run
`formal/s31/tests/run_pcs_fri_xdm04_framing_draft.sh <path-to-exact-draft-checkout>`
to regenerate that fixture at the pinned experimental commit and run the
[hostile controls](../../../../../scripts/tests/test_pcs_fri_xdm04_framing.py).
This differential audit covers the concrete fixture and its mutations; it
does not turn runtime agreement into a verified Zig semantics theorem, provide
collision resistance, or enable CAS05 in the production verifier.

[`TwoPointDegreeCorrection.lean`](TwoPointDegreeCorrection.lean) proves the
ordinary-polynomial degree step under exact reconstruction. For distinct
points `a,b`, values `vₐ,vᵦ` determine an affine line `L`. If polynomial `f`
has those values, then `(X−a)(X−b)` divides `f−L`, yielding its *own*
quotient `q`. The proof establishes both directions: if `deg f < d` and
`d ≥ 2`, then `q=0` or `2+deg q<d`; if `f=L+(X−a)(X−b)q` and the same
quotient bound holds, then `deg f<d`. Exact reconstruction determines one
unique own quotient for fixed `f` and claims. The module also proves that batching any finite
roster as `f₀+λq₀+λ²f₁+λ³q₁+⋯` preserves the `d` bound and that evaluating
this derived polynomial yields the previously modeled Protocol 3 row batch.
For a hand calculation over rationals, take `f=X²+1`, `a=1`, `b=3`:
the claims are `2,10`, their line is `L=4X−2`, and
`f−L=(X−1)(X−3)`, so `q=1`. Here `deg f=2<3` and `2+deg q=2<3`.
The native circle denominator is a circle vanishing **line**, while this
module's divisor is quadratic in `F[X]`. Transferring the degree claim to
the native circle basis still requires a proved point-removal and degree
refinement; these theorems assign no native security bits.

[`CircleVanishingLine.lean`](CircleVanishingLine.lean) analyzes that actual
native line. Write the sampled QM31 point as
`(x₀+u x₁, y₀+u y₁)`, where `u²=d` in the CM31 coefficient field. At a base
circle row `(a,b)`, CAS05 divides by

```text
V(a,b) = (x₀-a)y₁ - (y₀-b)x₁.
```

The tower circle equation gives
`x₀²+y₀²+d(x₁²+y₁²)=1` and `x₀x₁+y₀y₁=0`. Along the
line `V=0`, every point is `(x₀+t x₁, y₀+t y₁)`, with
`t=(b-y₀)/y₁` under the native `y₁≠0` guard. Substitution gives the exact
identity

```text
(x₀+t x₁)² + (y₀+t y₁)² - 1 = (t²-d)(x₁²+y₁²).
```

The Lean proof shows `x₁²+y₁²≠0` from those equations and the guard. Thus
the line meets the circle only when `t²=d`: over QM31 at the two conjugate
sampled points, and at no CM31 base-circle point when `d` is nonsquare.
For a hand calculation with rational coefficients, use `d=2`,
`(x₀,y₀)=(-1/3,0)`, `(x₁,y₁)=(0,2/3)`. Then
`V(a,b)=(-1/3-a)·2/3`; its circle intersections are
`(-1/3,±2√2/3)`, with no rational intersection. This illustrates the
native *line* geometry, rather than the ordinary `(X-a)(X-b)` divisor.

Over a coefficient field containing `i²=-1`, the same line has Laurent
circle-coordinate edge coefficients `(-y₁-i x₁)/2` and
`(-y₁+i x₁)/2`; the formal proof shows both are nonzero.
[`CircleLaurentDegree.lean`](CircleLaurentDegree.lean) now represents a circle
polynomial concretely as a finite Laurent coefficient map `ℤ →₀ F`, with
filtration `L_n={f : support(f)⊆[-n,n]}`. It proves that the native line is
the three-term Laurent polynomial `V=aT+b+cT⁻¹`, evaluates to the exact
native denominator under `T=x+i y`, and has `a,c≠0` under the modeled OOD
circle equation and `y.c1` guard. The coefficient identity gives
`q∈L_{n-1} ⇒ Vq∈L_n`. Therefore an **assumed exact polynomial relation**
`f=ℓ+Vq`, with interpolation `ℓ∈L_1`, proves `f∈L_n` for `n≥1`. At a row
where `V≠0`, that same identity evaluates to the native quotient value
`q(row)=(f(row)-ℓ(row))/V(row)`. If `q` has nonzero coefficients at both
ends of `L_m`, the product has nonzero coefficients at `m+1` and `-(m+1)`;
the `+1` bound is sharp.

For example, let `q=uT+vT⁻¹` and `V=aT+b+cT⁻¹`, with `a,c,u,v≠0`. Then
`Vq=auT²+buT+(av+cu)+bvT⁻¹+cvT⁻²`. The new extreme coefficients `au` and
`cv` cannot cancel with lower terms. Adding an interpolation line with
support in `[-1,1]` still leaves the original in `L_2`.

[`CircleLaurentQuotient.lean`](CircleLaurentQuotient.lean) closes the **coefficient
model's quotient existence step**. If `f∈L_n`, `ℓ∈L_1`, `n≥1`, and their
evaluations agree at an invertible OOD Fourier coordinate `z`, the theorem
constructs `q∈L_{n−1}` with `f=ℓ+Vq`. Its explicit field assumptions are
that `z` has a monic degree-two minimal polynomial over the coefficient
field, the native line `V` vanishes at `z`, and the modeled OOD circle
equations and `y.c1≠0` guard hold. It shifts `f−ℓ` by `T^n`, obtains an
ordinary polynomial of degree at most `2n`, divides by `minpoly(z)`, and
shifts the quotient back by `T^{n−1}`. The proof identifies the native
three-term line with a nonzero scalar times that minimal polynomial. Its
leading Fourier coefficient is nonzero by the existing circle geometry,
so the quotient loses exactly one band radius as a bound.

[`ConcreteCircleMinpoly.lean`](ConcreteCircleMinpoly.lean) supplies the
degree-two minimal-polynomial premise for a concrete guarded QM31 circle
point. It constructs the CM31→QM31 algebra map, proves that a point with
`y.c1≠0` has a Fourier parameter `x+i*y` outside CM31, and proves that
parameter's inverse and Fourier coordinates recover the original point.
It then proves its minimal polynomial over CM31 is monic of degree two.
This removes a field-algebra premise when applying the Laurent quotient
theorem to the modeled CAS05 point; authenticating that point and all
source rows is still separate.

Here is the arithmetic over `F₅` by hand. Take `i=2` (`i²=−1`), `d=2`
(a nonsquare), and `(x₀,y₀,x₁,y₁)=(0,0,2,2)`. The modeled tower circle
equations hold: `2·(2²+2²)=1 mod 5`, and `y₁=2≠0`. The Fourier coordinate
at the OOD point is `z=u`, where `u²=2` in `F₂₅`; its conjugate is `−u`.
The native line and its shifted ordinary polynomial are

```text
V(T) = 2T + T⁻¹              T·V(T) = 2T² + 1 = 2(T²−2).
```

Choose `ℓ(T)=1+T` and `q(T)=T+T⁻¹`. Then

```text
f(T) = ℓ(T)+V(T)q(T) = 2T² + T + 4 + T⁻²  (mod 5).
f(u)=ℓ(u)=1+u,       f(−u)=ℓ(−u)=1−u.
```

Thus `f∈L₂` and the constructed quotient is in `L₁`; multiplying by the
line recovers the polynomial identity, not just values at opened rows.

[`CircleLaurentUniqueness.lean`](CircleLaurentUniqueness.lean) proves the
finite-domain degree-correction boundary. If `f∈L_n`, then `Tⁿf` is an
ordinary polynomial of degree at most `2n`. A nonzero `f` can therefore
vanish at no more than `2n` distinct nonzero Fourier coordinates, and two
`L_n` polynomials agreeing at `2n+1` such coordinates are identical. For
`n=2`, five distinct coordinates suffice: shifting the five coefficient
slots `T⁻²,T⁻¹,1,T,T²` by `T²` gives an ordinary degree-at-most-four
polynomial, which cannot have five roots unless it is zero.

The theorem also starts from an **arbitrary table of original values**. If a
bounded own quotient `q∈L_{n−1}` satisfies the CAS05 row equation at every
table coordinate where the native line `V` is nonzero, then
`f=ℓ+Vq∈L_n` evaluates to exactly that entire table. This is the exact
all-row degree-correction statement. CAS05 opens only sparse sampled rows;
the theorem does not turn those samples into an all-row equation or prove
correlated agreement. The separate full-row uniqueness lemma says that when
an already bounded `f` and `q` obey this equation at more than `2n`
distinct coordinates, the polynomial identity `f=ℓ+Vq` follows.

CAS05 commits evaluation rows, and no formal map currently refines those
rows into this Laurent coefficient object. The native OOD Fourier coordinate
also needs a refinement to the modeled degree-two root and line-root
hypotheses. No theorem identifies this `L_n` with the paper's `L_n'` circle
basis. Pointwise native division alone establishes none of those joins, so
this theorem assigns no native PCS/FRI security bits.

[`BundleQueryBound.lean`](BundleQueryBound.lean) proves the elementary query
event needed by the experimental full-fiber cascade: if a query checks every
row in its selected bundle, the raw positions whose bundles touch a fixed
bad-row set include all the bad rows themselves. Thus `s` independent uniform
raw draws miss bad bundles no more often than they miss the bad rows, even
when bundle positions overlap or raw queries repeat. This is a finite
counting theorem. Its `masked_bundle_miss_fraction_le` corollary also uses
the exact M31-reduce-and-mask word count: for `2 ≤ k ≤ 31`, an ideal
independent 32-bit word stream misses all bad bundles with fraction at most
`((2^k - |bad|)/2^k + 2/2^32)^s`. It still requires a proof that the native
verifier checks each required bundled row and that the Fiat–Shamir transcript
realizes the assumed independent word stream.

[`SparseCascadeQueries.lean`](SparseCascadeQueries.lean) handles the distinct
sparse path proposed for the adjacent-height paired cascade. A raw row `r`
opens just the pair starting at `2·⌊r/2^(i+1)⌋` at source height `i`.
The projected circle row is that even row plus `r mod 2`, and the folded
line row lies in the next opened pair. An explicit finite equivalence proves
that each source row at height `i` has exactly `2^i` raw preimages, so this
projection preserves uniformity if the raw row is uniform. The old
full-fiber `BundleQueryBound` theorem does not apply directly to this sparse
verifier. Neither module proves native transcript independence or the FRI
proximity theorem.

[`SparseMultiHeightAgreement.lean`](SparseMultiHeightAgreement.lean) handles
the fact that **one raw query opens a pair at every height**. For fixed bad
source-row sets `Bᵢ`, let `G` be the raw rows whose opened pairs avoid `Bᵢ`
at every height. With `s` independent ideal raw draws made *with replacement*,
the exact number of all-good query vectors is `|G|^s`. If a global
correlated-agreement theorem can show that some height has at most `b` safe
raw rows, the number is at most `b^s`. The Lean theorem states that missing
agreement hypothesis explicitly; it does not derive it from the committed
polynomials, Merkle roots, or the native transcript.

[`PairedSparseBatchAgreement.lean`](PairedSparseBatchAgreement.lean) adds the
fixed-oracle paired-batch step before raw queries. Fix the original and
candidate source tables, the OOD-derived quotient recipes, and a finite set
`Λ` of batch challenges **before drawing one shared `λ`**. If height `i` has
`mᵢ` source rows where any of its `cᵢ` original columns differs, a bad `λ`
can hide a mismatch at one row at no more than `2cᵢ` field values. Across
every height, the union of exceptional challenges `E` satisfies

```text
|E| ≤ Σᵢ 2 cᵢ mᵢ.
```

For `λ∈Λ\E`, batched original/own-quotient values disagree at **exactly**
the rows where the fixed original source tables disagree. The quotient for
each column is derived from that same original value; a separately chosen
quotient could invalidate the polynomial injection step. A specialized Lean
corollary applies the collision count to the modeled native QM31
`nativeBatch` formula through the existing row-algebra refinement.

Choose one height `i<k`, set `Dᵢ=2^(k−i)`, and make `s` independent uniform
raw queries from the `2^k` largest-domain positions, with replacement. The
number of all-query misses for a nonexceptional `λ` is at most
`[(Dᵢ−mᵢ)·2^i]^s`. Counting challenge/query pairs gives the explicit bound

```text
|E|·(2^k)^s + (|Λ|−|E|)·[(Dᵢ−mᵢ)·2^i]^s.
```

For example, with `k=3`, height `i=1`, and one mismatched source row,
`Dᵢ=4` and each projected row has two raw preimages. The bound permits six
of eight raw positions to miss per draw. The adjacent-pair check may detect
more, but the proof uses only the guaranteed selected-row projection.
This theorem **does not produce `mᵢ` from false acceptance or FRI proximity**.
In particular, the candidate source table must be fixed before `λ`; a
candidate chosen after seeing `λ` is outside the theorem. Native Merkle/BCS
binding and the shared transcript's adaptive sampling law also remain open.

More precisely, if `Dᵢ` is the set of raw positions whose opened pair meets
`Bᵢ`, then Lean proves `G = {0,…,2^k−1} \ ⋃ᵢ Dᵢ`. Thus the exact ideal count is
`(2^k − |⋃ᵢ Dᵢ|)^s`. This union automatically accounts for overlap between
heights, from identical events to disjoint events; no height-independence
assumption is hidden in the formula.

The counterexample is small enough to check by hand. On eight raw rows
`0..7`, mark source rows `{0,2}` bad at height zero and `{0}` bad at height
one. The native pair formula opens these rows:

| Raw rows | Height 0 pair | Height 1 pair | Both heights safe? |
| --- | --- | --- | --- |
| `0,1` | `(0,1)` | `(0,1)` | No |
| `2,3` | `(2,3)` | `(0,1)` | No |
| `4,5` | `(4,5)` | `(2,3)` | Yes |
| `6,7` | `(6,7)` | `(2,3)` | Yes |

Each height alone is safe on four of eight raw rows, and the **same** four
rows are safe at both heights. One-query joint miss is therefore `1/2`,
while the invalid product of the two height miss fractions would be `1/4`.
For `s` fresh ideal raw queries, the joint miss fraction is `(1/2)^s`.
The paired native row formula is `pairBase(raw,height) =
(raw >> (height+1)) << 1` in the experimental XDM04
[`transposed_merkle_sparse.zig`](https://github.com/teddyjfpender/stwo-zig/blob/bafa2b4669c6da74a6b8f7341ffb172e5479f95f/src/core/pcs/transposed_merkle_sparse.zig).
This is a source-revision pin for the model, not a proof that every later
CAS05 binary implements the same schedule. Native binding, adaptive
commitments, and Fiat–Shamir sampling remain separate obligations.

For example, take a 32-row domain (`k=5`), source height `i=2`, and raw
row `r=23`. The pair base is `2·⌊23/8⌋=4`, so the verifier opens rows `4`
and `5`. The projected circle row is `5` because `23` is odd. Folding that
pair produces line row `2`, which lies in the next opened pair `2,3`.
Exactly four raw rows project to source row `5`: `17,19,21,23`. This is the
`2^i` preimage count proved for every valid height and row.
For any fixed set of bad source rows, the module counts its raw preimages
exactly and proves that a sparse pair that checks both rows misses the set
on no more raw positions than the projected single-row event. Under
independent uniform raw draws, the all-missed sequence count is bounded by
`((2^(k-i) - |bad|)·2^i)^s` out of `(2^k)^s` sequences. Native M31 word
reduction, transcript independence, and authenticated checking of both
rows remain separate obligations.
The `masked_sparse_miss_fraction_le` theorem further composes this fixed-set
count with the **exact** M31-reduce-and-mask preimage bound. For
`2 ≤ k ≤ 31`, if independent ideal uniform 32-bit words supply the raw
queries, its missed fraction is at most
`((2^(k-i)-|bad|)/2^(k-i) + 2/2^32)^s`. The extra two-word term records the
native mask bias; it grants no concrete BLAKE2s or adaptive BCS claim.

[`ConservativeEnvelope.lean`](ConservativeEnvelope.lean) proves an arithmetic
limit of one **published upper-bound expression**: in Circle STARKs Remark 26,
its leading commitment/folding term exceeds `2^-96` whenever the candidate
degree parameter has at least 256 rows, blowup is at least 2, Johnson
multiplicity is at least 3, and batch width is at least 1. The proof uses a
lower floor for `sqrt(blowup)` and exact arithmetic. It does not prove that
the native protocol matches the paper or that an adversary can succeed with
that probability.

The [BCS transcript epoch model](BcsTranscriptEpoch.lean) proves that a
modeled verified nonce starts a fresh query-input epoch with nine distinct
pre-hash messages for the sealed 70-query schedule. The nine concrete
little-endian u32 counter encodings are checked in Lean. The
[native and independent-model replay](../../../../../design/s31/security/PCS_FRI_BCS_TRANSCRIPT_REFINEMENT.md)
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
log-size ordering of a two-column leaf and five malformed inputs. An independent
post-verification checker additionally reconstructs the pair/witness event
trace for every subset, checks each published path entry at its ancestor, and
requires exact witness offset order and final root equality. The one-sort Lean
model now has explicit all-height witness accounting and per-query path
theorems. These checks cover
the pinned native implementation on that finite domain; a general Zig
semantics theorem, committed-column origin and collision bound are still
required for P06.

The [native collision reduction](../../../../../design/s31/security/PCS_FRI_NATIVE_MERKLE_COLLISION_REDUCTION.md)
checks two full native BLAKE2s openings of one root, height and index. When
their canonical M31 rows differ, it constructs a checkable leaf or parent
hash collision witness. Its toy-hash tests exercise both outcomes; native
BLAKE2s tests reject a conflicting row without such a collision. A separate
native audit checks exact equality of rows and paths copied to duplicate query
positions. This is a concrete conditional binding step, while the hash
probability bound and general compressed-decoder
refinement remain open.

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

[`PairedSparseRound.lean`](PairedSparseRound.lean) specializes this algebra to
the **experimental CAS05 paired sparse verifier**. At an interior height its
exact check is

```text
fold(previous_even, previous_odd, x, α)
  + α² · fold(source_even, source_odd, y, α) = selected_next_line_word
fold(a,b,z,α) = (a+b) + α(a-b)/z
```

If the previous pair is `p₀ ± x p₁` and the source pair is `q₀ ± y q₁`,
with nonzero `x,y`, the left side is exactly
`2p₀ + 2αp₁ + 2α²q₀ + 2α³q₁`. Lean proves both the evaluation identity and
degree at most three. It also proves that a native raw row `r` selects one of
the two opened circle rows according to `r mod 2`, that the line output row is
`floor(r / 2^(step+1))`, and that this row belongs to the next authenticated
line pair. In the circle-point model, conjugation changes `(x,y)` to `(x,-y)`
and doubling preserves that conjugation relation. The point-pair property of
the concrete canonical coset is still a premise in the theorem; the current
Lean proof does not refine Zig's `bitReverseIndex`, `CanonicCoset.at`, or the
Merkle openings into that premise.

The degree-one expression for each **single pair** is freely interpolable
when `2y` is invertible. It provides no evidence that *all* opened pairs come
from one globally low-degree committed oracle. The degree-three local
polynomial and row-schedule lemmas are a native formula refinement, not a
correlated-agreement result.

For a hand check over ordinary rational arithmetic, set
`(p₀,p₁,q₀,q₁)=(1,2,3,4)`, `(x,y)=(2,3)`, and `α=5`. The previous pair is
`(5,-3)` and source pair is `(15,-9)`. The native calculation is
`fold(5,-3,2,5)=22` and `fold(15,-9,3,5)=46`, hence
`22 + 5²·46 = 1172`. The polynomial gives the same answer:
`2 + 4·5 + 6·5² + 8·5³ = 1172`. Over QM31, these calculations are read
modulo its field characteristic; the example uses small values to expose the
signs, factor two, and `α²` insertion weight.

**Do not turn the degree-three polynomial into a three-roots soundness bound.**
The next line commitment is mixed *after* this round's challenge, so its
values can depend on `α`. A proximity theorem must cover this adaptive round,
the degree-corrected original and quotient ensemble at every source height,
the multi-domain correlated-agreement hypotheses, the native sparse queries,
and the BCS/ROM commitment game. This module proves a local evaluation
refinement only and grants no native security bits.

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
