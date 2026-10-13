# CAS05 paired PCS/FRI: theorem correspondence ledger

**Decision:** CAS05 is experimental. It has no proven native security bits and
is not eligible for the conservative release profile. This ledger separates
what the [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf) proves for
its idealized Protocols 1, 3, and 4 from what the draft [native paired PR
#249](https://github.com/teddyjfpender/stwo-zig/pull/249) checks. The
[official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
identifies the exact theorem and equation labels. The earlier
[Circle STARKs theorem](https://eprint.iacr.org/2024/278.pdf) treats another
protocol and cannot be substituted for the multi-domain theorem.

The native source was inspected in the working PR while CAS05 was still being
edited. This is a theorem **interface** review, not a source-pin or installed
binary audit. Every native observation below must be rechecked against the
final committed source, canonical wire, and verifier entry point. The
[v0.1 blocker matrix](pcs-fri-v01-blockers.json) remains authoritative for the
production PCS path; this document does not close any blocker in that matrix.

## The one query CAS05 tries to check

Let the largest circle evaluation domain have `D₀=2^k` rows in native
bit-reversed order. A raw query `r` is an integer in `[0,D₀)`. At source
height `h`, CAS05 opens the **two** rows

```text
bₕ(r) = 2 floor(r / 2^(h+1))
source pair = (bₕ(r), bₕ(r)+1)
selected projected row = bₕ(r) + (r mod 2)
```

The last expression is the circle-doubling projection in this row order; the
low bit selects the conjugate half. At line layer `h`, the pair needed by the
next fold is opened at the same `bₕ(r), bₕ(r)+1` pattern. For example, with
`r=13` (`1101₂`), heights `h=0,1,2` open source pairs `(12,13)`, `(6,7)`,
`(2,3)`; the selected source rows are `13,7,3`. A fold at height `h`
produces the line row `floor(r/2^(h+1))`. Its parity chooses one member of
the next line pair. Repeated raw queries deliberately repeat the same
positions; soundness amplification counts **draws with replacement**, not
deduplicated distinct positions.

The [sparse query Lean module](../../../formal/s31/S31/Gadgets/PcsFri/SparseCascadeQueries.lean)
proves these index and fiber-count identities for arbitrary valid heights.
It does not show that every successful Zig verification implements those
indices or authenticate the corresponding values.

The XDM04 source tree hashes all source heights under one transposed root and
authenticates each pair with missing child/sibling hashes. Each CAS05 line
root is separate; its proof opens exactly two QM31 words (four M31 columns)
per raw query and layer. The verifier derives raw positions after mixing the
source and line roots and terminal coefficients, checks the Merkle paths,
the adjacent-pair fold equalities, and the terminal polynomial at each
selected point. A complete proof needs the outer statement and exact channel
state supplied independently; proof-embedded claims or roots are not an
authority. These are source-level descriptions, not a semantic refinement
theorem for the Zig verifier.

## Every theorem join that must hold

| Published hypothesis or reduction | Required CAS05/production identification | Current state |
| --- | --- | --- |
| Field and domains: M31 circle codes, QM31 challenges, canonical cosets, `B=2^β`, `N B²≤2³⁰`, `deg(A)≤B+1` | Extract each actual component domain, degree, and key parameter from one installed binary; identify `D₀`, each `Sⱼ`, code rate, and terminal space | Candidate source profile only; no installed binary/key witness |
| Flat-AIR relation: every component constraint and exact `uses=yields` multiplicity, including public messages | Compiler, native committed rows, interaction columns, multiplicity bounds `<q`, and AIR composition must realize Protocol 1 | General correspondence and committed-row custody still open |
| OOD algebraic identity: composition quotient and all claimed values at one sampled point | Match native quotient denominator/numerator and ownership of source columns to the paper's OOD identity | Local quotient formulas/test vectors exist; whole accepted-proof implication open |
| Degree-corrected batch evaluation, Theorem 5 | At **each** native height, authenticate and FRI-test both original `f` and its own one-point quotient `(f-v)/v_Q`, with the paper's claimed degree spaces and cross-domain relation | CAS05 constructs both at opened rows; no all-oracle degree/refinement theorem |
| Small-table condition | For every nonempty table, `1−θ > (1/B)(1+2/Nₜ)` in the same code spaces and rates | Hypothetical scenario script checks it; native roster not extracted |
| Multi-domain batching | Same precommitted oracles and one challenge, correct weighted ensemble and cross-domain correlated agreement | Source spelling checks weighted original/quotient pairs; theorem join open |
| Every published FRI fold, Theorem 4 | Exact circle-to-line and line-to-line twiddles, source insertions, domain projections, challenge timing and degree transitions | Local normalization identity is Lean-checked; full operational and theorem correspondence open |
| Query phase | Each sampled position authenticates **all** source/line values read by the fold, with exact projection, duplicates, and terminal check | Draft XDM04/CAS05 code and small tests; no all-input native-to-ideal theorem |
| OOD distribution | Uniform point in the paper's `C(QM31) \ C(M31)` or a new proof for the guarded rational-map support | Different accepted support; exact correction below is only a conditional calculation |
| Native query distribution | Independent paper query draws, or a theorem for native `drawU32s` M31 reduction and bit mask under adaptive Fiat–Shamir | Exact one-word preimage arithmetic is Lean-checked; adaptive independence open |
| Merkle/BCS transform, Theorem 6 | Exact leaf/inserted-node encoding, binding/collision reduction, domain-separated transcript, abort/retry semantics, PoW validation, justified `T`, `R`, and 256-bit oracle model | Local authentication tests only; quantitative native reduction open |
| Proof and key custody | Canonical CAS05 wire, source/line roots and OOD claims matched to an external statement, no verifier state publication on failure, production dispatch | Draft statement-bound verifier; production remains on different PCS |

The first eight rows are enough to prevent a theorem shortcut. The proof of a
local fold equality cannot replace a correlated-agreement theorem about all
far committed words. Authentication of selected rows cannot by itself prove
that the committed whole word has the claimed degree. A finite test suite
cannot replace the quantitative BCS/ROM reduction.

### The short-cascade issue

The draft profile caps `height_count` at **8**, while its terminal polynomial
has `2^(k−height_count−β)` QM31 coefficients and is evaluated on a domain of
`2^(k−height_count)` points. For the illustrative full Protocol-4 geometry
`N=2²⁰`, `B=2`, `D₀=N B²=2²²`, the paper ledger lists **21** single-fold
domains down to `B`. CAS05 with eight heights instead stops after eight
folds, checks an **8192-coefficient** terminal polynomial on a **16384-row**
domain, and has **13 fewer committed fold rounds**. Direct terminal checking
can be a sensible protocol design, but the published full-cascade round list,
error expressions, and BCS round count do not transfer verbatim. A theorem
for this exact shortened cascade, including the degree and query bound at
its larger terminal domain, is required. The executable sensitivity tool
reports this geometry without claiming its soundness.

## The guarded OOD support, exactly

Put `q=2³¹−1` and `F=QM31`, so `|F|=q⁴`. The paper's affine OOD set has
`|C(F) \ C(M31)|=q⁴−q−2` points. The rational map

```text
x(t) = (1−t²)/(1+t²),     y(t) = 2t/(1+t²)
```

is bijective from regular seeds (`1+t²≠0`) to all circle points except
`(-1,0)`, by the [Lean rational-map
theorem](../../../formal/s31/S31/Gadgets/PcsFri/OodRationalMap.lean).
The CAS05 OOD draw additionally rejects `y.c1=0`. The
[field count](PCS_FRI_OOD_SEED_GEOMETRY.md) yields `2q²−3` regular seeds
with `y.c1=0`; two more seeds make `1+t²=0`. Consequently the **early-guard
passing** seed set has

```text
A = q⁴ − 2 − (2q²−3) = (q²−1)².
P = q⁴ − q − 2.             [paper OOD point set]
P − A = 2q² − q − 3 > 0.
P/A < 1 + 2⁻⁶⁰.
```

The [Lean support module](../../../formal/s31/S31/Gadgets/PcsFri/OodAcceptedSupport.lean)
checks these exact cardinality identities and the last inequality at the
real M31 modulus. It proves a generic **conditional** mass step: if a bad
event has at most `b` points in the paper support and at most `a≤b` in the
guarded support, then `a/A ≤ (b/P)(P/A)`. The separate finite-field count
`2q²−3` and the premise that the native channel supplies an independent
uniform seed at every relevant transcript state are not proved in Lean.
Also, the early guard's success does not itself prove every native quotient
denominator is nonzero; that all-row statement needs a separate proof.

It would be unsound to replace `P` by `A` in the published OOD round formula
and call the result a theorem. One must prove that its bad-set numerator
continues to apply to the guarded support and that abort on rejected seeds
fits the adaptive transcript/BCS game. The exact ratio is useful for sizing
the needed lemma, not for bypassing it.

## Quantitative feasibility without a native claim

The [published unique-decoding ledger](PCS_FRI_STWO_UDR_FEASIBILITY.md)
checks all quoted idealized round expressions with exact rational arithmetic
and zero grinding credit. At `N=2²⁰`, `B=2`, a deliberately tiny one-table
model with `T=2³²`, `R=26`, `θ=16383/65536`, and `s=232` fits the paper's
**96-bit work-factor** convention `ε(T)/T≤2⁻⁹⁶`, while its absolute error is
roughly 64 bits. The current production Gate is configured for 70 raw
queries, and the CAS05 draft only has small host fixtures. The 232-query
idealized result does not imply that either native prover fits its cost or
the theorem.

The [paired OOD sensitivity tool](../../../scripts/release/pcs_fri_paired_ood_bridge.py)
starts with the **same explicitly idealized** scenario, re-evaluates only the
OOD term against `A`, recomputes the maximum-round BCS expression, and prints
the short-cascade mismatch for an explicitly supplied height count. Its
`--require-proven` mode always exits 2. This is a numerical diagnostic only.
With `T≥2²⁸`, the quoted ungrinded QM31 OOD term alone prevents an
**absolute** 96-bit certificate from this theorem envelope even if every
other term vanished; increasing query count alone cannot fix that limit.

## Reproduce the narrow checks

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_paired_ood_bridge -v
cd formal/s31 && lake env lean S31/Gadgets/PcsFri/OodAcceptedSupport.lean

# Use an explicit paper-protocol scenario JSON, never a native key:
python3 -B scripts/release/pcs_fri_paired_ood_bridge.py scenario.json \
  --candidate-cas05-height-count 8 --require-proven
```

The last command returns 2 even if the hypothetical expression is small.
The complete native release needs source-pinned installed-binary
correspondence, a short-cascade multi-domain theorem, the guarded OOD
reduction, and the BCS/ROM/merkle budget before any security-bit claim.
