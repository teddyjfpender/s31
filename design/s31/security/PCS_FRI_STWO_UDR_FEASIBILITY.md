# S-two unique-decoding feasibility ledger for the S31 Gate

This note evaluates the **published S-two 2026 theorem expressions** with
exact rational arithmetic. It does not certify the native S31 PCS/FRI verifier:
the executable protocol, its AIR relation, OOD quotient ensemble, query sampler,
Merkle layout, and Fiat–Shamir transcript have not been proved to instantiate
the paper's protocols. The release result remains **closed** even when an
idealized scenario's arithmetic passes.

Primary source: [S-two Whitepaper, Protocols 1, 3, and 4; Theorems 4–6;
Appendix A.4 Lemmas 5–7 and Remarks 8 and 16](https://eprint.iacr.org/2026/532.pdf).
The [official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
identifies the paper's round formulas and implementation caveats. The earlier
[multi-domain ledger](PCS_FRI_STWO_MULTIDOMAIN_LEDGER.md) treats the Johnson
and Guruswami–Sudan list regimes. This note uses the **unique-decoding**
regime `0 < θ < δ/2`, where `δ = 1−ρ` and `ρ = 1/B`; the list size is one.
Do not substitute the older [Circle STARKs 2024 single-domain FRI bound](https://eprint.iacr.org/2024/278.pdf)
for these multi-domain rounds.

## What is bounded

Let `q = 2^31−1`, `F = QM31 = 𝔽_(q⁴)`, `N = max N_t`, and `B = 2^β`. All
fractions below are calculated exactly by
[`pcs_fri_stwo_udr.py`](../../../scripts/release/pcs_fri_stwo_udr.py).
The paper's setup requires `deg(A) ≤ B+1`, `N B² ≤ 2³⁰`, use multiplicities
below `q`, and, for every nonempty table, `1−θ > (1/B)(1+2/N_t)`.

| Published round | Unique-decoding upper-bound expression | Ledger inputs |
| --- | --- | --- |
| Flat AIR logUp | `r(k_in+k_out+Σ_t (r_t+s_t)N_t)/q⁴` | Maximum message dimension `r`, public message counts, each table's use and yield counts and height |
| Flat AIR composition | `Σ_t(k_t+r_t+s_t)/q⁴` | `k_t` is the number of AIR constraints in table `t`, not its column count |
| Flat AIR OOD | `[1+(B+2)N]/|C(F) \ C(𝔽_q)|` | Circle-point cardinality and largest table |
| Multi-domain FRI batching | `(M−1)NB/q⁴` | Maximum domain batch width `M` |
| Each FRI fold `j` | `3|S_j|/q⁴` | Explicit candidate post-projection domains `S_j` |
| Final FRI query | `(1−θ)^s` | `s` independent paper-protocol query draws |
| BCS/ROM composition | `(T+R) max_i ε_i + 3(T²+1)/2^λ` | Hash-query budget `T`, protocol rounds `R`, candidate `λ=256` |

The OOD denominator is explicit: since `q≡3 (mod 4)` and `q⁴≡1 (mod 4)`,
the affine circles have `|C(𝔽_q)|=q+1` and `|C(F)|=q⁴−1`, hence
`|C(F) \ C(𝔽_q)|=q⁴−q−2`. The formulas are quoted **upper bounds**. A
large upper bound means this theorem expression cannot *certify* a target;
it does not establish an attack or a lower bound on the true error. The ledger
assigns **zero grinding credit** because no corresponding native reduction is
proved. The paper's degree-corrected batch evaluation uses both `f` and
`(f−v)/v_Q`; a quotient-only ensemble would require a different argument.

The script's `scenario_arithmetic` accepts a fully explicit *hypothetical*
paper-protocol scenario. It checks the listed parameter preconditions and
calculates every listed bound as a reduced numerator/denominator pair. It
requires a stated `T` and `R`; the floor on `R` counts three AIR rounds, one
batching round, every listed fold, and a query phase. The resulting Boolean
`conditional_formula_meets_target` means only that these **chosen paper
inputs** fit the requested absolute soundness bound. No scenario field can
assert native correspondence.

## A concrete unique-decoding example

Take one idealized table of height `N=2²⁰`, `B=2`, one AIR constraint, one
use and one yield per row, dimension `r=1`, batch width `M=2`, single folds
from size `2²⁰` to `2`, and `R=25`. Choose `θ=16383/65536`, just inside
`δ/2=1/4`, and `T=2³²`. At `s=232` the exact BCS expression is about
`0.822513 × 2⁻⁶⁴`; at `s=231` it exceeds `2⁻⁶⁴`. This is a conditional
64-bit **paper arithmetic** example, with 232 raw queries and an idealized
protocol. It is neither the native 70-query Gate nor a released 64-bit proof.

At the same geometry, `T=1` and `s=243` make the hypothetical expression
about `0.903414 × 2⁻⁹⁶`; `s=242` fails. `T=1` is not a useful deployment
adversary budget. Both examples are executable in the focused test file
[`test_pcs_fri_stwo_udr.py`](../../../scripts/tests/test_pcs_fri_stwo_udr.py).

## Target, domain, and query tradeoffs

The next table fixes `N=2²⁰`, `T=2³²`, `λ=256`, zero grinding, and the
single-fold paper cascade. The five `B` values exhaust `N B²≤2³⁰` for this
height. The nonquery ratio is an **optimistic necessary** BCS expression
using only the paper OOD and first-fold terms, with minimal `R`; other rounds
can increase it. The query count is the least integer at the excluded
`θ=δ/2` boundary for the query term alone. Strict `θ<δ/2` can need more
queries; these numbers do not rescue a failed nonquery ratio.

| `B` | `|D₀|=NB` | Minimum `R` | 64-bit nonquery ratio | Query-only minimum, 64 bits | 96-bit nonquery ratio | Query-only minimum, 96 bits |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 2,097,152 | 25 | 0.015625004 | 232 | 67,108,881 | 309 |
| 4 | 4,194,304 | 26 | 0.023437504 | 142 | 100,663,313 | 189 |
| 8 | 8,388,608 | 27 | 0.046875001 | 116 | 201,326,594 | 155 |
| 16 | 16,777,216 | 28 | 0.093750001 | 106 | 402,653,188 | 141 |
| 32 | 33,554,432 | 29 | 0.187500002 | 101 | 805,306,375 | 134 |

All 64-bit nonquery ratios are below one, although the complete native proof
and cost remain unknown. All 96-bit nonquery ratios exceed one by many orders
at this `N,T`. The 80-bit nonquery ratios also exceed one: approximately
`1024, 1536, 3072, 6144, 12288` as `B` grows. At `T=1`, 96-bit
nonquery arithmetic fits only `B=2` or `4` for this height; higher blowups
increase the first-fold bound enough to fail. This is an unusually strong
illustration that **more blowup and more queries alone do not solve the
published field-size terms**.

An even broader necessary condition ignores `N`, `B`, and every fold. Lemma 7
has OOD numerator at least one and denominator below `q⁴<2¹²⁴`; Theorem 6
multiplies the largest round bound by `T+R≥T`. Its quoted expression is
therefore **strictly greater than** `T/q⁴`. For `T≥2²⁸` this alone exceeds
`2⁻⁹⁶`. The arithmetic is formalized in
[`StwoUDRFeasibility.lean`](../../../formal/s31/S31/Gadgets/PcsFri/StwoUDRFeasibility.lean).
Thus **QM31 cannot certify an absolute 96-bit bound through this ungrinded
published envelope at a hash-query budget of `2²⁸` or more**, regardless of
domain or raw query count. This statement is scoped to the quoted theorem
and zero proved grinding credit. A larger challenge field, a proved reduction
that gives effective grinding credit to the limiting round, or a stronger
theorem may change the conclusion.

## Native status and next proof obligations

`gate_udr_ledger` reads a locally trusted sealed Gate package. It reports
source-observed `N`, configured `B`, raw query count, PoW setting, key hash,
and the necessary hypothetical tradeoffs. **Every native theorem term remains
null**, including `R` and the ROM collision/Merkle mapping. The CLI flag
`--require-proven` exits unsuccessfully even when an optional hypothetical
scenario passes.

To admit an actual conservative profile, establish all of the following:

1. Extract the real table heights, AIR constraint counts/degrees, message
   dimensions, multiplicities, FRI batch widths, fold domains, and protocol
   round count from the emitted key and verifier, then prove they match the
   paper's flat-AIR and cross-domain oracle relation.
2. Prove the native OOD sampler and quotient openings realize the degree-
   corrected `f` plus `(f−v)/v_Q` ensemble and circle-point assumptions.
3. Prove a query-distribution reduction for the native non-squaring-consistent
   sampler, and the exact FRI fold, insertion, and terminal checks.
4. Prove the native BLAKE2s transcript, Merkle authentication, challenge
   domain separation, and any PoW credit instantiate the paper's BCS/ROM
   bound for a declared adversary budget `T`.
5. Recompute every bound with actual parameters. Preserve the 96-bit target
   unless the release policy is explicitly changed; an arithmetic 64-bit
   scenario is evidence of a tradeoff, not an automatic target reduction.
