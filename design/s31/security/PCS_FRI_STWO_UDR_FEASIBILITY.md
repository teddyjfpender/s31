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
| Flat AIR composition | `max(2+max_t(k_t+r_t+s_t), Σ_t(k_t+r_t+s_t))/q⁴` | Conservative envelope of the conflicting Theorem 3 and Appendix Lemma 6/Table 4 displays; `k_t` counts AIR constraints |
| Flat AIR OOD | `[1+(B+2)N]/|C(F) \ C(𝔽_q)|` | Appendix Lemma 7; Theorem 3 displays `1+deg(A)N`, which is smaller under `deg(A)≤B+1` |
| Multi-domain FRI batching | `(M−1)NB²/q⁴` | Full Protocol 4 ensemble includes the composition quotient on `D₀=NB²`; `M` is the maximum batch width |
| Each FRI fold `j` | `3|S_j|/q⁴` | Full-ensemble projected domains `S_j`: `NB²/2, NB²/4, …, B` |
| Final FRI query | `(1−θ)^s` | `s` independent paper-protocol query draws |
| BCS/ROM composition | `(T+R) max_i ε_i + 3(T²+1)/2^λ` | Hash-query budget `T`, protocol rounds `R`, candidate `λ=256` |

The paper's parameter examples assess **work-factor security** using
`ε(T)/T ≤ 2⁻σ`, where `ε(T)` is the complete BCS expression. A separate,
strictly stronger **absolute-error** claim would require
`ε(T) ≤ 2⁻σ` for the specified `T`. The ledger reports both measures and
never infers one from the other without the factor `T`. Neither conditional
paper calculation is a native security certificate.

For v0.1, the selected target is **96 bits in the paper's work-factor
measure**, `ε(T)/T ≤ 2⁻⁹⁶`, at an adversary BLAKE2s query budget
`T=2⁶⁴`. This is a selected target, not a derived native bound. The
`T=2³²` example below remains an illustration. The
[release blocker matrix](pcs-fri-v01-blockers.json) records the metric and
`T=2⁶⁴`; it remains closed until the actual verifier has a complete
theorem-instantiated bound at that budget.

There is already a **T-independent necessary failure** for the current
single-fold native tuple under this *ungrinded published expression*.
At `B=2`, unique decoding requires `θ<1/4`, so the paper's query base
`α=1−θ` is strictly greater than `3/4`. With 70 raw draws,
`α^70>(3/4)^70>2⁻⁹⁶`. The BCS work-factor expression contains
`((T+R)/T)α^70≥α^70` for every positive `T`, even before other positive
terms. At least 232 draws are necessary at the excluded `α=3/4` boundary;
strict θ and the other errors can require more. The
[matrix](pcs-fri-v01-blockers.json) calculates this exact rational floor,
and [Lean](../../../formal/s31/S31/Gadgets/PcsFri/StwoUDRFeasibility.lean)
proves the boundary and all-positive-`T` inequality. This shows that the
quoted no-grinding formula cannot certify the current 70-query tuple at
96 bits. It does **not** lower-bound the actual native attack probability,
rule out a different theorem, or assign any unproved PoW credit.

The OOD denominator is explicit: since `q≡3 (mod 4)` and `q⁴≡1 (mod 4)`,
the affine circles have `|C(𝔽_q)|=q+1` and `|C(F)|=q⁴−1`, hence
`|C(F) \ C(𝔽_q)|=q⁴−q−2`. The formulas are quoted **upper bounds**. A
large upper bound means this theorem expression cannot *certify* a target;
it does not establish an attack or a lower bound on the true error. The ledger
assigns **zero grinding credit** because no corresponding native reduction is
proved. The paper's degree-corrected batch evaluation uses both `f` and
`(f−v)/v_Q`; a quotient-only ensemble would require a different argument.

Theorem 3 displays composition numerator `2+max_t(k_t+r_t+s_t)`, while
Appendix A.4 Lemma 6 and Table 4 display `Σ_t(k_t+r_t+s_t)`. The ledger
exposes both exact rational expressions and uses their maximum; neither is
silently discarded. Theorem 3 itself states the Johnson interval, while the
Appendix's unique-decoding remark supplies list size one for this scenario.
Theorem 3's OOD numerator is `1+deg(A)N`; Appendix Lemma 7's
`1+(B+2)N` dominates it under the setup degree cap. Both OOD expressions
are exposed, and the Appendix bound is used.

Protocol 1 commits the overall composition quotient `q` on a domain of
size `NB²`; Protocol 4 includes `q` in its batch evaluation ensemble. Thus
the full-ensemble FRI starts at `D₀=NB²`, with `log₂(NB)` post-projection
domains down to `B`. A computation starting at `NB` omits that committed
oracle and understates the batching and first-fold terms.

The script's `scenario_arithmetic` accepts a fully explicit *hypothetical*
paper-protocol scenario. It checks the listed parameter preconditions and
calculates every listed bound as a reduced numerator/denominator pair. It
requires a stated `T` and `R`; the floor on `R` counts three AIR rounds, one
batching round, every listed fold, and a query phase. The resulting Boolean
`conditional_paper_work_factor_meets_target` compares `ε(T)/T` with the
chosen target; `conditional_absolute_error_meets_target` separately compares
`ε(T)` with it. Both mean only that these **chosen paper inputs** fit their
respective arithmetic expression. `R=25` in the example below is a candidate
minimum, not a source-derived count of the actual transcript. No scenario
field can assert native correspondence.

## A concrete unique-decoding example

Take one idealized table of height `N=2²⁰`, `B=2`, one AIR constraint, one
use and one yield per row, dimension `r=1`, batch width `M=2`, single folds
from size `2²¹` to `2`, and `R=26`. Choose `θ=16383/65536`, just inside
`δ/2=1/4`, and `T=2³²`. At `s=232` the exact BCS expression is about
`0.822513 × 2⁻⁶⁴`, so `ε(T)/T` is about
`0.822513 × 2⁻⁹⁶`; at `s=231` both thresholds fail. This is a conditional
**96-bit paper work-factor** and **64-bit absolute-error** arithmetic
example, with 232 raw queries and an idealized protocol. It is neither the
native 70-query Gate nor a released 96-bit proof.

The native query path reduces each ideal 32-bit hash word modulo M31 and then
masks it to a power-of-two position. For a fixed good set, its positive
probability bias over a uniform position is at most `2/2³²` on every native
query domain ([exact finite count and Lean proof](PCS_FRI_M31_MASKED_QUERY_DISTRIBUTION.md)).
`scenario_arithmetic` now reports a **separate conditional adaptation** that
replaces the uniform query term `α^s` by `(α+2/2³²)^s`. It assumes independent
uniform raw words and a good set fixed before each draw. For the illustrative
`T=2³²` scenario above, the full expression divided by `T`, in units of
`2⁻⁹⁶`, moves from about `0.822512610179` to `0.822512728655`; 232 queries
still pass this arithmetic and 231 fail. The adaptation is a finite sampling
bound, not a published S-two protocol theorem or a Fiat–Shamir proof for
BLAKE2s. Its result remains outside release admission.

At the same geometry, `T=1` and `s=243` make the hypothetical expression
about `0.938161 × 2⁻⁹⁶`; `s=242` fails. `T=1` is not a useful deployment
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

| `B` | `|D₀|=NB²` | Minimum `R` | Approx. nonquery ratio: absolute 64 / paper work-factor 96 | Query-only minimum: absolute 64 / paper work-factor 96 | Approx. nonquery ratio: absolute 96 | Query-only minimum: absolute 96 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 4,194,304 | 26 | 0.023437501 | 232 | 100,663,297 | 309 |
| 4 | 16,777,216 | 27 | 0.093750001 | 142 | 402,653,188 | 189 |
| 8 | 67,108,864 | 28 | 0.375000004 | 116 | 1,610,612,750 | 155 |
| 16 | 268,435,456 | 29 | 1.500000013 | 106 | 6,442,451,000 | 141 |
| 32 | 1,073,741,824 | 30 | 6.000000054 | 101 | 25,769,804,004 | 134 |

The paper work-factor 96-bit nonquery ratios fit for `B=2,4,8` and fail
for `B=16,32`; the complete native proof and cost remain unknown. All **absolute** 96-bit
nonquery ratios exceed one by many orders at this `N,T`. The absolute 80-bit
nonquery ratios also exceed one at every `B`. At `T=1`, 96-bit
absolute nonquery arithmetic fits only `B=2` for this height; higher blowups
increase the first-fold bound enough to fail. This is an unusually strong
illustration that **more blowup and more queries alone do not solve the
published absolute-error field-size terms**.

An even broader necessary condition ignores `N`, `B`, and every fold. Lemma 7
has OOD numerator at least one and denominator below `q⁴<2¹²⁴`; Theorem 6
multiplies the largest round bound by `T+R≥T`. Its quoted expression is
therefore **strictly greater than** `T/q⁴`. For `T≥2²⁸` this alone exceeds
`2⁻⁹⁶`. The arithmetic is formalized in
[`StwoUDRFeasibility.lean`](../../../formal/s31/S31/Gadgets/PcsFri/StwoUDRFeasibility.lean).
Thus **QM31 cannot certify an absolute 96-bit bound through this ungrinded
published envelope at a hash-query budget of `2²⁸` or more**, regardless of
domain or raw query count. This statement is scoped to the quoted theorem
and zero proved grinding credit. After dividing by `T`, the same universal
necessary term becomes `1/q⁴`, slightly greater than `2⁻¹²⁴` but below
`2⁻⁹⁶`; it **does not obstruct** a paper
work-factor 96-bit claim. The hypothetical `T=2³²`, `s=232` calculation
above demonstrates paper-style numerical feasibility. A larger challenge
field, a proved reduction
that gives effective grinding credit to the limiting round, or a stronger
theorem may change the absolute-error conclusion.

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
3. Prove the exact native query sampler matches the theorem's query
   distribution and projection model, plus the FRI fold, insertion, and
   terminal checks.
4. Prove the native BLAKE2s transcript, Merkle authentication, challenge
   domain separation, and any PoW credit instantiate the paper's BCS/ROM
   bound for a declared adversary budget `T`.
5. Recompute every bound with actual parameters. Preserve the 96-bit target
   and state whether it means the paper's `ε(T)/T` work-factor convention or
   an absolute `ε(T)` claim. A paper-style arithmetic pass is not an automatic
   native-security claim.
