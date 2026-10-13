# S-two 2026 multi-domain FRI: Gate parameter ledger

The user selected a **proven conservative** release profile. This ledger
tests the published [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf),
Theorem 4 and Appendix A Theorem 11, against one conditional Gate geometry.
The [official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
summarizes the protocol and explicitly warns that the currently implemented
non-squaring-consistent circle query variant lacks the full list-decoding
proof in the paper. The older [Circle STARKs 2024](https://eprint.iacr.org/2024/278.pdf)
Remark 26 calculation is a **different** theorem envelope. The argument here
uses the newer paper's own multi-domain fold bound.

## Reproduce

```sh
python3 -B scripts/release/pcs_fri_stwo_multidomain.py /path/to/locally-trusted-sealed-gate-package
python3 -B scripts/release/pcs_fri_stwo_multidomain.py /path/to/locally-trusted-sealed-gate-package --require-proven
```

The second command exits 2. The script calls the existing Gate geometry
extractor, which checks the native key using a **locally trusted** package
binary. Its hashes do not independently authenticate that binary. The result
remains `proven_release_admissible: false` with null native security bits.
All changed-blowup rows are hypothetical theorem arithmetic: the native key
and constructor remain at blowup 2, fold step 1, and 70 raw queries.

## Hand calculation: one fold already controls the Johnson envelope

Assume, *only for this calculation*, that the native Gate maximum trace
height maps to the paper's `N=2^20`, its initial FRI oracle to `D₀=N·B`, and
its challenge field to `F=QM31` of order `(2^31−1)^4`. The paper's first line
domain has `S₀=D₀/2`. The line-code rate in Theorem 4 is

```text
ρ₀ = 1/B + 1/|S₀|,
ℓ₀ = (m+1)/(2√ρ₀), with m ≥ 3,
ε_fold,0 = 3ℓ₀ · (2ℓ₀⁴/(3ρ₀) + 1) · |S₀|/|F|.
```

At `B=2`, `S₀=2^20`, `ρ₀=524289/1048576`, and `ℓ₀` is at least about
`2.828`. The positive leading term of the paper's **upper-bound expression**
is `2ℓ₀⁵|S₀|/(ρ₀|F|)`, already greater than `2^-95`. Adding its remaining
positive term cannot make the quoted upper bound smaller than `2^-96`.

The result extends across every `B≥2` for this candidate height. Since
`S₀≥2^20` and `ρ₀≤1/2+1/2^20<9/16`, multiplicity `m≥3` gives `ℓ₀>8/3`.
The favorable rational floor

```text
2 · (8/3)^5 · 2^20 / ((9/16) · (2^31−1)^4) > 2^-96
```

is checked by the Lean theorem
`S31.PcsFri.StwoMultidomainEnvelope.favorable_first_fold_floor_exceeds_96`.
Its companion Lean theorem checks the stated line-rate bound for all
`N≥2^20,B≥2`. Python additionally computes tighter rational floors using
integer square-root intervals, with no floating-point comparison.

This is a **limit of the quoted proof envelope**. An upper bound larger than a
target does not imply that a prover can cheat at that probability, nor that a
tighter or different theorem is impossible. Without a native-to-Protocol-3
refinement, even the candidate substitution is conditional.

| Hypothetical `B` | Johnson first-fold envelope exceeds | Unique-decoding raw queries needed at excluded `θ=δ/2` boundary | Max BCS adversary hash queries `T` allowed by quoted unique-decoding first-fold term alone at 96 bits, assuming `R≥1` |
| ---: | ---: | ---: | ---: |
| 2 | `2^-95` | 232 | 84 |
| 4 | `2^-91` | 142 | 41 |
| 8 | `2^-86` | 116 | 20 |
| 16 | `2^-82` | 106 | 9 |
| 32 | `2^-77` | 101 | 4 |

These `B` values are the entire power-of-two candidate set satisfying the
paper's circle-domain capacity `N·B²≤2^30` at `N=2^20`. Every first-fold
entry concerns the published *Johnson upper bound*, not real attack odds.

## Unique decoding is numerically different, but not a release certificate

The whitepaper's Remark 9 gives the much smaller unique-decoding first-fold
bound `3|S₀|/|F|` for `θ<δ/2`. The query error is still `(1−θ)^s`, so the
current `B=2,s=70` configuration cannot use this route at 96 bits. At the
excluded boundary `θ=δ/2`, the query expression is `(3/4)^s`; **232** is the
smallest `s` for which this limiting expression falls below `2^-96`.
An actual `θ<δ/2` must be chosen and checked separately. A 26-bit native PoW
setting receives no automatic soundness credit.

The BCS/NIROP theorem (Theorem 6) then multiplies the largest interactive
round error by `T+R`. For `B=2` and `T=2^32`, the quoted unique-decoding
first-fold term alone contributes more than `2^-71` after this multiplier,
even with only `R=1` and every other round/collision term omitted. Thus the
quoted theorem with QM31 and this height cannot certify 96 bits for that
explicit hash-query budget. The default `T=2^32` in the checker is a
**hypothetical analysis budget**, not a property of the native prover or an
established threat model. The `T` limits in the table ignore the other
positive terms and are only necessary ceilings.

## Missing before any native claim

The checker leaves logUp, composition, OOD, batching, all actual FRI folds,
query-distribution refinement, BCS round count, Merkle binding, and binary
correspondence unbound. Theorem 5's degree-corrected batch OOD relation also
requires both quotient and non-quotient words to be tested. The paper notes
the current implementation's quotient and query-sampling variations; these
must be separately reconciled. The native FRI terminal and sampled-opening
checks, even when independently tested, do not discharge the cryptographic
relation or BCS/ROM hypotheses.

The immediate design direction for a conservative profile is to evaluate a
larger challenge field or a substantially stronger theorem/refinement, then
choose a new native query and blowup tuple. Merely increasing the 70 queries
cannot repair the first-fold Johnson envelope or the illustrated `T=2^32`
BCS budget. Any such change needs measured prover costs and a new package key.

Focused checks:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_stwo_multidomain -v
cd formal/s31 && lake env lean S31/Gadgets/PcsFri/StwoMultidomainEnvelope.lean
```
