# P10: grouped FRI folds need a separate soundness reduction

**Status:** open. This note supplies an algebraic bound and an exact finite
counterexample to treating a four-fold group as four independent published
rounds. It does not establish a native PCS/FRI security level or make a
fold-step-4 release profile proven-admissible.

## Published protocol and pinned native schedule

The [Circle STARKs paper, Appendix B, Protocol 2 and Theorem 6](https://eprint.iacr.org/2024/278)
analyzes a cascade of single-fold commitment rounds. The
[official S-two whitepaper theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
describes its multi-domain circle FRI as per-level folds with challenge
`λᵢ`, and its folding-error term is a round-by-round reduction. The S-two
paper distinguishes the proven Johnson regime from its conjectural parameter
regimes. Neither cited theorem, as stated, supplies an error bound for the
native group below by simply multiplying four single-fold errors.

In the pinned `59e1f115` stwo-zig engine, [`fri.zig`](../../../deps/stwo-zig/src/core/fri.zig)
mixes one committed layer root and draws one `folding_alpha` for that layer.
[`folding.zig`](../../../deps/stwo-zig/src/core/fri/folding.zig) then uses:

```text
one authenticated group, fold_step = 4
  first butterfly:  α
  second:           α²
  third:            α⁴
  fourth:           α⁸
  commit next group output and only then draw its new challenge
```

The first grouped layer starts with a circle-to-line butterfly using the
inverse circle `y` coordinate. The implementation clears its destination
buffer before that fold, then performs three line butterflies using inverse
`x` coordinates. Inner grouped layers perform four line butterflies. The
existing [source-shape guards](../../../scripts/s31_formal_lib/pcs_fri_fold.py)
and [challenge-custody guard](../../../scripts/s31_formal_lib/pcs_fri_challenge_custody.py)
pin these call sites and the one-draw-per-committed-layer structure; they do
not prove Zig operational semantics or a cryptographic reduction.

## What the Lean result establishes

[`GroupedFoldSchedule.lean`](../../../formal/s31/S31/Gadgets/PcsFri/GroupedFoldSchedule.lean)
models a complete binary tree of inverse butterflies with **fixed** opened
values and fixed inverse coordinates. Its `eval_polynomial` theorem identifies
the tree output with evaluation of one polynomial in `α`; its
`polynomial_natDegree_le` theorem bounds degree by `2^n−1`. Thus four local
butterfly levels have degree at most 15 in the one group challenge. This
provides an exact algebraic interface for a future grouped-round argument.
It does not account for all multi-domain insertions, prove that opened values
were fixed before `α`, or show proximity to a lower-degree code.

The same file proves a concrete **distributional obstruction**. Let
`q = |F| > 1` and let `E(a,b)` mean `a=0` and `b=0`. Under a uniform native
seed, the first two challenge values are `(α, α²)`, so `E` holds for exactly
one of `q` seeds: probability `1/q`. Under two independent uniform field
draws, `E` holds for exactly one of `q²` pairs: probability `1/q²`.
`grouped_zero_event_exceeds_independent` proves the strict inequality by
cross multiplication of those exact finite counts. This toy event is **not
an FRI attack**; it proves that fresh-challenge event probabilities cannot
be substituted unchanged for the native correlated schedule.

## Exact next proof obligation

For each group, fix the authenticated input oracle and any batched column
oracles **before** drawing `α`. Prove a multi-domain correlated-agreement
reduction for the whole `2⁴`-to-1 map with the actual circle-to-line step,
`α²` insertion weights, subsequent line folds, degree transition, and
commitment of the group output. The theorem must bound the probability that
a far input yields a close output as one function of the **single** uniform
`α`, with explicit field size, list bound, domain geometry, and degree
parameters. It must cover adaptive prover choices *between* groups while
preventing choices *within* a group after that group's challenge. Only then
can its group error be composed with authenticated query checks, the native
M31-masked query law, Merkle binding, and the Fiat–Shamir/BCS budget.

The [v0.1 blocker matrix](pcs-fri-v01-blockers.json) therefore retains
`P10_GROUPED_FOLD_SCHEDULE` for both fold-step-4 profiles. The
[published-bound preflight](../../../scripts/release/pcs_fri_proven_preflight.py)
continues to reject `fold_step != 1` when asked for a proven profile. Other
PCS/FRI obligations remain open for every profile.

Reproduce the local formal check without a native prover build:

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.GroupedFoldSchedule
```
