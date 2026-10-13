# P05: native quotient-only FRI and degree correction

**Status:** open. This is a theorem-applicability finding for the pinned native
engine, not an exploit or a proof that every quotient-only protocol is unsound.
The v0.1 proven-release gate remains closed.

## The published premise

The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf), batch-evaluation
protocol `prot:cFRI:batch:eval:degree:corrected` and theorem
`thm:cFRI:batch:eval:degree:corrected:soundness`, tests an **extended ensemble**:
the original, nonquotient polynomial words as well as their OOD quotient words.
The [authors' theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
identifies this ensemble as equation `e:cFRI:batch:eval:extended:ensemble` and
separately states the weaker uncorrected relation `e:cFRI:batch:eval:relation:plus`.
The theorem also has degree and small-table hypotheses, including the latter's
`1 - θ > (1 - δ)(1 + 2/N_t)` condition. The release ledger has not instantiated
those parameters for the native path.

## What the pinned engine actually checks

The inspected S31 engine gitlink is
`59e1f115250b8af01712b9bf3d71616e53094964`.

1. [`scheme.zig`](../../../deps/stwo-zig/src/prover/pcs/scheme.zig) builds one
   `LazyQuotientProvider` from committed columns, claimed samples and a DEEP
   random coefficient, then passes that provider to one `FriProver.commitLazy…`.
2. [`verifier.zig`](../../../deps/stwo-zig/src/core/pcs/verifier.zig) constructs
   one `FriVerifier` at the lifted-domain degree bound. After Merkle opening
   checks, it calls `quotients.friAnswers` and passes those answers to
   `fri_verifier.decommit` (or its capture variant).
3. [`fri_answers.zig`](../../../deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig)
   returns one `[]QM31` whose entry at each query is the accumulated row
   quotient. The original row values are authenticated at the tree roots and
   used to calculate this word. They are not independently fed to FRI as
   nonquotient words with their own degree bounds.

The [source-bound audit](../../../scripts/release/pcs_fri_degree_correction.py)
locks this classification to the exact reviewed gitlink and seven source file
hashes. Source changes cause rejection and a fresh review. It emits
`published_degree_corrected_nonquotient_premise_met: false`; `--require-p05`
exits 2. The [v0.1 blocker matrix](../../../scripts/release/pcs_fri_v01_blockers.py)
runs the audit and keeps P05 open.

Merkle authentication binds queried **values** to roots under a collision
assumption. It does not prove the entire original committed word has the
claimed polynomial degree. Likewise, a local algebraic identity for a
quotient does not provide that missing degree claim.

## A hand example of the logical gap

Use ordinary polynomials for a minimal illustration. Claim `f(0) = 0`, set
`q(X) = X` and `f(X) = X²`. Then

```text
f(X) = (X - 0) q(X) + 0
deg q = 1 < 2
deg f = 2, so deg f < 2 is false
```

The [Lean file](../../../formal/s31/S31/Gadgets/PcsFri/DegreeCorrectionGap.lean)
checks these statements. It is an example of an invalid *inference*, not a
native-circle or adversarial-proof construction. A quotient checked against a
different, strictly tighter bound may behave differently; exact native bounds
and the theorem relation must be proved together.

## Required discharge

Either implement the published quotient-plus-nonquotient ensemble and prove
that native prover/verifier control flow, domain lifting and degree bounds
refine it, or prove an alternative theorem for the actual quotient-only
protocol with its own list/agreement and error bounds. Both routes additionally
need committed-column ownership, OOD sample custody, exact Zig-to-model and
installed-binary correspondence, and all parameter hypotheses. This audit
supplies none of those positive proofs.

The separate [OOD seed geometry audit](PCS_FRI_OOD_SEED_GEOMETRY.md) pins the
native rational circle map and identifies exceptional and quadratic-subfield
seeds that must be handled in the exact sampling/distribution argument.
