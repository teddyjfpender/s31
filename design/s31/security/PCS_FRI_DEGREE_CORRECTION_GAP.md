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
locks this classification to the exact reviewed gitlink and nine source-file
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

## Versioned Gate PCS bridge, with admission closed

The audit now emits `native_gate_epoch_trace`: 21 exact source locations from
the legacy direct-profile verifier through the core STARK verifier and PCS capture path. It
checks one ordered occurrence of every event in each function and pins all
nine reviewed files by SHA-256. This is a machine-checkable **source-shape**
boundary, not binary semantics. The trace establishes this current order:

```text
legacy wire → fixed root → public values → main root
→ lookup challenge and interaction claim → interaction root
→ composition challenge → composition root → OOD seed and AIR identity
→ sampled values and DEEP challenge → FRI commitment and queries
→ original Merkle row authentication → accumulated quotient answer → FRI check
```

The proposed selector `s31-gate-degree-corrected-pcs-v2-spec` is deliberately
**uninstalled** and `proof_admissible: false`. The minimum implementation path
preserves the first four root epochs and changes the PCS opening protocol
*after* the OOD claims:

| Boundary | Concrete change needed |
| --- | --- |
| Source roster | Construct one ordered roster of every committed fixed, main, interaction, **and composition** column, with its actual height, root epoch, OOD point, claimed value, and degree bound. The CAS07 311-column pilot excludes eight composition columns, so it cannot be admitted as this roster. |
| Prover FRI input | Replace the single `LazyQuotientProvider` input with an original-and-own-quotient ensemble for each roster word at its native height. The original word must undergo a degree test independently of its quotient. |
| Verifier FRI input | Replace the one `friAnswers` quotient word with an authenticated per-height pair. At every queried point, derive the original from its already authenticated tree opening and check its *own* two-point quotient against the same OOD claim and divisor. Verify both degree bounds in the multi-domain FRI relation. |
| Theorem join | Prove original/quotient whole-oracle ownership, two-point circle identity, lifted correlated agreement, every small-height condition, and exact native query and adaptive BCS error. The whitepaper's written theorem is for single-point quotients; its two-point extension still needs a proof or a sound published specialization. |
| Admission | Bind a distinct proof selector and native prover/verifier implementation to this profile; reject legacy postcard proofs as evidence for it. Instantiate the full error bound at `T=2^64` and require paper work factor at most `2^-96`. |

The [source-bound Gate/CAS07 roster audit](PCS_FRI_CAS07_GATE_ROSTER_AUDIT.md)
already records the four epochs and the missing composition columns. The P05
audit adds the exact core-verifier and PCS opening order and enumerates the
unsatisfied theorem premises in `proposed_degree_corrected_profile`. The
release blocker matrix rejects a forged positive selector or admission flag.

The narrowest plausible native adapter keeps the existing four Merkle roots.
`core/verifier.zig:verifyImpl` can continue to draw the OOD seed after the
composition root. `pcs/verifier.zig:verifyValuesImpl` already draws the DEEP
coefficient after mixing claimed OOD values, commits FRI layers, then samples
queries. A new paired provider could use that same post-OOD coefficient as its
batch scalar, so the **event order and number of draws can remain**. Its FRI
commitments and therefore later query values will differ, which requires the
new versioned selector; legacy proof bytes do not retain their meaning.

The required interfaces are precise. On the prover side,
`pcs/scheme.zig:proveValuesFromSamplesWithRecorderAndPhase` currently hands
`LazyQuotientProvider` to `FriProver.commitLazyWithWorkRecorderAndRootMixCapture`;
the latter accepts one lifted-domain quotient provider. The replacement must
expose original and own-quotient words by source height to a multi-domain FRI
commit. On the verifier side, `pcs/utils.zig:prepareTreeQueryPositions` maps
lifted queries to each existing tree, and `pcs/verifier.zig:verifyValuesImpl`
authenticates those projected rows before `friAnswers` computes one scalar
quotient. A multi-root source-opening adapter must retain tree/column/height
ownership, reconstruct **both** values for each paired FRI query from the
authenticated original row and its OOD claim, and pass the resulting per-height
words through new multi-domain FRI batching and fold checks. Merely adding an
original term to the current single lifted `[]QM31` first-layer answer would
not establish separate native-height degree bounds or the paper's correlated
multi-domain relation.

An [experimental original-word adapter](../../../formal/s31/tests/lib/p05_multi_root_original_batch.zig)
now implements the first sampled-row step on the *existing* proof-capture
interface. It invokes the independent four-root path and projection check,
then groups authenticated original values by native column log size. Within
each height it combines columns in tree/column order with successive powers
of the captured post-OOD DEEP challenge; it retains every raw query slot,
including duplicates, and the projected position. It reads no transcript
channel and does not change any commitment epoch. Restarting powers at one
for each height is an executable **candidate schedule**, not a proven match
to the paper's cross-domain batching coefficients. The
[small native control](../../../formal/s31/tests/pcs_fri_p05_multi_root_original_native.zig)
constructs four separate two-level Merkle roots, two column heights, one
projected query and one repeated raw query. It checks exact batch values and
rejects a changed row, composition-tree path, projected position, or root.
This establishes local **sampled original-row
reconstruction only**. The own quotients, a paired multi-domain FRI, whole
oracle degree bounds, and the theorem reduction remain absent; the v2 selector
and P05 admission stay false.

The [own-quotient row adapter](../../../formal/s31/tests/lib/p05_own_quotient_rows.zig)
adds the next local relation. It first rechecks all four source roots and raw
query projections. It then requires an independently supplied, ordered claim
roster with the exact tree, column, sample index, source height, OOD point,
and claimed value. For each explicit mask sample it derives the conjugate
two-point line and computes, at each authenticated lifted PCS row,

```text
own_q(row) = (c · original(row) − a · row.y − b)
             / ((P.x₀ − row.x) · P.y₁ − (P.y₀ − row.y) · P.x₁)
```

Here `a,b,c` are native `complexConjugateLineCoeffs(P, claim, 1)`, and the
subscripts are the CM31 components of the QM31 OOD point. A zero divisor or
non-circle OOD point is rejected. When a column has two explicit mask samples,
the adapter emits the native periodicity sample **before** both explicit
samples, preserving separate quotients and their owner identities. The
[four-root control](../../../formal/s31/tests/pcs_fri_p05_multi_root_original_native.zig)
checks exact agreement against native `friAnswers` for one sample and for the
three-term composition periodicity sequence. It rejects swapped claims,
changed paths, projected positions, rows, roots, and a zero divisor.

The expected-claim roster is **supplied externally by the test caller**. The
adapter compares its point and value, as well as tree, column, sample index,
and source height, against the verifier capture for every explicit sample.
It does not reconstruct that roster from an installed key or independently
authenticate the OOD claims. A real v2 verifier must derive the roster from
its accepted AIR/OOD relation and bind it to the public statement. This adapter
uses the pinned verifier's **lifted** row point and labels the source height;
the theorem still needs a proof that the native-height paired codewords and
lifted rows have the required relation. It has no whole-oracle degree test,
multi-domain FRI, or admission selector.

The opt-in raw Gate channel adds a separate transcript and proof/key format.
Its native verifier still calls the same core verifier and quotient-only PCS
path; changing the hash-to-field sampler does not supply the missing
nonquotient FRI degree test. The refreshed source pin covers the new
compile-time profile dispatch while the 21 checked legacy direct-profile
transcript events and the P05 negative conclusion remain unchanged. The
report marks `raw_gate_epoch_trace_evidenced: false`: it does not promote the
legacy event trace to the raw profile or claim an adaptive BCS theorem.
