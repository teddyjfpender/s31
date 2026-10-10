# Arithmetic RSS follow-up, predeclared v2

The [machine-readable protocol](arithmetic-rss-v2.json) is pinned before any
v2 native package build or proof timing. This is a **targeted follow-up** to
the arithmetic peak RSS failure in [stage-aware v1](STAGE_AWARE_COST_V1.md).
It is not a replacement validation of all whole-prover targets.

The v1 training programs show a fixed prover memory baseline plus increasing
memory as padded arithmetic rows grow. An ordinary log-linear line cannot
represent a fixed byte baseline. A positive affine model is a physical
hypothesis: one process/runtime baseline and one per-padded-row allocation
term. On the **v1 training split only**, leave-one-program-out errors for this
candidate were 0.25%, 0.38%, 3.81%, 2.77% and 5.05%. The v1 validation
programs revealed the original failure, so they are development evidence and
will never be used to claim that this candidate was validated.

The new training split uses five source programs at rounds 24, 96, 384, 1536
and 6144. The independent validation split uses four new round counts 48,
192, 768 and 3072 in **two** bodies: `square; add 11` and `square; multiply 3;
add 11`. This tests interpolation across padded tiers and transfer to another
direct-gate recurrence body. All programs have twenty distinct deterministic
witnesses; train and validation seeds and source digests must be disjoint.
Every trial requires native proof acceptance, changed-public-claim rejection,
and independent value-oracle agreement. The compiler fingerprint and proof
policy must match across the entire run.

Fit the positive affine model on training program **medians** only. Freeze the
model file before validation package builds. For context, fit a training-only
log-linear baseline in the same file; do not select a model by validation
error. The candidate interval adds the maximum training leave-one-program-out
absolute error to empirical training within-program p05/p95 residuals. It is
a diagnostic interval, not a calibrated confidence interval. The protocol
pins p90/max point-error, per-body interval coverage and interval-width gates.

The full prover wall, proof bytes, verifier wall and other stages may be saved
as raw telemetry, but **only prover peak RSS** enters this v2 accuracy gate.
Even a local pass cannot enable automatic lowering: other families, hosts,
full-process latency, proof bytes, cached setup and proof-profile soundness
still need independent validation.
