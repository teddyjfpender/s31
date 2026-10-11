# Prospective mixed whole-prover cost baseline v2

This is a new prediction study on the phase-timed engine. It starts from a
frozen protocol, trains on four source programs, commits the exact model bytes,
then measures four different held-out programs. The earlier mixed-stage v1
transfer remains unscored because its frozen model bytes were lost. This v2
study never uses that old timing corpus for fitting or interval selection.

## Workload and prediction target

All programs use record ABI v2, the source-embedded `direct-mixed-general`
profile, and 20 new public assignments each. The source shapes are:

| Split | Sources | Purpose |
| --- | --- | --- |
| Training | `control_n2`, `control_n6`, `deep32_n2`, `deep32_n6` | Two call counts and both 16- and 32-round chains |
| Held out | `feeder_n4`, `feeder_n6`, `fork_n4`, `fork_n6` | New circuit shapes, one interpolated count |

The target is the sum of one fresh prover-process wall and one fresh external
native-verifier-process wall. Package build is reported separately and has no
prediction. Each accepted proof also records all six package stages, the
interaction and FRI PoW intervals, proof bytes, and source/binary identity.
Post-proof timing is **never** a predictor feature. A valid changed public
result must be rejected at `InvalidMixedInteractionNonce` for every proof.

The preregistered model predicts first-verified wall as the median of four
training-program wall medians. It predicts proof bytes by ordinary least
squares against live chip call count on four training-program proof medians.
A constant proof-size baseline is saved for comparison. Training-trial 5th
and 95th percentile actual/predicted ratios, clamped to include one, form
empirical bands; these are not confidence intervals. The held-out diagnostic
requires wall program-median p90 relative error at most 30%, proof p90 at
most 10%, wall-trial band coverage at least 70%, and proof-trial band coverage
at least 80%. All four gates, source/claim disjointness, and native audit must
pass to call this baseline locally accurate for the pinned host/profile.
Even a pass does not support cross-host reliability, tail latency, automatic
lowering, or a speedup claim.

## Chronology

Run from the S31 repository root on a quiet host. Each phase refuses a
changed engine, compiler, tool byte, host identity, source, or claim.

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py prepare
# Review and commit protocol before any native build.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py train \
  --out zig-out/s31-mixed-cost-v2
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py audit-train \
  --out zig-out/s31-mixed-cost-v2
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py fit \
  --out zig-out/s31-mixed-cost-v2
# Review and commit train corpus, model.json, and model-anchor.json.
# Record the exact model SHA-256 and full model-anchor commit before heldout:
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py heldout \
  --out zig-out/s31-mixed-cost-v2 \
  --model-sha256 <exact model SHA-256> --model-anchor-commit <full commit>
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py audit-heldout \
  --out zig-out/s31-mixed-cost-v2
python3 -B src/frontends/s31/benchmarks/mixed_cost_v2/study.py evaluate \
  --out zig-out/s31-mixed-cost-v2 \
  --model-sha256 <exact model SHA-256> --model-anchor-commit <full commit>
```

`fit` repeats native verification of every training proof and its mutated
claim before producing the model. The held-out runner reads the exact model
and anchor bytes from the named ancestor commit **before its first build**.
`evaluate` repeats native verification of every held-out proof and changed
claim. The raw output retains proofs and logs; the compact tracked corpora
and model alone cannot replay native verification. Any failed partial phase
must be restarted in a fresh raw directory under a new protocol/version.
