# Proof runtime

`trials.py` builds or loads a sealed package, asks the native prover for a
proof, runs the package's native verifier, then changes one public word and
requires that verifier to reject the altered claim. It records an independent
value-oracle result when the relation is supported, source equations, cost,
proof size and stage timings. `tune` repeats this process across explicitly
selected lowerings; it does not automatically claim one profile is sounder or
faster from a single run.

`cost_model.py` measures complete native prover and verifier process wall time
and OS high-water resident memory when available. `trial` and `tune` include
an observed cost summary with stage completeness and variability. Every trial
starts a new prover and pays cold native setup. The corpus command and exact
interpretation of these measurements are in
[`design/s31/measurements/WHOLE_PROVER_COST.md`](../../../../../design/s31/measurements/WHOLE_PROVER_COST.md).

`folds.py` verifies each saved recursive fold checkpoint and checks contiguous
step numbers, fixed key and commitment fields, and public state continuity.
For supported four-lane state transitions it also independently replays the
source step between checkpoints. The native verifier remains responsible for
cryptographic proof verification at each checkpoint.

The root `../s31.py` imports these functions as its stable Python API and
provides the CLI. Runtime source files are included in the package compiler
fingerprint because they influence trial evidence and verification commands.
