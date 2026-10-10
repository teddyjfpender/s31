# Proof runtime

`trials.py` builds or loads a sealed package, asks the native prover for a
proof, runs the package's native verifier, then changes one public word and
requires that verifier to reject the altered claim. It records an independent
value-oracle result when the relation is supported, source equations, cost,
proof size and stage timings. `tune` repeats this process across explicitly
selected lowerings; it does not automatically claim one profile is sounder or
faster from a single run.

`folds.py` verifies each saved recursive fold checkpoint and checks contiguous
step numbers, fixed key and commitment fields, and public state continuity.
For supported four-lane state transitions it also independently replays the
source step between checkpoints. The native verifier remains responsible for
cryptographic proof verification at each checkpoint.

The root `../s31.py` imports these functions as its stable Python API and
provides the CLI. Runtime source files are included in the package compiler
fingerprint because they influence trial evidence and verification commands.
