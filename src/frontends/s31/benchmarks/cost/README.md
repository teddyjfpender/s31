# Whole-prover model transfer

`transfer_v1.py` checks whether the frozen V6 whole-prover predictor still
describes the changed S31 compiler on the same host. Its eight generated
programs cover arithmetic, direct chip, hash, and fixed-width division.
The script does not fit a new model or select lowering automatically.

The `freeze` phase writes the protocol, including exact source and assignment
digests, compiler and engine revisions, tool bytes, host identity, V6 audit
digest, target list, and accuracy thresholds. Commit that protocol before
running a native build. The `run` phase checks the committed bytes and pins,
builds fresh packages, and runs ten independent assignments per program.
Each trial verifies a native proof, rejects a changed public claim, and checks
the result with an independent value oracle. Raw artifacts remain under
`--out`; the resulting `audit.json` is a compact summary.

```sh
python3 src/frontends/s31/benchmarks/cost/transfer_v1.py freeze --out zig-out/s31-cost-transfer-v1
git add design/s31/measurements/language/whole-prover-transfer-v1.json
git commit -m 'Freeze V6 transfer protocol'
python3 src/frontends/s31/benchmarks/cost/transfer_v1.py run --out zig-out/s31-cost-transfer-v1
```

A passing diagnostic is evidence only for this host, these eight programs,
these ten trials per program, and this compiler revision. It cannot certify
cross-host performance, tail latency, or automatic lowering decisions.

## Replay saved evidence

After `run` has completed, `replay_transfer_v1.py` checks the protocol against
freeze commit `5fbf2fc`, requires the Python code used by the study and oracle
to match that commit, and reopens all eight sources, 80 assignments, saved
proofs, trial reports, statements, package manifests, and cost reports. It
recomputes V6 predictions and diagnostic gates independently of `transfer_v1.py`.

```sh
python3 src/frontends/s31/benchmarks/cost/replay_transfer_v1.py --out zig-out/s31-cost-transfer-v1
python3 src/frontends/s31/benchmarks/cost/replay_transfer_v1.py --out zig-out/s31-cost-transfer-v1 --native
```

The default run verifies hashes, source and assignment disjointness from both
V6 splits, saved statement mutation, and the Python value oracle. `--native`
also reruns each saved proof against its original and changed public statement.
Neither mode builds packages or changes the frozen runner, protocol, thresholds,
or saved evidence. A successful replay reports what was checked; it does not
turn a failed diagnostic into a pass or establish compiler or proof soundness.
The freeze commit preceded the first local native build, but its full hash was
not independently timestamped before observation, so this remains a local
same-host diagnostic rather than a fully anchored prospective acceptance gate.
