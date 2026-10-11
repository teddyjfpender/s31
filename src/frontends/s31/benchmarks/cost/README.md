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
