# Post-hoc check of the V11 process-wall method change

This diagnostic was run **after** the single V11 prospective run failed
14/16 gates. It neither changes the frozen V11 result/score nor fits a new
model. The [script](../../../src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/posthoc_method_check.py)
used the exact saved source-pinned gate-only and joint binaries, the same
scored claim-1 assignment and statement, and a saved proof for fixed-verifier
measurements. It authenticated saved binary/claim hashes before starting.
Each of 16 prover pairs and 24 verifier pairs per source invoked the same
native command once bare and once under `/usr/bin/time`, with balanced,
deterministically shuffled order. Every newly generated proof was verified
by the saved native verifier. The new proofs are **diagnostic only**.

| Saved source | Median paired prover wall delta, time−bare | Median paired prover wall-minus-reported-PoW delta | Median paired fixed-verifier wall delta |
| --- | ---: | ---: | ---: |
| gate-only log 11 | +6.30 ms | +6.66 ms | +5.42 ms |
| joint log 11 | +4.34 ms | +6.82 ms | +6.59 ms |

The prover residual pairs reduce the large random FRI PoW variation by
subtracting each process's native reported interaction and FRI PoW time. The
approximate combined process-method shift is around 12–13 ms for these two
saved sources. Gate-only V11 observed wall p50 exceeded its frozen prediction
by 92.88 ms, and its FRI PoW p50 exceeded the joint source's by 55.89 ms.
The wrapper shift therefore cannot by itself account for the gate-only wall
miss. These paired numbers are local, post-hoc, and not a correction to the
V11 forecast; proof generation still has stochastic PoW and the diagnostic
was not randomized at the program level.

The canonical [diagnostic artifact](language/mixed-cost-v11-posthoc-method-check.json)
has SHA-256 `e041d0afbaaa2d5bac6c8c9f82a69b2f04058762dc2292cee7cc62388edb0e0e`.
It retains pair order, timing values, native phase splits, new proof hashes,
and OS resource-report hashes. The raw 7.2 MB diagnostic proof/resource files
are local under `/tmp/s31-v11-unseen-d85fe72/posthoc_method_check`. The
frozen V11 14/16 failed score remains unchanged.
