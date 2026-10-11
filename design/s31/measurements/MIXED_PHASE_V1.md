# Mixed prover native phase timing v1

The source-embedded mixed prover now has an opt-in timing path that measures
interaction proof of work and the FRI proof of work inside PCS. The opt-in
path emits `S31_MIXED_NATIVE_PHASE_V1` on stderr. These values do not enter
the proof transcript. The ordinary package stage report still measures one
outer `native_prove_including_setup_ns` interval.

This first study checks whether enabling that instrumentation preserves the
proof and whether the reported intervals account for a subset of native
proving. It is **not** a predictive whole-prover cost model. An earlier
360-trial cross-shape transfer remains unscored because the exact prior
training model bytes were not retained; none of its timing observations is
fitted here.

## Frozen local diagnostic

The [protocol](language/mixed-phase-v1-protocol.json) was committed before
the first package build with SHA-256
`f004af8901a1cd601e26fdec37fa075f54d24851b665245908e3568cb06bb303`.
Its final prebuild commit is `5450f61`; earlier protocol revisions were
superseded before native work. The protocol pins the engine commit,
compiler fingerprint, Zig executable, anonymized
host identity, measurement tool bytes, source template, and 60 new source,
assignment, and statement identities. Two record ABI v2 programs have N=2
and N=6 live 16-round chip calls. Each uses 30 distinct public statements.
Those statements and assignments are disjoint from the earlier transfer and
mixed model train/held-out protocols.

The compact [result](language/mixed-phase-v1-result.json) has SHA-256
`2eeec0a19de95510eeb6a8927ddd81d38ed9214b3f1e107649846eff7167f514`.
The [native replay audit](language/mixed-phase-v1-audit.json) has SHA-256
`eb6f1f46419d573122c9fe23e08c74a5773aed9925bf9dc47956e04a14d37e66`.

One ReleaseFast prover/verifier pair is built per source. For each statement,
the same binary proves once with `S31_MIXED_NATIVE_PHASES=1` and once with
the variable unset. Even assignment indices run ordinary first; odd indices
run instrumented first. Each result must satisfy all these checks:

1. The emitted statement equals the frozen, canonical ABI v2 statement.
2. Both proofs are byte identical and accepted by the source-embedded native
   verifier.
3. Mutating exactly one public result word leaves a valid decoded eight-word
   ABI statement. Both proof checks must reject at the transcript interaction
   nonce, specifically `InvalidMixedInteractionNonce`.
4. The instrumented run emits one phase record with the same source/circuit
   identity and outer native interval as the ordinary package stage record.
   The uninstrumented run emits no phase record.
5. The six package intervals sum to package total. Interaction and FRI proof
   of work are positive, fit inside their parent intervals, and their sum
   does not exceed native proving. `native_without_reported_pow_ns` and
   `pcs_without_fri_pow_ns` are arithmetic differences.

The runner retains all raw proofs, statements, binary hashes, build logs,
and stderr in the ignored `zig-out` path. A separate read-only auditor checks
the compact tracked result against those files and can rerun all native
verifier controls. The exact commands are in the [study README](../../../src/frontends/s31/benchmarks/mixed_phase_v1/README.md).

## Observed result

All **60 pairs** produced exactly equal proof bytes and source-bound public
statements in both modes. All 120 original proofs passed the native verifier;
all 120 changed-result claims were rejected at
`InvalidMixedInteractionNonce`. The read-only audit rehashed every raw
proof, statement, binary, and stage line, then repeated all 120 original and
120 changed-result native verifier calls successfully.

All times below are medians over 30 distinct statements in each program.
Build time is one package build per source. KiB means 1024 bytes.

| Live chip calls | Timed / untimed native prove incl. setup | Interaction / FRI PoW | Timed native minus reported PoW | Timed / untimed first-verified process wall | Proof size | Package build |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 105.92 / 110.49 ms | 1.69 / 101.47 ms | 2.66 ms | 129.40 / 136.69 ms | 82.91 KiB | 55.18 s |
| 6 | 67.19 / 67.41 ms | 1.45 / 59.34 ms | 4.69 ms | 93.71 / 94.81 ms | 139.40 KiB | 54.39 s |

The median *per-trial* fraction of native time in the two reported PoW
intervals was 97.5% for N=2 and 92.6% for N=6. That fraction is computed
within each timed proof before taking the median; it is not a ratio of the
table medians. Native intervals ranged from 5.38 to 449.31 ms for timed N=2
and 9.35 to 384.78 ms for timed N=6. This wide spread, driven in part by
nonce search and potentially host scheduling, prevents interpreting the
lower N=6 median as a faster six-call implementation. The median paired
timed/untimed native ratios were approximately 0.998 and 1.009 for N=2 and
N=6 respectively; proof identity is established, while timing overhead is
not resolved precisely by this local sample.

The engine's optional timing records have established a useful next cost
feature: FRI PoW can dominate the native interval for these small mixed
programs. A reliable model needs to explain that random and host-sensitive
work separately from source-dependent computation, then validate on a
prospectively frozen held-out cohort. Neither this result nor the older
unscored cross-shape corpus is such a validation.

## Interpretation

First-verified wall includes a fresh prover process and external native
verifier process. Source package build is a separate, one-time cost. The
recorded native interval includes setup and all proof work. The two proof
of work timers are only a partial decomposition; the arithmetic residual
contains setup, trace construction, commitments, other PCS work, and timer
overhead. It must not be interpreted as one separately executed stage.

Host scheduling and concurrent builds can dominate tens-of-milliseconds
process samples. This local diagnostic reports observations and proof
identity, not a speedup or a worker policy. A reliable predictor needs a
new prospective source and claim split, phase-aware features, a quiet host,
and an exact training-only model artifact committed before held-out work.
