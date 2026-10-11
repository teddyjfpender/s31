# Mixed native phase paired diagnostic v1

This study compares the same source-embedded prover binary with optional
native phase telemetry off and on. It is a diagnostic of instrumentation
identity and whole-prover accounting. It does **not** fit a predictive model,
establish a speedup, or evaluate a held-out cohort.

The [committed protocol](../../../../../design/s31/measurements/language/mixed-phase-v1-protocol.json)
was frozen before any native package build. It pins engine commit
`f889c2a03f4e8ae5e4a9e2db39f26c5b6a315719`, compiler fingerprint, Zig
executable, frontend/runtime tool bytes, source template, two source hashes,
and 60 new assignment and typed-statement hashes. The roster has 30 distinct
statements each for two and six live 16-round chips. None of these statements
or assignments is reused from the earlier mixed transfer cohort. The
protocol SHA-256 is
`f004af8901a1cd601e26fdec37fa075f54d24851b665245908e3568cb06bb303`.
The earlier protocol commits `7722767`, `309b091`, and `98ad2ea` were
superseded before any native build. The final runner pins a host identity and
proves each changed public result is a
valid eight-word ABI statement and requires the exact transcript nonce
rejection `InvalidMixedInteractionNonce`. An output equality rejection alone
does not satisfy this control.

For each statement, the runner alternates process order by assignment index,
executes timed and untimed proving using the **same binary**, verifies both
proofs with the same source-embedded native verifier, and requires byte-for-byte
proof and statement equality. A changed public result must be rejected for
both modes. Timed stderr must contain exactly one phase record, with source
and circuit identity equal to the ordinary package stage record. All phase
subtractions are checked against the native total. The untimed path must not
emit the phase record. All 120 proofs and their logs remain in the ignored
raw output path; the compact result is tracked under `design/s31/measurements/language/`.
Each changed result is decoded against the same source and ABI before the
verifier runs. A preflight parser rejection does not count as a negative
proof check.

Run from the S31 repository root on a quiet host:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_phase_v1/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_phase_v1/study.py run \
  --out zig-out/s31-mixed-phase-v1-20261011
python3 -B src/frontends/s31/benchmarks/mixed_phase_v1/audit.py \
  --out zig-out/s31-mixed-phase-v1-20261011 --native
```

The runner refuses a changed protocol, compiler, engine gitlink, tool file,
source template, or generated claim. Package build time is measured separately
from the fresh prover and external verifier process wall. The phase report
separates interaction PoW and FRI PoW from the opaque native prove interval;
`native_without_reported_pow_ns` is an arithmetic difference, not another
timer. Timings remain sensitive to host scheduling. A later cost predictor
needs a new prospective train and held-out split, an isolated host, and the
exact training-model bytes committed before held-out native work.

The read-only audit checks the committed compact result against all raw
assignment, statement, proof, binary, and stderr files. `--native` also
reruns every original and changed-result verifier check. The raw directory
must be retained to repeat that audit; the compact tracked result alone
cannot rerun native verification.
