# Mixed prover PoW worker diagnostic

The [frozen mixed transfer corpus](../../../../../design/s31/measurements/MIXED_STAGE_COST_TRANSFER_V1_UNSCORED_RESULT.md)
puts native proving, including setup, at roughly 55–103 ms median across
its twelve programs. Source inspection shows a 20-bit interaction grind in
`deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig`
and a second PCS/FRI grind in `Engine.prove`. These are inside the opaque
`native_prove_including_setup_ns` interval. The other measured S31 package
steps are approximately 2–3 ms in total. The earlier direct-gate stage
study separately measured a median 84.49 ms in native PoW against 1.86 ms
native non-PoW over 36 trials, but is a different proof profile.

The [diagnostic script](diagnose.py) holds two frozen ReleaseFast package
binaries, their source, assignment `00`, public ABI v2 statement, and proof
settings fixed. It interleaves worker counts across four rounds, verifies
each proof with the corresponding independent native verifier, and requires
identical proof bytes for every worker count. It checks binary SHA-256 against
the frozen build record. It writes outputs outside the frozen measurement
worktree. The two proof SHA-256 values also equal the frozen transfer corpus's
first proof for the respective sources. The raw [32 trial records](results/worker-sweep-20261011.json)
and [two changed-claim smoke records](results/claim-mutation-smoke-20261011.json)
are retained; full generated proofs are discarded after acceptance. The
smoke run changed one ABI-valid public result and the native verifier
rejected it for both shapes. The host reported 18 logical CPUs and the
default grinder chooses that count when `STWO_ZIG_POW_WORKERS` is unset.

| Source | 1 worker | 4 workers | 8 workers | 16 workers |
| --- | ---: | ---: | ---: | ---: |
| Control, 2 calls | 1346.69 ms | 349.19 ms | 186.46 ms | 101.58 ms |
| Control, 6 calls | 342.57 ms | 90.95 ms | 50.73 ms | 29.58 ms |

These are medians of four fixed-statement trials of the **whole native prove
interval**, not PoW-only measurements. The same binaries and same claims
produce the same proof sizes and hashes at every worker count (85,145 bytes
for 2 calls; 146,182 bytes for 6 calls). The 18-worker smoke runs measured
116.78 and 31.25 ms, one sample each. Neither that difference nor these
small fixed-statement samples supports a speedup claim over the default.

## Fresh-statement paired diagnostic

[`fresh_assignments.py`](fresh_assignments.py) runs a second, more useful
worker comparison against the *same frozen binaries* over 30 distinct
assignments for each of the 2-call and 6-call control programs. The runner
checks the prospective protocol SHA-256 and its freeze record, source and
assignment hashes, and both binary hashes before launching native work. It
rotates worker order across statements, repeats each statement twice, checks
every emitted proof with the source-embedded native verifier, and requires
proof bytes to remain identical across all worker counts and repetitions for
that statement. An ABI-valid changed result is rejected by the verifier for
each program. All 480 proofs were accepted; there were 30 distinct proof
hashes per program and both changed claims failed with
`InvalidMixedInteractionNonce`. The full [trial records](results/fresh-statements-20261011.json)
retain timing, proof-byte, binary, source, protocol and script hashes.

| Source | 16 workers | 18 workers | 24 workers | 32 workers |
| --- | ---: | ---: | ---: | ---: |
| Control, 2 calls | 68.97 ms | 72.94 ms | 71.83 ms | 69.00 ms |
| Control, 6 calls | 107.01 ms | 106.98 ms | 105.93 ms | 105.03 ms |

Each entry is the median of **30 per-statement medians**, each of which
contains two process runs. In the paired per-statement analysis, relative to
18 workers, the median timing ratios for 16/24/32 workers were
0.963/0.972/0.957 for 2 calls and 0.969/0.992/0.960 for 6 calls. The
ratios do not establish an overall winner: differences are small relative
to run-to-run and statement-dependent variation. Native proving spans
roughly 6–380 ms in these records. This is one host and two source shapes.
The timed interval includes native setup and both PoW stages, so it does not
measure either grinder separately. It is a diagnostic, not a trained or
validated whole-prover predictor; the earlier transfer corpus remains
**unscored** because its exact frozen training-model bytes were lost.

Run the saved study with the frozen package root (a fresh `--out` directory is
required):

```sh
python3 src/frontends/s31/benchmarks/pow_workers/fresh_assignments.py \
  --package-root /path/to/zig-out/s31-mixed-stage-transfer-v1-20261011 \
  --shapes control_n2 control_n6 --workers 16 18 24 32 \
  --assignments 30 --rounds 2 --out /path/to/new/output-directory
python3 -m unittest discover -s src/frontends/s31/benchmarks/pow_workers -p 'test_*.py'
```

The next measurement step is separate, non-transcript timers around the
20-bit interaction grind and PCS/FRI grind in an isolated engine branch. If
a host-local worker policy is changed later, it may alter only the search
schedule:
the canonical smallest-valid lattice nonce, PoW difficulty, verifier,
Fiat–Shamir transcript and proof bytes must remain unchanged. If device
offload wins after startup cost, its result must be checked by the native
channel and tested against the same canonical nonce. Neither route requires
relaxing the proof system's security parameters.

Example with a separately built frozen transfer package root:

```sh
python3 src/frontends/s31/benchmarks/pow_workers/diagnose.py \
  --package-root /path/to/zig-out/s31-mixed-stage-transfer-v1-20261011 \
  --shapes control_n2 control_n6 --workers 1 4 8 16 --rounds 4 \
  --out /path/to/new/output-directory
```
