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

The immediate performance work is to add separate, non-transcript timers
around the 20-bit interaction grind and PCS/FRI grind in an isolated engine
branch, then run an interleaved same-binary 16/18/24/32-worker comparison
over multiple sources and fresh assignments. If the default worker count is
suboptimal, a host-local worker policy can change only the search schedule:
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
