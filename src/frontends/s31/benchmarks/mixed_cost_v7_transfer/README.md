# Fresh 80-claim transfer after the unscored v6 integrity failure

The [v6 run](../../../../../design/s31/measurements/MIXED_COST_V6_TRANSFER_INVALIDATED.md)
was invalidated before scoring when the compiler fingerprint changed during
timing. This v7 cohort uses **entirely new source and claim identities**,
checks disjointness from v4, v5 and v6, and retains the unchanged v4 model.
It uses the same four explicit gates as the preregistered v6 protocol. It is
not a re-score or selected rerun of v6.

`affine_seed_n1` scales and offsets a public four-word input before one
16-round chip call, then offsets and adds the input. `switchback_n8`
alternates add and scale feeders across eight 16-round calls, with an offset
after every third call. Both produce eight public proof words through the
versioned record ABI. Their exact compiled source JSON bytes are committed
beside the protocol before the first native package build.

From the repository root, in order:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/protocol.py freeze
# Commit the protocol, source JSON, and every v7 script before Zig.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/protocol.py check
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/study.py run \
  --out zig-out/s31-mixed-cost-v7-transfer
python3 -B src/frontends/s31/benchmarks/mixed_cost_v7_transfer/audit.py \
  --out zig-out/s31-mixed-cost-v7-transfer --native --write
```

Claim 0 is run twice for descriptive first-post-build and same-claim-repeat
observations; claims 1–80 are scored. All 164 honest proofs must verify, and
every ABI-valid changed public result must be rejected at the interaction
nonce. The runner retains raw proofs, binaries and stderr locally, and writes
a compact result only if both source packages complete and the final pinned
stack still equals the committed protocol. The auditor checks artifact hashes
and replays every proof and mutation without measuring timing.

Each source must meet warm-wall median relative error ≤30%, predicted 90%
wall interval coverage ≥80%, proof-size median relative error ≤10%, and
predicted 90% proof interval coverage ≥80%. Cold/startup and build walls are
descriptive only. These are one-host, one-stack transfer checks of the
call-count-only cost model; they do not compare against Cairo or establish
general statistical coverage.
