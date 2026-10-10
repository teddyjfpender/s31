# Whole-prover cost model V5: prospective RSS interval study

**Status: static protocol and tooling only. No V5 package or native proof has
been built or timed.** The [V4 audit](language/whole-prover-cost-v4-audit.json)
is immutable and failed its predeclared local gate: hash prover-RSS trial
interval coverage was 72% against an 80% threshold. V5 is a new prospective
study. V4 held-out values motivated the interval design but cannot enter V5
fitting, calibration, or gate changes.

The machine-readable [V5 protocol](whole-prover-cost-v5.json) currently has
null source, engine, compiler, and measurement-tool pins. The runner refuses
all native phases until the integrated source revision is stable and those
four pins plus an explicit sorted Python tool-path inventory are filled.
Before the first V5 native build, commit the protocol freeze JSON described
below and record its commit SHA plus the full protocol SHA in a timestamped
external message. The CLI requires both, checks the committed anchor bytes,
and checks exact protocol bytes. Before prove, it also checks the saved
build-inventory protocol SHA. A local draft record or CLI argument alone
cannot establish when the hash was first recorded. The protocol requires at
least 8 GiB of free artifact space; raw V4 and V5 evidence is retained.

## Split and controls

V5 has **23 training programs**: six direct-gate arithmetic, six generated
direct-chip, six Blake hash, and five signed fixed-width division programs.
It has **20 held-out programs**, five per family. Each program uses 100
distinct fresh assignments, giving 2,300 training and 2,000 held-out native
proof trials if the study runs. Generated source bytes and assignment values
are disjoint within V5 and from V4; the unit test checks this before any
native observation. Training and held-out cases use different recurrence
constants, assignment ranges, hash depths, chip rounds, and signed public
outputs. Each trial must pass native verification, independent output-oracle
evaluation, and a rejected changed-public-claim control. Each direct-chip
package must seal its one-call component manifest into the native key.

Static elaboration caught a public ABI limit before measurement: publishing
both i128 quotient and remainder needs 16 `u16` words, but the current ABI
allows eight. The training i128 case publishes quotient only, and the
held-out i128 case publishes remainder only. Both expose eight words. This
change is recorded in the protocol before any V5 native build or trial.

The target remains the arithmetic mean of 100 fresh prover-process wall
times plus their native verifier-process wall times. Native setup runs inside
each fresh prover process. Package-build wall and memory are recorded
separately; package construction is excluded from this prediction. The
fixed 26-bit PoW policy remains stochastic: exposed interaction and FRI PoW
stages use pooled constant expected values, while generic hash proving has
opaque PoW inside its prove stage. V4 stage formulas for expected wall and
proof bytes stay unchanged, including its pooled training-only whole-wall
leave-one-program-out trial interval.

## RSS interval specified before data

The RSS point fit uses the V4 formula: a positive affine fit in padded rows
for arithmetic, a positive affine fit in authenticated chip trace cells for
direct chip, and a log-linear fit for hash and fixed-width families. All
points are training-program trial medians.

For each training program `j`, fit that family model on **all other V5
training programs** and predict its RSS center `p_j`. For each trial `i`,
compute the signed residual in bytes `r_ij = observed_RSS_ij - p_j`. Define
`radius_j = max(|q05(r_ij)|, |q95(r_ij)|)` and
`R = max_j(radius_j)`. The full-training fit gives a future center `p`; its
trial interval is `[max(0, p - R), p + R]`. Keeping the largest program's
absolute-byte residual envelope prevents a systematic program miss from
being diluted by pooling all training trials. It does not guarantee tail
coverage on a new source, host, or compiler revision.

The predeclared local gate retains V4's per-family wall program-mean p90
relative error ≤25%, whole-wall trial interval coverage ≥80%, and median
upper-to-measured-mean ratio ≤8×. Proof bytes and prover RSS each require
per-family program-median p90 error ≤10% and trial interval coverage ≥80%.
V5 additionally requires **each** held-out program's RSS trial coverage
≥70% and interval upper bound / measured RSS median ≤1.5×. Every family
needs at least five training and five held-out programs and each held-out
program needs 100 trials. Failure of any condition fails the local gate.
Automatic lowering selection remains disabled even if the local gate passes.

## Freeze and publication procedure

After integration tests complete, pin the exact S31 source commit, stwo-zig
gitlink, `s31.compiler_fingerprint()` digest, sorted list of every S31
benchmark/frontend Python path, and aggregate tool-source SHA in the
protocol; set `status` exactly to `frozen-before-any-v5-native-observation`.
Write `design/s31/measurements/language/whole-prover-cost-v5-protocol-freeze.json`
with schema `s31-whole-prover-v5-protocol-freeze`, aware UTC
`recorded_at_utc`, full `protocol_sha256`, and the four pinned
`source_base_commit`, `engine_gitlink_commit`, `compiler_sha256`, and
`measurement_tool_sha256` values. Commit that file **before the first native
build**. Record the full anchor commit SHA, protocol SHA, and host pseudonym
in a timestamped external message. Pass the same
`--protocol-anchor-commit` and `--expected-protocol-sha256` to both training
phases and both held-out phases. The runner checks that the anchor bytes
exist at an ancestor commit and match the current file. Only `--phase build`
and `--phase prove` are accepted. Before prove,
the runner checks the build inventory's protocol SHA, compiler/tool SHA,
program set, and fresh-build status. For every program it also matches
source SHA and package-build timing against the package-build record,
rehashes the generated source, and checks the chip manifest binding.
Changing only a gate, assignment range, build timing, or source after build
therefore fails before any native proof process.

Build and prove all 23 training packages, then fit the model. Write
`design/s31/measurements/language/whole-prover-cost-v5-model-freeze.json`
with schema `s31-whole-prover-v5-model-freeze`, aware UTC
`recorded_at_utc`, full `protocol_sha256`, `frozen_model_sha256`, and
`training_corpus_sha256`. Commit it **before any held-out package build**
and externally record its full commit SHA and model SHA. Its commit must
descend from the protocol-anchor commit. Pass `--model-anchor-commit` and
`--expected-model-sha256` to both held-out phases. The held-out build
inventory records both anchor commits and the model SHA, and
the proof phase rejects a mismatch. Build and prove the 20 new held-out
packages without changing source, tools, protocol, or model. Evaluate once
against the frozen gate and publish both passes and failures with
`publish_whole_prover_cost_v5.py --expected-protocol-sha256 ...
--protocol-anchor-commit ... --expected-model-sha256 ...
--model-anchor-commit ...`. The publisher replays both committed anchors and external hashes,
the two build inventories, model fitting, evaluation, and saved artifact
bindings, including exact build-inventory-to-final-corpus cost measurements.
It does not rerun native proofs or oracles. Do not adjust the
radius or gate after held-out observations.

**Replay requires the exact pinned checkout.** V4's publisher cannot replay
from a later checkout after new benchmark Python files change its dynamic
tool digest; its V4 audit remains valid under its original frozen snapshot.
V5 records an explicit path inventory to make such changes visible and
diagnosable, and rejects any added or removed path during native work or
publication. Merely hashing an old allowlist while loading Python from a
newer checkout could miss code introduced through imports, so this inventory
does not authorize replay on an arbitrary newer tree. Use an isolated
worktree at the pinned commit and engine gitlink to reproduce the audit.

This one-host check, even if successful, will not measure cached setup,
predict compile-to-proof latency, establish cross-host transfer, or license
automatic lowering. Those require separate prospective studies.
