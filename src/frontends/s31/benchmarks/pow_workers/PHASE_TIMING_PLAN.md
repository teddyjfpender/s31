# Mixed prover phase timing: exact next seam

## What the current binary reports

The source-pinned mixed package reports profile rebuild, semantic evaluation,
topology compilation, witness compilation, **one opaque native prove including
setup**, and envelope serialization. The native interval starts immediately
before `engine.proveSourceBound` and ends immediately after it returns in
[`general_package.zig`](../../runtime/mixed_boundary/general_package.zig).
The production binary has no runtime flag for either native PoW timer.

The pinned engine's
[`proveSourceBound`](../../../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig)
calls `channel.grind(INTERACTION_POW_BITS)` directly, then calls
`Engine.prove` without a stage recorder. There is therefore no sound way to
split the two grinders from the existing `S31_MIXED_STAGE_V1` output or from
the serialized proof. Estimating them by subtracting different worker-count
runs would mix PoW, setup, scheduler overhead and host contention.

The engine already has the needed low-level instrumentation for **FRI PoW**:
`Engine.ProveOptions.recorder` accepts a `stage_profile.Recorder`, and
`prover/pcs/scheme.zig` wraps the PCS nonce search in the stage ID
`proof_of_work`. The sibling `direct_arithmetic.zig` and
`sparse_arithmetic.zig` integrations demonstrate a stage-only recorder
(`capture_tasks = false`) and extract that stage after `Engine.prove`.
The **interaction PoW** still needs a timer around the direct `channel.grind`.

## Minimal implementation, when the pinned engine can change

1. Add an optional diagnostic output to the mixed engine without changing
   its proof format or verifier API. Preserve `proveSourceBound` as the
   existing uninstrumented entrypoint; a second function or optional request
   can return a `Timing` value with monotonic integer nanoseconds. At entry,
   time these sequential, nonoverlapping regions:

   - plan/preprocessed/AIR admission and binding;
   - PCS setup plus preprocessed commitment;
   - circuit/chip/bridge base traces and main commitment;
   - the interaction `channel.grind` call alone;
   - interaction traces, lookup closure and interaction commitment;
   - `Engine.prove` as a whole, including composition/FRI/PCS work;
   - returned proof-object assembly.

2. Only on the diagnostic path, pass a stage-only recorder to `Engine.prove`,
   then require **exactly one** `proof_of_work` node in its snapshot. Convert
   its seconds to nanoseconds and retain the whole `Engine.prove` duration as
   a separate field. Report `pcs_without_reported_fri_pow_ns` as an accounting
   subtraction, not a separately executed stage. Likewise report
   `native_without_reported_pow_ns = native_total - interaction_pow -
   fri_pow` only when both PoW timers exist and their sum fits inside the
   measured native interval.

3. Keep the telemetry out of channel mixing, proof bytes, AIR, manifest,
   public statement and verifier. Make the S31 wrapper emit a new diagnostic
   schema such as `S31_MIXED_NATIVE_PHASE_V1`; do not silently add fields to
   the old frozen `S31_MIXED_STAGE_V1` record. Every native proof still goes
   through the unchanged source-embedded verifier.

4. Compare diagnostic and ordinary proving from the **same built commit**
   using the 30 frozen statements per source. For each statement require
   identical canonical proof SHA-256 and proof bytes with timing on/off,
   verifier acceptance, and proof-level rejection of an ABI-valid changed
   result. Check that the phase intervals are nonnegative, nonoverlapping,
   within the native total and have a bounded accounting residual. An
   instrumented binary has a new engine/compiler fingerprint; never attach
   its timings to the previous prospective transfer run.

5. Only after the new code and source/engine hashes are frozen, predeclare
   train/held-out cohorts and seal the **exact** model bytes with
   [`model_artifact_retention_v1/retain.py`](../model_artifact_retention_v1/retain.py).
   Commit the artifact and manifest in an anchor commit, then run `check`
   with the externally recorded model SHA-256, protocol SHA-256 and anchor
   commit **before** the first held-out native build. Keep model fitting,
   threshold selection and the held-out phase separate. The earlier mixed
   transfer corpus stays unscored because the exact old model bytes were
   lost.

## First runnable data and its limit

The existing [fresh-statement probe](fresh_assignments.py) needs no engine
change. Its retained [480 native-verified trials](results/fresh-statements-20261011.json)
use 60 distinct public statements, two source shapes, two repetitions and
16/18/24/32 PoW workers. Both changed public claims reached proof-level
`InvalidMixedInteractionNonce`. Proof bytes were identical across settings
for each statement. The median of per-statement native prove times was
68.97/72.94/71.83/69.00 ms for the 2-call shape and
107.01/106.98/105.93/105.03 ms for the 6-call shape. Individual native
intervals ranged from 5.99 to 371.89 ms. This is **whole native prove
including setup and both PoW stages**; it is not a measurement of either
grinder, a validated cost predictor, or evidence to change the default
worker policy.
