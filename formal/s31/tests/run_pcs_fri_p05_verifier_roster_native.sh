#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 verifier-owned AIR and proof roster' \
  --dep stwo_core \
  --dep s31_p05_roster \
  --dep s31_pair_fold \
  --dep s31_gate_plan \
  -Mroot=formal/s31/tests/pcs_fri_p05_verifier_roster_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core \
  -Ms31_p05_roster=formal/s31/tests/lib/p05_claim_roster.zig \
  --dep stwo_core \
  --dep s31_p05_roster \
  -Ms31_gate_plan=formal/s31/tests/lib/p05_gate_multi_epoch_plan.zig \
  --dep stwo_core \
  --dep s31_own_adapter \
  --dep s31_p05_roster \
  -Ms31_pair_fold=formal/s31/tests/lib/p05_native_height_pair_fold.zig \
  --dep stwo_core \
  --dep s31_lifted_capture \
  --dep s31_p05_roster \
  -Ms31_own_adapter=formal/s31/tests/lib/p05_own_quotient_rows.zig \
  --dep stwo_core \
  -Ms31_lifted_capture=src/frontends/s31/runtime/pcs_lifted_capture_admission.zig
