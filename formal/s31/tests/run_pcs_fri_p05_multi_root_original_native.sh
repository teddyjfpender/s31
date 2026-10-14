#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 paired native first fold reconstructs' \
  --dep stwo_core \
  --dep s31_adapter \
  --dep s31_own_adapter \
  --dep s31_pair_fold \
  -Mroot=formal/s31/tests/pcs_fri_p05_multi_root_original_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core \
  --dep s31_lifted_capture \
  -Ms31_adapter=formal/s31/tests/lib/p05_multi_root_original_batch.zig \
  --dep stwo_core \
  --dep s31_lifted_capture \
  --dep s31_p05_roster \
  -Ms31_own_adapter=formal/s31/tests/lib/p05_own_quotient_rows.zig \
  --dep stwo_core \
  --dep s31_own_adapter \
  --dep s31_p05_roster \
  -Ms31_pair_fold=formal/s31/tests/lib/p05_native_height_pair_fold.zig \
  --dep stwo_core \
  -Ms31_p05_roster=formal/s31/tests/lib/p05_claim_roster.zig \
  --dep stwo_core \
  -Ms31_lifted_capture=src/frontends/s31/runtime/pcs_lifted_capture_admission.zig
