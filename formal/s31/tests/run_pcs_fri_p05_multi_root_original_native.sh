#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 original batch reconstructs' \
  --dep stwo_core \
  --dep s31_adapter \
  -Mroot=formal/s31/tests/pcs_fri_p05_multi_root_original_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core \
  --dep s31_lifted_capture \
  -Ms31_adapter=formal/s31/tests/lib/p05_multi_root_original_batch.zig \
  --dep stwo_core \
  -Ms31_lifted_capture=src/frontends/s31/runtime/pcs_lifted_capture_admission.zig
