#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'FRI raw DEEP custody' \
  --dep stwo_core --dep deep_capture_admission \
  -Mroot=formal/s31/tests/pcs_fri_deep_custody_native.zig \
  --dep stwo_core -Mdeep_capture_admission=src/frontends/s31/runtime/deep_capture_admission.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
