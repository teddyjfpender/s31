#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'Gate log-4 native canonical rows' \
  --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_gate16_fourier_rows_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
