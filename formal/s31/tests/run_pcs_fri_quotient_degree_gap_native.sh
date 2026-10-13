#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 native quotient degree' \
  --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_quotient_degree_gap_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
