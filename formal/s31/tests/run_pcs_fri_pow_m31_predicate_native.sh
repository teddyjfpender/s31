#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_pow_m31_predicate_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
