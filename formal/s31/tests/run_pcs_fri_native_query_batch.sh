#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_native_query_batch.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
