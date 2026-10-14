#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j4 \
  --test-filter 'Gate log-4 four-slot native FFT' \
  --dep stwo_core --dep stwo_prover_engine \
  -Mroot=formal/s31/tests/pcs_fri_gate16_four_slot_fft_native.zig \
  --dep stwo_core --dep stwo_prover_api --dep stwo_backend_contracts \
  -Mstwo_prover_engine=deps/stwo-zig/src/prover/mod.zig \
  --dep stwo_core \
  -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig \
  --dep stwo_core \
  -Mstwo_backend_contracts=deps/stwo-zig/src/backend/mod.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
