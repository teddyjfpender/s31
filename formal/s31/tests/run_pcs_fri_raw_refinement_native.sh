#!/usr/bin/env bash
set -euo pipefail

zig test -O ReleaseSafe -j2 \
  --test-filter 'FRI raw-slot refinement' \
  --dep stwo_core --dep stwo_prover_engine --dep stwo_cpu_backend \
  -Mroot=formal/s31/tests/pcs_fri_raw_refinement_native.zig \
  --dep stwo_core --dep stwo_backend_contracts --dep stwo_prover_api \
  -Mstwo_prover_engine=deps/stwo-zig/src/prover/mod.zig \
  --dep stwo_core --dep stwo_backend_contracts --dep stwo_prover_api --dep stwo_prover_engine \
  -Mstwo_cpu_backend=deps/stwo-zig/src/backends/cpu_scalar/mod.zig \
  --dep stwo_core -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig \
  --dep stwo_core -Mstwo_backend_contracts=deps/stwo-zig/src/backend/mod.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
