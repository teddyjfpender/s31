#!/usr/bin/env bash
set -euo pipefail

# Run from the S31 repository root. Keep this audit test outside src/: package
# compiler fingerprints must not change when a proof test is added.
zig test -O ReleaseSafe -j2 \
  --test-filter 'native Gate finalizer matches independent' \
  --dep stwo_core --dep stwo_circuit_frontend \
  -Mroot=formal/s31/tests/native_gate_finalizer_refinement.zig \
  --dep stwo_core --dep stwo_prover_engine \
  -Mstwo_circuit_frontend=deps/stwo-zig/src/frontends/circuit/mod.zig \
  --dep stwo_core --dep stwo_backend_contracts --dep stwo_prover_api \
  -Mstwo_prover_engine=deps/stwo-zig/src/prover/mod.zig \
  --dep stwo_core -Mstwo_backend_contracts=deps/stwo-zig/src/backend/mod.zig \
  --dep stwo_core -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
