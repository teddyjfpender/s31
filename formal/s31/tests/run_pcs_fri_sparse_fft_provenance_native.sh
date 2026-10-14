#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 sparse source FFT provenance differential' \
  --dep stwo_core --dep stwo_prover_engine \
  -Mroot=formal/s31/tests/pcs_fri_sparse_fft_provenance_native.zig \
  --dep stwo_core --dep stwo_prover_api --dep stwo_backend_contracts \
  -Mstwo_prover_engine=deps/stwo-zig/src/prover/mod.zig \
  --dep stwo_core \
  -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig \
  --dep stwo_core \
  -Mstwo_backend_contracts=deps/stwo-zig/src/backend/mod.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
