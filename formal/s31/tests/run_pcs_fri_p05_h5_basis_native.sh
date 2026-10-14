#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 h5' \
  --dep stwo_core --dep point_eval \
  -Mroot=formal/s31/tests/pcs_fri_p05_h5_basis_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core -Mpoint_eval=deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 h5 five-column' \
  --dep stwo_core --dep stwo_prover \
  -Mroot=formal/s31/tests/pcs_fri_p05_h5_plan_tail_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core --dep stwo_prover_api -Mstwo_prover=deps/stwo-zig/src/prover/mod.zig \
  -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig
