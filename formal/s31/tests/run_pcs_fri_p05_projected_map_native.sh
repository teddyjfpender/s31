#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 accepted sparse OOD points refine native mask and prover projections' \
  --dep stwo_core --dep stwo_cairo --dep stwo_point_eval \
  -Mroot=formal/s31/tests/pcs_fri_p05_projected_map_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core -Mstwo_cairo=deps/stwo-zig/src/frontends/cairo/mod.zig \
  --dep stwo_core -Mstwo_point_eval=deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig
