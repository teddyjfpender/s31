#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo_root"
expected_engine="$(git rev-parse HEAD:deps/stwo-zig)"
actual_engine="$(git -C deps/stwo-zig rev-parse HEAD)"
if [[ "$actual_engine" != "$expected_engine" ]]; then
  echo "pinned stwo-zig checkout differs from S31 gitlink" >&2
  exit 1
fi
if [[ -n "$(git -C deps/stwo-zig status --porcelain --untracked-files=no)" ]]; then
  echo "pinned stwo-zig checkout has tracked modifications" >&2
  exit 1
fi

zig test -O ReleaseSafe -j2 \
  --test-filter 'Gate quotient-only x-square source' \
  --dep stwo_core --dep stwo_prover_engine \
  -Mroot=formal/s31/tests/pcs_fri_gate_quotient_only_gap_native.zig \
  --dep stwo_core --dep stwo_backend_contracts --dep stwo_prover_api \
  -Mstwo_prover_engine=deps/stwo-zig/src/prover/mod.zig \
  --dep stwo_core -Mstwo_prover_api=deps/stwo-zig/src/prover_api/mod.zig \
  --dep stwo_core -Mstwo_backend_contracts=deps/stwo-zig/src/backend/mod.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
