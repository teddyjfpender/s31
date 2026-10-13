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

python3 -B -m unittest scripts.tests.test_pcs_fri_lifted_capture
zig test -O ReleaseSafe -j2 \
  --dep stwo_core --dep pcs_merkle_collision_reduction \
  -Mroot=formal/s31/tests/pcs_fri_native_collision_reduction.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core \
  -Mpcs_merkle_collision_reduction=formal/s31/tests/lib/pcs_merkle_collision_reduction.zig
formal/s31/tests/run_pcs_fri_lifted_capture_native.sh
