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

python3 -B -m unittest scripts.tests.test_pcs_fri_merkle_byte_preimage
zig test -O ReleaseSafe -j2 --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_merkle_byte_preimage_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
