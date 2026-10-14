#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 projected OOD guard' \
  --dep stwo_core \
  -Mroot=formal/s31/tests/pcs_fri_projected_ood_guard_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig
