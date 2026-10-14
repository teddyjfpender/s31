#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 accepted sparse H3 two-point own quotient rows' \
  --dep stwo_core --dep s31_own_adapter \
  -Mroot=formal/s31/tests/pcs_fri_p05_sparse_h3_accepted_rows_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core --dep s31_lifted_capture --dep s31_p05_roster \
  -Ms31_own_adapter=formal/s31/tests/lib/p05_own_quotient_rows.zig \
  --dep stwo_core -Ms31_p05_roster=formal/s31/tests/lib/p05_claim_roster.zig \
  --dep stwo_core -Ms31_lifted_capture=src/frontends/s31/runtime/pcs_lifted_capture_admission.zig
