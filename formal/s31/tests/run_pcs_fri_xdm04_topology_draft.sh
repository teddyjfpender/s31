#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../../.." && pwd)"
engine_repo="${1:?pass a stwo-zig checkout at the reviewed CAS05 draft commit}"
expected="234ac67b2819e6b102e8d43da93a38a4a902075e"
actual="$(git -C "$engine_repo" rev-parse HEAD)"
if [[ "$actual" != "$expected" ]]; then
  echo "XDM04 draft checkout differs from reviewed CAS05 commit" >&2
  exit 1
fi

cd "$repo_root"
zig test -O ReleaseSafe -j2 \
  --dep stwo_core --dep stwo_prover_engine \
  -Mroot=formal/s31/tests/pcs_fri_xdm04_topology_draft.zig \
  --dep stwo_core --dep stwo_backend_contracts --dep stwo_prover_api \
  -Mstwo_prover_engine="$engine_repo/src/prover/mod.zig" \
  --dep stwo_core -Mstwo_prover_api="$engine_repo/src/prover_api/mod.zig" \
  --dep stwo_core -Mstwo_backend_contracts="$engine_repo/src/backend/mod.zig" \
  -Mstwo_core="$engine_repo/src/core/mod.zig"
