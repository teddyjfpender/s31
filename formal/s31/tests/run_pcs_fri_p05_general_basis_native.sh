#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"

python3 -B - <<'PY'
import json
from pathlib import Path
path = Path('design/s31/security/evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json')
report = json.loads(path.read_text())
if report.get('schema') != 's31-p05-sparse-gate-accepted-geometry-v1':
    raise SystemExit('unexpected accepted sparse geometry schema')
if report.get('status') != 'accepted_native_proof_experimental_geometry_only':
    raise SystemExit('accepted sparse proof status changed')
heights = report['accepted_capture']['heights']
actual = [(x['committed_input_log_size'], x['extended_log_size'], x['source_columns']) for x in heights]
if actual != [(16, 17, 14), (10, 11, 28), (4, 5, 19)]:
    raise SystemExit(f'accepted sparse source roster changed: {actual}')
if report.get('native_to_paper_batch_width_M') is not None or report.get('native_proven_security_bits') is not None or report.get('proven_release_admissible') is not False:
    raise SystemExit('candidate geometry unexpectedly claims security or release')
print('accepted sparse h11/h17 coefficient logs pinned: 10/16')
PY

zig test -O ReleaseSafe -j2 \
  --test-filter 'P05 general' \
  --dep stwo_core --dep point_eval \
  -Mroot=formal/s31/tests/pcs_fri_p05_general_basis_native.zig \
  -Mstwo_core=deps/stwo-zig/src/core/mod.zig \
  --dep stwo_core -Mpoint_eval=deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig
