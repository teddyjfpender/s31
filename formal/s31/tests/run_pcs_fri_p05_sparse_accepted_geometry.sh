#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
temp_dir="$(mktemp -d "${TMPDIR:-/tmp}/s31-p05-sparse-accepted.XXXXXX")"
trap 'rm -rf "$temp_dir"' EXIT

source_path=src/frontends/s31/examples/arithmetic/arith4.s31.json
assignment_path=src/frontends/s31/examples/arithmetic/arith4.valid.json
statement_path=src/frontends/s31/examples/arithmetic/arith4.statement.json
package="$temp_dir/package"
proof="$temp_dir/proof.bin"
verifier="$package/bin/s31-arith4-native-verifier"

python3 src/frontends/s31/python/s31.py build "$source_path" --lowering sparse-gate --out "$package"
"$package/bin/s31-arith4-prover" prove "$assignment_path" "$proof"
"$verifier" "$proof" "$statement_path" "$package/verification-key.json"
python3 -B scripts/release/pcs_fri_sparse_p05_accepted_geometry.py \
    "$package" "$proof" "$statement_path" > "$temp_dir/geometry.json"
python3 - "$temp_dir/geometry.json" \
    design/s31/security/evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json <<'PY'
import json
import sys

live, pinned = (json.load(open(path, encoding="utf-8")) for path in sys.argv[1:])
# Compiler output artifacts are checked against each *local* manifest by the
# reporter, but a fresh build directory changes its manifest file digest.
# Compare every accepted proof/claim/query/source field exactly.
for report in (live, pinned):
    manifest_sha = report["package_checks"].pop("manifest_sha256")
    assert isinstance(manifest_sha, str) and len(manifest_sha) == 64
assert live == pinned, "accepted sparse proof, claim, or row evidence changed"
PY
python3 -B scripts/release/pcs_fri_sparse_p05_h3_roster.py \
    --evidence "$temp_dir/geometry.json" --check
python3 - "$temp_dir/geometry.json" <<'PY'
import json
import sys
from copy import deepcopy
from scripts.release.pcs_fri_sparse_p05_accepted_geometry import ordered_claim_slices

result = json.load(open(sys.argv[1], encoding="utf-8"))
shape = result["accepted_capture"]
assert shape["root_columns"] == [12, 17, 24, 8]
assert shape["root_ood_claims"] == [12, 17, 36, 8]
assert [(h["extended_log_size"], h["source_columns"], h["ood_claims"])
        for h in shape["heights"]] == [(17, 14, 18), (11, 28, 32), (5, 19, 23)]
assert len(shape["claims"]) == 73
assert len(result["accepted_ood_claim_map_sha256"]) == 64
base = (tuple(shape["oods_point_x_limbs"]), tuple(shape["oods_point_y_limbs"]))
shifted = set()
for height, base_count in [(17, 14), (11, 28), (5, 19)]:
    points = [(tuple(c["point_x_limbs"]), tuple(c["point_y_limbs"]))
              for c in shape["claims"] if c["extended_log_size"] == height]
    assert points.count(base) == base_count
    assert len(set(points)) == 2
    shifted.update(set(points) - {base})
assert len(shifted) == 1
assert result["candidate_paper_parameters"]["largest_integer_M_passing_isolated_batch_factor"] == 1024
assert result["candidate_paper_parameters"]["certified_batch_grinding_credit"] == 0
assert result["native_to_paper_batch_width_M"] is None
assert result["native_proven_security_bits"] is None
assert result["proven_release_admissible"] is False
assert len(list(ordered_claim_slices(shape))) == len(shape["columns"])
for field, value, column_index in [
    ("first_claim_index", -1, 0),
    ("first_claim_index", 0, 1),
    ("first_claim_index", True, 0),
    ("ood_claims", -1, 0),
]:
    malformed = deepcopy(shape)
    malformed["columns"][column_index][field] = value
    try:
        list(ordered_claim_slices(malformed))
    except ValueError:
        pass
    else:
        raise AssertionError(f"accepted malformed claim slice: {field}={value}")
malformed = deepcopy(shape)
malformed["claims"].append(malformed["claims"][-1])
try:
    list(ordered_claim_slices(malformed))
except ValueError:
    pass
else:
    raise AssertionError("accepted an unowned trailing claim")
PY

# A wrong key must fail before any geometry JSON is emitted. This control
# needs no modified proof or adversarial acceptance fixture.
if "$verifier" inspect-p05 "$proof" "$statement_path" /dev/null > "$temp_dir/rejected.out" 2>&1; then
    echo "inspect-p05 unexpectedly accepted a wrong key" >&2
    exit 1
fi
if grep -q 's31-sparse-p05-accepted-capture-shape-v1' "$temp_dir/rejected.out"; then
    echo "inspect-p05 emitted geometry for a rejected key" >&2
    exit 1
fi
echo "P05 sparse accepted geometry and wrong-key control passed"
