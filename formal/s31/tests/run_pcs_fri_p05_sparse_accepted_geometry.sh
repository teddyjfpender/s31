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
python3 - "$temp_dir/geometry.json" <<'PY'
import json
import sys

result = json.load(open(sys.argv[1], encoding="utf-8"))
shape = result["accepted_capture"]
assert shape["root_columns"] == [12, 17, 24, 8]
assert shape["root_ood_claims"] == [12, 17, 36, 8]
assert [(h["extended_log_size"], h["source_columns"], h["ood_claims"])
        for h in shape["heights"]] == [(17, 14, 18), (11, 28, 32), (5, 19, 23)]
assert result["candidate_paper_parameters"]["largest_integer_M_passing_isolated_batch_factor"] == 1024
assert result["native_to_paper_batch_width_M"] is None
assert result["native_proven_security_bits"] is None
assert result["proven_release_admissible"] is False
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
