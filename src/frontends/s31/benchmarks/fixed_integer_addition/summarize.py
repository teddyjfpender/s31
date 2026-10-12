#!/usr/bin/env python3
"""Validate and compare the two native checked-addition acceptance matrices."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

KINDS = tuple(f"{sign}{width}" for sign in ("u", "i")
              for width in (8, 16, 32, 64, 128))
CONTROLS = ("native_verifier_accepted", "changed_public_statement_rejected",
            "native_overflow_rejected")


def indexed(path: Path, lowering: str) -> tuple[dict[str, dict], str]:
    report = json.loads(path.read_text())
    if report.get("schema") != "s31-int-addition-native-v1" or report.get("lowering") != lowering:
        raise ValueError(f"{path}: wrong native report schema or lowering")
    cases = report.get("cases")
    if not isinstance(cases, list) or len(cases) != len(KINDS):
        raise ValueError(f"{path}: expected all ten integer kinds")
    by_kind = {case["kind"]: case for case in cases}
    if set(by_kind) != set(KINDS) or len(by_kind) != len(cases):
        raise ValueError(f"{path}: missing or duplicate integer kind")
    for kind, case in by_kind.items():
        if case["lowering"] != lowering or not all(case.get(key) is True for key in CONTROLS):
            raise ValueError(f"{path}: {kind} native control failed")
    fingerprint = report.get("compiler_sha256")
    if not isinstance(fingerprint, str) or len(fingerprint) != 64:
        raise ValueError(f"{path}: compiler fingerprint is missing")
    return by_kind, fingerprint


def summarize(sparse_path: Path, direct_path: Path) -> dict:
    sparse, sparse_compiler = indexed(sparse_path, "sparse-wide-gate")
    direct, direct_compiler = indexed(direct_path, "direct-gate")
    if sparse_compiler != direct_compiler:
        raise ValueError("the two native matrices used different compiler fingerprints")
    rows = []
    for kind in KINDS:
        old, new = sparse[kind], direct[kind]
        if old["canonical_ir_sha256"] != new["canonical_ir_sha256"] or old["spec"] != new["spec"]:
            raise ValueError(f"{kind}: profiles compiled different relations")
        if (new["raw"]["eq"] != 0 or new["raw"]["m31_to_u32"] != 0 or
                new["raw"]["blake_g"] != 0 or new["raw"]["triple_xor"] != 0):
            raise ValueError(f"{kind}: direct profile contains unsupported component rows")
        rows.append({
            "kind": kind, "canonical_ir_sha256": old["canonical_ir_sha256"],
            "sparse": {key: old[key] for key in ("raw", "padded", "preprocessed_cells", "proof_bytes")},
            "direct": {key: new[key] for key in ("raw", "padded", "preprocessed_cells", "proof_bytes")},
            "proof_bytes_saved_percent": round(100 * (1 - new["proof_bytes"] / old["proof_bytes"]), 2),
            "preprocessed_cells_saved_percent": round(
                100 * (1 - new["preprocessed_cells"] / old["preprocessed_cells"]), 2),
        })
    return {"schema": "s31-fixed-addition-profile-matrix-v1",
            "compiler_sha256": sparse_compiler,
            "scope": "one native edge witness per kind and lowering; same canonical relation",
            "controls": list(CONTROLS), "rows": rows,
            "limitations": ["Proof bytes and preprocessing cells are measured; proving and verification times are not in these two inputs.",
                            "Equal visible settings do not establish equal soundness across different AIRs."]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sparse", type=Path)
    parser.add_argument("direct", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    encoded = json.dumps(summarize(args.sparse, args.direct), sort_keys=True, indent=2) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
