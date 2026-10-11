#!/usr/bin/env python3
"""Read-only replay of paired phase result; --native reruns every verifier."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from study import (ASSIGNMENTS, COUNTS, RESULT, canonical, case, changed_result,
                   frozen, parse, phase_check, process, proof_layer_rejection,
                   sha, stage_check, tagged)


def audit(out: Path, native: bool = False) -> dict:
    protocol, protocol_hash = frozen()
    raw = (out / "result.json").read_bytes()
    if raw != RESULT.read_bytes():
        raise ValueError("raw and committed compact results differ")
    result = parse(raw)
    if (raw != canonical(result) or result.get("schema") != "s31-mixed-phase-v1-result" or
            result.get("protocol_sha256") != protocol_hash or
            result.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"] or
            result.get("compiler_sha256") != protocol["compiler_sha256"] or
            result.get("host") != protocol["host"] or
            result.get("proof_pairs") != ASSIGNMENTS * len(COUNTS) or
            result.get("native_accepted_proofs") != 2 * ASSIGNMENTS * len(COUNTS) or
            result.get("changed_result_rejections") != 2 * ASSIGNMENTS * len(COUNTS) or
            result.get("exact_proof_byte_pairs") != ASSIGNMENTS * len(COUNTS) or
            result.get("predictive_model_enabled") is not False or
            result.get("speedup_claim_enabled") is not False):
        raise ValueError("compact result identity or tally changed")
    rows = result["rows"]
    if len(rows) != ASSIGNMENTS * len(COUNTS):
        raise ValueError("incomplete row set")
    verified = 0
    for count in COUNTS:
        directory = out / f"n{count}"
        source, _, _ = case(count, 0)
        if sha((directory / "source.s31.json").read_bytes()) != sha(source):
            raise ValueError("raw source differs from protocol")
        base = f"s31-mixed_phase_v1_n{count}-mixed-general-"
        prover = directory / "package/bin" / (base + "prover")
        verifier = directory / "package/bin" / (base + "native-verifier")
        binary_sha = {"prover": sha(prover.read_bytes()), "verifier": sha(verifier.read_bytes())}
        if binary_sha != result["binary_sha256"][str(count)]:
            raise ValueError("package binaries differ from measured result")
        for index in range(ASSIGNMENTS):
            row = rows[(0 if count == 2 else ASSIGNMENTS) + index]
            source_bytes, assignment, statement = case(count, index)
            expected_order = (["untimed", "timed"] if index % 2 == 0 else
                              ["timed", "untimed"])
            if (row["count"] != count or row["assignment_index"] != index or
                    row["order"] != expected_order or
                    row["source_sha256"] != protocol["roster"][str(count)]["source_sha256"] or
                    row["assignment_sha256"] != sha(assignment) or
                    row["statement_sha256"] != sha(statement) or
                    (directory / f"a{index:02d}.assignment.json").read_bytes() != assignment or
                    (directory / f"a{index:02d}.statement.json").read_bytes() != statement or
                    (directory / f"a{index:02d}.changed-result.json").read_bytes() !=
                        changed_result(source_bytes, statement)):
                raise ValueError(f"N{count}/a{index}: claim identity changed")
            proofs = []
            for mode in expected_order:
                trial = row[mode]
                proof = directory / f"a{index:02d}.{mode}.proof"
                proof_bytes = proof.read_bytes()
                stderr = (directory / f"a{index:02d}.{mode}.stderr").read_bytes()
                stage = tagged(stderr, b"S31_MIXED_STAGE_V1")
                if ((directory / f"a{index:02d}.{mode}.emitted.json").read_bytes() != statement or
                        trial["binary_sha256"] != binary_sha or
                        trial["proof_sha256"] != sha(proof_bytes) or
                        trial["proof_bytes"] != len(proof_bytes) or
                        stage["proof_bytes"] != len(proof_bytes) or
                        stage["source_sha256"] != row["source_sha256"] or
                        trial["first_verified_wall_ns"] !=
                            trial["prover_process_wall_ns"] +
                            trial["external_verifier_process_wall_ns"] or
                        trial["changed_result_rejected"] is not True):
                    raise ValueError(f"N{count}/a{index}/{mode}: proof or stage identity changed")
                native_ns = stage_check(stage, trial["prover_process_wall_ns"])
                if native_ns != trial["native_prove_including_setup_ns"]:
                    raise ValueError("native interval differs from saved stage")
                phase_lines = [line for line in stderr.splitlines()
                               if line.startswith(b"S31_MIXED_NATIVE_PHASE_V1 ")]
                if mode == "timed":
                    if len(phase_lines) != 1:
                        raise ValueError("timed phase record missing or duplicated")
                    phase = tagged(stderr, b"S31_MIXED_NATIVE_PHASE_V1")
                    for name, value in phase_check(stage, phase,
                                                  trial["prover_process_wall_ns"]).items():
                        if trial[name] != value:
                            raise ValueError(f"saved {name} differs from raw phase")
                elif phase_lines:
                    raise ValueError("untimed mode emitted phase telemetry")
                proofs.append(proof_bytes)
                if native:
                    statement_path = directory / f"a{index:02d}.statement.json"
                    changed_path = directory / f"a{index:02d}.changed-result.json"
                    ok, _ = process([str(verifier), str(proof), str(statement_path)])
                    bad, _ = process([str(verifier), str(proof), str(changed_path)])
                    if ok.returncode or b"verified" not in ok.stderr or \
                            not proof_layer_rejection(bad):
                        raise ValueError("native verifier replay failed")
                    verified += 1
            if proofs[0] != proofs[1]:
                raise ValueError("timing changed native proof bytes")
    return {"schema": "s31-mixed-phase-v1-audit",
            "protocol_sha256": protocol_hash, "result_sha256": sha(raw),
            "paired_statements_checked": len(rows),
            "byte_identical_proof_pairs": len(rows),
            "native_verifier_replays": verified}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    print(json.dumps(audit(args.out.resolve(), args.native), sort_keys=True))


if __name__ == "__main__":
    main()
