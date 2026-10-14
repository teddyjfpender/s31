#!/usr/bin/env python3
"""Join source-derived short-lane traces to verified honest proof roots.

This checks three package shapes and their native diagnostic paths. It does
not establish arbitrary-proof opening authentication or PCS/FRI soundness.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.build import build_text  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.pure_native_rows import make_certificate  # noqa: E402
from package.short_lane_main_correspondence import check_export, expected_columns  # noqa: E402
from package.source_relation_fragment import check_source_relation_certificate  # noqa: E402
from package.verify import verify_package  # noqa: E402
import s31  # noqa: E402

SOURCE = ("circuit three(public x: [m31; 3]) -> public [m31; 3] { "
          "let a = x + x; let b = a - x; let c = a .* b; c }\n")
ONE_SOURCE = ("circuit case1(public x: [m31; 1]) -> public [m31; 1] { "
              "let a = x + x; let dead = a .* a; a }\n")
TWO_SOURCE = ("circuit two(public x: [m31; 2], public y: [m31; 2]) "
              "-> public [m31; 2] { let a = x + y; let b = y .* a; b }\n")


def check_main(package: Path, inputs: dict[str, list[int]], expected: list[int]) -> dict:
    """Join source-derived cells to one verified honest proof's main root."""
    source = (package / "source.s31").read_bytes()
    relation = (package / "source.s31.json").read_bytes()
    certificate = (package / "source-relation-certificate.json").read_bytes()
    ssa = check_source_relation_certificate(source, relation, certificate)["ssa"]
    if not (package / "pure-native-rows-certificate.json").is_file():
        raise AssertionError("main-trace check requires the native fixed-row certificate")
    make_certificate(package)
    manifest = json.loads((package / "manifest.json").read_bytes())
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key_path = package / "verification-key.json"
    key = json.loads(key_path.read_bytes())
    output_name = json.loads(relation)["public_outputs"][0]
    assignment = package.parent / f"{manifest['name']}-main-assignment.json"
    assignment.write_bytes(encoded({"public_inputs": inputs,
                                    "private_inputs": {},
                                    "public_outputs": {output_name: expected}}))
    physical = json.loads(s31.invoke(str(prover), "inspect-physical-rows", str(assignment)))
    root = json.loads(s31.invoke(str(prover), "inspect-physical-root", str(assignment)))
    checked = check_export(ssa, inputs, physical, root)
    _, main, public = expected_columns(ssa, inputs)
    columns_path = package.parent / f"{manifest['name']}-source-main-columns.json"
    columns_path.write_bytes(encoded({"schema": "s31-direct-gate-main-columns-v1",
                                      "main_columns": main}))
    recommitted = json.loads(s31.invoke(str(prover), "inspect-main-root-from-columns",
                                        str(columns_path)))
    statement = package.parent / f"{manifest['name']}-main-statement.json"
    statement.write_bytes(encoded({"public_inputs": inputs,
                                   "public_outputs": {output_name: expected}}))
    proof = package.parent / f"{manifest['name']}-main-proof.bin"
    s31.invoke(str(prover), "prove", str(assignment), str(proof))
    s31.invoke(str(verifier), str(proof), str(statement), str(key_path))
    proof_fixed, proof_main, _ = proof_roots(proof.read_bytes())
    digest = checked["source_derived_main_columns_sha256"]
    if (physical.get("schema") != "s31-direct-gate-public-functional-physical-v1" or
            root.get("schema") != "s31-direct-gate-public-main-root-v1" or
            recommitted.get("schema") != "s31-direct-gate-recommitted-main-root-v1" or
            any(report.get("program_sha256") != manifest["program_sha256"]
                for report in (physical, root, recommitted)) or
            recommitted.get("main_columns_sha256") != digest or
            root.get("main_columns_sha256") != digest or
            root.get("public_words") != public or
            proof_fixed.hex() != key["preprocessed_root"] or
            proof_main.hex() != recommitted.get("main_root") or
            proof_main.hex() != root.get("main_root")):
        raise AssertionError("source-derived main cells differ from accepted honest proof roots")
    changed_main = copy.deepcopy(main)
    changed_main[0][0] = (changed_main[0][0] + 1) % 2147483647
    changed_columns_path = package.parent / f"{manifest['name']}-changed-main-columns.json"
    changed_columns_path.write_bytes(encoded({"schema": "s31-direct-gate-main-columns-v1",
                                              "main_columns": changed_main}))
    changed_commitment = json.loads(s31.invoke(str(prover), "inspect-main-root-from-columns",
                                               str(changed_columns_path)))
    if (changed_commitment.get("main_root") == proof_main.hex() or
            changed_commitment.get("main_columns_sha256") == digest):
        raise AssertionError("changed source-derived main cell retained the accepted root")
    for label in ("fixed", "main", "claim", "padding", "padding-bool",
                  "root-padding-bool", "digest"):
        altered = copy.deepcopy(physical)
        changed_root = copy.deepcopy(root)
        if label == "fixed":
            altered["fixed_columns"][0][0] ^= 1
        elif label == "main":
            altered["main_columns"][0][0] = (altered["main_columns"][0][0] + 1) % 2147483647
        elif label == "claim":
            output_index = sum(len(value) for value in inputs.values()) + len(expected) - 1
            altered["public_words"][output_index] ^= 1
        elif label == "padding":
            altered["public_words"][-1] ^= 1
        elif label == "padding-bool":
            altered["public_words"][-1] = False
        elif label == "root-padding-bool":
            changed_root["public_words"][-1] = False
        else:
            changed_root["main_columns_sha256"] = "00" * 32
        try:
            check_export(ssa, inputs, altered, changed_root)
        except ValueError:
            pass
        else:
            raise AssertionError(f"source-derived main check accepted {label} mutation")
    return {"export_mutations_rejected": 7,
            "source_main_root_matches_verified_proof": True,
            "changed_source_main_cell_changes_root": True,
            "selected_output_is_last_node": output_name == ssa["nodes"][-1]["name"]}


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def reseal(package: Path, name: str, value: object) -> None:
    path = package / name
    path.write_bytes(encoded(value))
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["artifacts"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest_path.write_bytes(encoded(manifest))


def must_reject(package: Path, contains: str) -> None:
    try:
        make_certificate(package)
    except ValueError as exc:
        if contains not in str(exc):
            raise AssertionError(f"wrong rejection: {exc}") from exc
    else:
        raise AssertionError("forged row plan entered the native certificate")
    try:
        verify_package(package)
    except ValueError:
        pass
    else:
        raise AssertionError("forged package passed ordinary verification")


def run(work: Path, existing: Path | None,
        one_lane_existing: Path | None = None,
        two_input_existing: Path | None = None) -> dict:
    package = existing if existing is not None else work / "package"
    if existing is None:
        source = work / "short3.s31"
        source.write_text(SOURCE)
        build_text(source, package, "direct-gate")
    if (package / "source.s31").read_text() != SOURCE:
        raise AssertionError("test package has unexpected source")
    verified = verify_package(package)
    certificate = make_certificate(package)
    if (certificate["lane_count"] != 3 or
            [item["op"] for item in certificate["source_rows"]] !=
            ["add", "sub", "mul"]):
        raise AssertionError("native source row roster differs from test graph")
    main_checks = [check_main(package, {"x": [2, 5, 7]}, [8, 50, 98])]

    topology = json.loads((package / "gate-topology.json").read_bytes())
    source_rows = certificate["source_rows"]
    if len({row["trace_row"] for row in source_rows}) != 3:
        raise AssertionError("source rows overlap")
    for label, mutate, expected in (
        ("selector", lambda t: t["columns"][0]["values"].__setitem__(
            source_rows[0]["trace_row"], 0), "selector/address columns differ"),
        ("operand", lambda t: t["sub"][0].__setitem__("in1", 20),
         "selector/address columns differ"),
        ("public-copy", lambda t: t["add"][3].__setitem__("in0", 0),
         "selector/address columns differ"),
        ("extra-row", lambda t: t["add"].append({"in0": 1, "in1": 1, "out": 511}),
         "row layout differs"),
    ):
        forged = work / f"forged-{label}"
        shutil.copytree(package, forged)
        changed = json.loads(encoded(topology))
        mutate(changed)
        reseal(forged, "gate-topology.json", changed)
        must_reject(forged, expected)
        shutil.rmtree(forged)

    forged = work / "forged-certificate"
    shutil.copytree(package, forged)
    changed = json.loads((forged / "pure-native-rows-certificate.json").read_bytes())
    changed["source_rows"][0]["op"] = "mul"
    reseal(forged, "pure-native-rows-certificate.json", changed)
    try:
        verify_package(forged)
    except ValueError as exc:
        if "certificate differs from replay" not in str(exc):
            raise AssertionError(f"wrong certificate rejection: {exc}") from exc
    else:
        raise AssertionError("re-sealed wrong certificate passed verification")
    shutil.rmtree(forged)

    one_lane = one_lane_existing if one_lane_existing is not None else work / "one-lane"
    if one_lane_existing is None:
        one_source = work / "one.s31"
        one_source.write_text(ONE_SOURCE)
        build_text(one_source, one_lane, "direct-gate")
    if (one_lane / "source.s31").read_text() != ONE_SOURCE:
        raise AssertionError("one-lane package has unexpected source")
    verify_package(one_lane)
    main_checks.append(check_main(one_lane, {"x": [3]}, [6]))
    two_input = two_input_existing if two_input_existing is not None else work / "two-input"
    if two_input_existing is None:
        two_source = work / "two.s31"
        two_source.write_text(TWO_SOURCE)
        build_text(two_source, two_input, "direct-gate")
    if (two_input / "source.s31").read_text() != TWO_SOURCE:
        raise AssertionError("two-input package has unexpected source")
    verify_package(two_input)
    if make_certificate(two_input)["lane_count"] != 2:
        raise AssertionError("two-input source lacks the native row certificate")
    main_checks.append(check_main(two_input, {"x": [2, 5], "y": [7, 11]}, [63, 176]))
    if main_checks[1]["selected_output_is_last_node"]:
        raise AssertionError("one-lane sample no longer checks an earlier selected node")
    forged = work / "forged-boolean-abi-length"
    shutil.copytree(one_lane, forged)
    abi = json.loads((forged / "public-abi.json").read_bytes())
    abi["public_inputs"][0]["length"] = True  # Python True == 1 must not pass.
    reseal(forged, "public-abi.json", abi)
    must_reject(forged, "public ABI differs")
    shutil.rmtree(forged)
    return {"schema": "s31-short-lane-native-controls-v1",
            "source_rows": source_rows, "forgeries_rejected": 6,
            "main_trace_mutations_rejected": sum(check["export_mutations_rejected"]
                                                  for check in main_checks),
            "source_main_root_matches_verified_proof": all(
                check["source_main_root_matches_verified_proof"] for check in main_checks),
            "changed_source_main_cell_changes_root": all(
                check["changed_source_main_cell_changes_root"] for check in main_checks),
            "earlier_return_and_dead_suffix_checked": True,
            "honest_package_verified": verified["schema"] == "s31-package-v1",
            "one_lane_verified": True, "two_input_verified": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--package", type=Path)
    parser.add_argument("--one-lane-package", type=Path)
    parser.add_argument("--two-input-package", type=Path)
    args = parser.parse_args()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=True)
        result = run(work, args.package.resolve() if args.package else None,
                     args.one_lane_package.resolve() if args.one_lane_package else None,
                     args.two_input_package.resolve() if args.two_input_package else None)
    else:
        with tempfile.TemporaryDirectory(prefix="s31-pure-short-native-") as temporary:
            result = run(Path(temporary), args.package.resolve() if args.package else None,
                         args.one_lane_package.resolve() if args.one_lane_package else None,
                         args.two_input_package.resolve() if args.two_input_package else None)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
