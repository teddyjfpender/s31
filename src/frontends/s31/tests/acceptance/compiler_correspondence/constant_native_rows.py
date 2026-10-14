#!/usr/bin/env python3
"""Check scalar literal erasure against direct-Gate rows and an honest proof.

The exact-byte Lean effects gate is run when its executable is supplied.
Native row and proof-root comparisons remain bounded honest-proof evidence;
they do not authenticate an arbitrary PCS opening.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

from package import build as package_build  # noqa: E402
from package.pure_native_rows import admitted_ssa, make_certificate  # noqa: E402
from package.source_relation_fragment import (  # noqa: E402
    check_source_relation_certificate, make_source_relation_certificate,
)
from package.verify import verify_package  # noqa: E402
from pure_native_short_lanes import check_main  # noqa: E402
from text_frontend import compile_text  # noqa: E402

SOURCE = ("circuit cchain(public x: [m31; 2]) -> public [m31; 2] { "
          "let seven = splat<2>(7_m31); let a = x + seven; "
          "let b = a .* seven; let c = b + splat<2>(9_m31); "
          "let d = c - seven; d }\n")
INLINE = ("circuit cchain(public x: [m31; 2]) -> public [m31; 2] { "
          "let a = x + splat<2>(7_m31); "
          "let b = a .* splat<2>(7_m31); "
          "let c = b + splat<2>(9_m31); "
          "let d = c - splat<2>(7_m31); d }\n")


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def lean_check(checker: Path, package: Path, work: Path) -> None:
    assignment = work / "assignment.json"
    assignment.write_bytes(encoded({"public_inputs": {"x": [3, 5]},
                                    "private_inputs": {},
                                    "public_outputs": {"d": [72, 86]}}))
    statement = work / "statement.json"
    statement.write_bytes(encoded({"public_inputs": {"x": [3, 5]},
                                   "public_outputs": {"d": [72, 86]}}))
    common = [str(package / name) for name in
              ("source.s31", "source-relation-certificate.json",
               "source.s31.json", "public-abi.json")]

    def accepted(mode: str, paths: list[str], expect: bool) -> None:
        result = subprocess.run([str(checker), mode, *paths], capture_output=True,
                                text=True, timeout=45, check=False)
        if (result.returncode == 0) != expect:
            raise AssertionError(f"Lean {mode} acceptance differed: {result.stderr}")

    accepted("static", common, True)
    accepted("statement", [*common, str(assignment), str(statement)], True)
    altered_source = work / "wrong-literal.s31"
    altered_source.write_bytes((package / "source.s31").read_bytes().replace(
        b"7_m31", b"8_m31", 1))
    accepted("static", [str(altered_source), *common[1:]], False)


def run(lean_checker: Path | None = None) -> dict[str, object]:
    if lean_checker is not None and not lean_checker.is_file():
        raise FileNotFoundError(lean_checker)
    old_invoke = package_build.invoke

    def bounded_invoke(*args: str) -> str:
        if args[:2] == ("zig", "build"):
            args = (*args[:2], "-j4", *args[2:])
        return old_invoke(*args)

    package_build.invoke = bounded_invoke
    try:
        with tempfile.TemporaryDirectory(prefix="s31-constant-native-") as temporary:
            work = Path(temporary)
            source = work / "constant.s31"
            source.write_text(SOURCE)
            package = package_build.build_text(source, work / "package", "direct-gate")
            verify_package(package)
            relation_bytes = (package / "source.s31.json").read_bytes()
            certificate = check_source_relation_certificate(
                (package / "source.s31").read_bytes(), relation_bytes,
                (package / "source-relation-certificate.json").read_bytes())
            relation = json.loads(relation_bytes)
            inline_relation, _ = compile_text(INLINE)
            if relation != inline_relation or [node["op"] for node in relation["nodes"]] != [
                    "add_const", "mul_const", "add_const", "add_const"]:
                raise AssertionError("source literal alias added a normalized node")
            rows = make_certificate(package)
            source_rows = rows["source_rows"]
            if (rows != json.loads((package / "pure-native-rows-certificate.json").read_bytes()) or
                    [row.get("constant") for row in source_rows] !=
                    [7, 7, 9, 2147483640] or
                    not (source_rows[0]["in1"] == source_rows[1]["in1"] <
                         source_rows[2]["in1"] < source_rows[3]["in1"]) or
                    sum(rows["gate_counts"].values()) != 512):
                raise AssertionError("native constant row schedule differs from source")

            for trivial in (0, 1):
                trivial_source = ("circuit trivial(public x: [m31; 2]) -> public [m31; 2] { "
                                  f"let y = x + splat<2>({trivial}_m31); y }}\n")
                trivial_relation, _ = compile_text(trivial_source)
                trivial_certificate = make_source_relation_certificate(
                    trivial_source.encode(), encoded(trivial_relation))
                if admitted_ssa(trivial_certificate, trivial_source.encode()):
                    raise AssertionError("trivial constant entered native row profile")

            # The text compiler's output is the direct relation fed to the
            # native builder. Building that relation separately checks that
            # the literal alias has no hidden AIR cost.
            direct_source = work / "direct.json"
            direct_source.write_bytes(relation_bytes)
            direct = package_build.build_json(direct_source, work / "direct", "direct-gate")
            text_cost = json.loads((package / "cost-report.json").read_bytes())
            direct_cost = json.loads((direct / "cost-report.json").read_bytes())
            for field in ("raw", "padded", "trace_log_size", "canonical_ir_sha256",
                          "preprocessed_root", "circuit_hash"):
                if text_cost[field] != direct_cost[field]:
                    raise AssertionError(f"literal alias changed native {field}")

            if lean_checker is not None:
                lean_check(lean_checker, package, work)
            main = check_main(package, {"x": [3, 5]}, [72, 86])

            # A re-sealed changed constant in the certificate cannot enter
            # the source-derived row checker or ordinary package verifier.
            forged = work / "forged"
            shutil.copytree(package, forged)
            altered = copy.deepcopy(rows)
            altered["source_rows"][0]["constant"] = 8
            (forged / "pure-native-rows-certificate.json").write_bytes(encoded(altered))
            manifest = json.loads((forged / "manifest.json").read_bytes())
            manifest["artifacts"]["pure-native-rows-certificate.json"] = hashlib.sha256(
                (forged / "pure-native-rows-certificate.json").read_bytes()).hexdigest()
            (forged / "manifest.json").write_bytes(encoded(manifest))
            try:
                verify_package(forged)
            except ValueError:
                pass
            else:
                raise AssertionError("re-sealed wrong constant certificate passed")
            return {"schema": "s31-direct-gate-constant-correspondence-v1",
                    "normalized_ops": [node["op"] for node in relation["nodes"]],
                    "source_constants": [row["constant"] for row in source_rows],
                    "reused_constant_address": source_rows[0]["in1"],
                    "zero_cost_alias_matches_direct_graph": True,
                    "raw_qm31_rows": text_cost["raw"]["qm31_ops"],
                    "padded_qm31_rows": text_cost["padded"]["qm31_ops"],
                    "lean_exact_byte_run_checked": lean_checker is not None,
                    "lean_changed_source_rejected": lean_checker is not None,
                    "honest_main_proof_root_join": main["source_main_root_matches_verified_proof"],
                    "native_export_mutations_rejected": main["export_mutations_rejected"],
                    "trivial_constant_admission_rejections": 2,
                    "resealed_wrong_constant_rejected": True}
    finally:
        package_build.invoke = old_invoke


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-checker", type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.lean_checker), sort_keys=True))
