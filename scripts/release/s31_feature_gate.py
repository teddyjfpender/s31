#!/usr/bin/env python3
"""Run scoped S31 language feature checks with reproducible command evidence.

This finite regression runner is not a release certificate or a soundness
proof. It delegates every semantic and proof check to existing test programs.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[2]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402

KINDS = tuple(f"{sign}{width}" for sign in ("u", "i")
              for width in (8, 16, 32, 64, 128))
ACCEPT = "src/frontends/s31/tests/acceptance/"
SECURITY = "src/frontends/s31/tests/python/security/"
FUNCTIONAL = "src/frontends/s31/tests/python/functional/"
GENERATED = "src/frontends/s31/tests/python/generated/"


@dataclasses.dataclass(frozen=True)
class Check:
    id: str
    script: str
    args: tuple[str, ...]
    format: str
    native: bool = False
    expected_kinds: tuple[str, ...] = ()
    expected_modes: tuple[str, ...] = ()

    def argv(self, python: str = sys.executable) -> tuple[str, ...]:
        return (python, "-B", self.script, *self.args)


def checks(mode: str) -> tuple[Check, ...]:
    if mode not in ("source", "smoke", "full"):
        raise ValueError(f"unknown mode: {mode}")
    base = [
        Check("v1-source-relation", SECURITY + "test_source_relation_fragment.py", (), "unittest"),
        Check("static-tuple-erasure-source", SECURITY + "test_static_tuple_erasure.py", (), "unittest"),
        Check("v2-record-source-relation", SECURITY + "test_record_source_fragment.py", (), "unittest"),
        Check("typed-structural-derivation-source", SECURITY + "test_structural_derivation.py",
              (), "unittest"),
        Check("static-sum-dce-source", FUNCTIONAL + "test_static_sum_dce.py", (), "unittest"),
        Check("static-enum-effects-source", GENERATED + "test_static_enum_effect_generated.py",
              (), "unittest"),
        Check("direct-add-source", ACCEPT + "math/addition.py", ("--source-only",),
              "addition-source", expected_kinds=KINDS),
        Check("direct-sub-le-source", ACCEPT + "math/direct_binary.py", (),
              "binary-source", expected_kinds=KINDS),
        Check("direct-mul-source", ACCEPT + "math/direct_multiplication.py", (),
              "multiplication-source", expected_kinds=KINDS,
              expected_modes=("checked", "wrapping")),
        Check("record-u8-source", ACCEPT + "record_abi/public_u8_direct_gate_v2.py", (),
              "record-u8-source"),
        Check("record-u16-source", ACCEPT + "record_abi/public_u16_direct_gate_v2.py", (),
              "record-u16-source"),
        Check("record-u32-source", ACCEPT + "record_abi/public_u32_direct_gate_v2.py", (),
              "record-u32-source"),
    ]
    if mode == "source":
        return tuple(base)
    native = [
        Check("static-sum-dce-native", ACCEPT + "functional/static_sum_dce.py", (),
              "static-sum-native", native=True),
        Check("static-enum-if-native", ACCEPT + "functional/static_enum_if.py", (),
              "static-enum-if-native", native=True),
        Check("v2-record-source-native", ACCEPT + "record_abi/record_source_fragment_v2.py", (),
              "record-source-native", native=True),
        Check("combined-helper-tuple-native",
              ACCEPT + "compiler_correspondence/combined_helper_tuple_native_rows.py", (),
              "combined-helper-tuple-native", native=True),
    ]
    if mode == "smoke":
        native.extend((
            Check("direct-add-u8-native", ACCEPT + "math/addition.py",
                  ("--lowering", "direct-gate", "--case", "u8"),
                  "addition-native", True, ("u8",)),
            Check("direct-sub-le-i8-native", ACCEPT + "math/direct_binary.py",
                  ("--native", "--case", "i8"), "binary-native", True, ("i8",)),
            Check("direct-mul-u8-native", ACCEPT + "math/direct_multiplication.py",
                  ("--native", "--case", "u8", "--mode", "both"),
                  "multiplication-native", True, ("u8",), ("checked", "wrapping")),
            Check("record-u8-native", ACCEPT + "record_abi/public_u8_direct_gate_v2.py",
                  ("--native",), "record-u8-native", True),
            Check("record-u32-native", ACCEPT + "record_abi/public_u32_direct_gate_v2.py",
                  ("--native",), "record-u32-native", True),
        ))
    else:
        native.extend((
            Check("pow65535-native", ACCEPT + "math/power_chain.py", (),
                  "power-native", True),
            Check("pow-factor-native", ACCEPT + "math/factor_power.py", (),
                  "factor-power-native", True),
            Check("direct-add-all-native", ACCEPT + "math/addition.py",
                  ("--lowering", "direct-gate"), "addition-native", True, KINDS),
            Check("direct-sub-le-all-native", ACCEPT + "math/direct_binary.py",
                  ("--native",), "binary-native", True, KINDS),
            Check("direct-mul-all-native", ACCEPT + "math/direct_multiplication.py",
                  ("--native", "--mode", "both"),
                  "multiplication-native", True, KINDS, ("checked", "wrapping")),
            Check("record-u8-native", ACCEPT + "record_abi/public_u8_direct_gate_v2.py",
                  ("--native",), "record-u8-native", True),
            Check("record-u16-native", ACCEPT + "record_abi/public_u16_direct_gate_v2.py",
                  ("--native",), "record-u16-native", True),
            Check("record-u32-native", ACCEPT + "record_abi/public_u32_direct_gate_v2.py",
                  ("--native",), "record-u32-native", True),
        ))
    return tuple(base + native)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def valid_digest(value: object) -> bool:
    return type(value) is str and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def raw(value: bytes | str) -> bytes:
    return value if isinstance(value, bytes) else value.encode("utf-8")


def failure_excerpt(value: bytes | str) -> str:
    """Keep compiler diagnostics at the start as well as the command tail."""
    decoded = raw(value).decode("utf-8", errors="replace")
    if len(decoded) <= 5000:
        return decoded
    return decoded[:3000] + "\n... stderr omitted ...\n" + decoded[-2000:]


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def _case_set(records: object, keys: tuple[str, ...]) -> set[tuple[str, ...]]:
    if not isinstance(records, list) or any(not isinstance(row, dict) for row in records):
        raise ValueError("case report must contain a list of objects")
    values = [tuple(row.get(key) for key in keys) for row in records]
    if any(any(type(value) is not str for value in item) for item in values):
        raise ValueError("case report has a missing or invalid case identity")
    if len(values) != len(set(values)):
        raise ValueError("case report has duplicate identities")
    return set(values)


def validate_output(check: Check, stdout: str, stderr: str,
                    expected_compiler: str | None = None) -> dict:
    """Check the reported finite controls as well as the subprocess exit code."""
    if check.format == "unittest":
        match = re.search(r"Ran (\d+) tests? in [^\n]+", stderr)
        if not match or int(match.group(1)) < 1 or not re.search(r"(?m)^OK\s*$", stderr):
            raise ValueError("unittest did not report a nonempty successful suite")
        count = int(match.group(1))
        if check.id == "static-enum-effects-source" and count != 2:
            raise ValueError("static enum source corpus did not run both checks")
        return {"tests": count}
    try:
        report = json.loads(stdout)
    except json.JSONDecodeError as exc:
        raise ValueError("check did not emit one JSON report") from exc
    if not isinstance(report, dict):
        raise ValueError("check report must be an object")
    if expected_compiler is not None and "compiler_sha256" in report and report["compiler_sha256"] != expected_compiler:
        raise ValueError("check report has a different compiler fingerprint")
    fmt = check.format
    if fmt.startswith("addition-"):
        expected_schema = ("s31-int-addition-native-v1" if check.native
                           else "s31-int-addition-source-v1")
        if report.get("schema") != expected_schema or report.get("lowering") != (
                "direct-gate" if check.native else "sparse-wide-gate"):
            raise ValueError("addition report has wrong schema or lowering")
        records = report.get("cases")
        if _case_set(records, ("kind",)) != {(kind,) for kind in check.expected_kinds}:
            raise ValueError("addition report has missing or extra widths")
        for row in records:
            if check.native:
                controls = ("native_verifier_accepted", "changed_public_statement_rejected",
                            "native_overflow_rejected")
            else:
                controls = ("source_and_oracle_checked", "native_not_run")
            if any(row.get(key) is not True for key in controls):
                raise ValueError("addition report failed a control")
    elif fmt.startswith("binary-"):
        if report.get("schema") != "s31-direct-integer-binary-v1" or report.get("native") is not check.native:
            raise ValueError("subtraction/order report has wrong schema or mode")
        records = report.get("cases")
        expected = {(kind, op) for kind in check.expected_kinds for op in ("sub_checked", "le")}
        if _case_set(records, ("kind", "operation")) != expected:
            raise ValueError("subtraction/order report has missing or extra operations")
        for row in records:
            controls = (("native_verifier_accepted", "changed_public_statement_rejected")
                        if check.native else ("source_and_oracle_checked",))
            if any(row.get(key) is not True for key in controls):
                raise ValueError("subtraction/order report failed a control")
            if check.native and row["operation"] == "sub_checked" and row.get("native_underflow_rejected") is not True:
                raise ValueError("native subtraction did not reject underflow")
    elif fmt.startswith("multiplication-"):
        if (report.get("schema") != "s31-direct-integer-multiplication-v1" or
                report.get("native") is not check.native):
            raise ValueError("multiplication report has wrong schema or mode")
        records = report.get("cases")
        expected = {(kind, mode) for kind in check.expected_kinds for mode in check.expected_modes}
        if _case_set(records, ("kind", "mode")) != expected:
            raise ValueError("multiplication report has missing or extra widths or modes")
        for row in records:
            controls = (("native_verifier_accepted", "changed_public_statement_rejected")
                        if check.native else ("source_and_oracle_checked",))
            if any(row.get(key) is not True for key in controls):
                raise ValueError("multiplication report failed a control")
            if check.native and row["mode"] == "checked" and row.get("native_overflow_rejected") is not True:
                raise ValueError("native multiplication did not reject overflow")
    elif fmt == "static-sum-native":
        if any(report.get(key) is not True for key in (
                "native_verifier_accepted", "changed_public_statement_rejected",
                "equal_native_air_geometry")):
            raise ValueError("static-sum DCE report failed a proof or geometry control")
    elif fmt == "static-enum-if-native":
        proofs = report.get("proofs")
        raw_rows = report.get("raw")
        padded_rows = report.get("padded")
        valid_proofs = ([item for item in proofs if
                         type(item) is dict and
                         type(item.get("flag")) is int and
                         type(item.get("x")) is int and
                         item.get("native_verified") is True and
                         item.get("changed_claim_rejected") is True and
                         item.get("oracle_passed") is True and
                         type(item.get("proof_bytes")) is int and
                         item["proof_bytes"] > 0]
                        if type(proofs) is list else [])
        if (report.get("schema") != "s31-static-enum-if-acceptance-v1" or
                report.get("profile") != "direct-m31-v4" or
                type(raw_rows) is not dict or raw_rows.get("qm31_ops") != 280 or
                type(padded_rows) is not dict or padded_rows.get("qm31_ops") != 512 or
                report.get("preprocessed_cells") != 4096 or
                report.get("equal_relation_and_air") is not True or
                report.get("selected_and_eager_partial_arms_rejected") is not True or
                type(proofs) is not list or len(proofs) != 3 or
                len(valid_proofs) != 3 or
                {(item["flag"], item["x"]) for item in valid_proofs} !=
                {(1, 7), (0, 7), (0, 0)}):
            raise ValueError("static enum conditional report failed proof or AIR controls")
    elif fmt == "power-native":
        cases = report.get("cases")
        edge = report.get("zero_residue")
        expected = {"addition-chain": (39, 397, 512, 4096),
                    "binary": (120, 559, 1024, 8192)}
        if (report.get("schema") != "s31-power-chain-native-v2" or
                report.get("lanes") != 8 or report.get("stages") != 4 or
                report.get("exponent_per_stage") != 65535 or
                report.get("fused_exponent") != 2146172967 or
                report.get("saved_arithmetic_nodes") != 81 or
                report.get("saved_raw_qm31_rows") != 162 or
                report.get("halved_padded_rows") is not True or
                type(cases) is not list or len(cases) != 2 or
                {case.get("kind") for case in cases if type(case) is dict} != set(expected) or
                type(edge) is not dict or edge.get("symbolic_exponent") != 2147483646 or
                edge.get("nodes") != 37 or
                any(edge.get(key) is not True for key in
                    ("zero_input_verified", "nonzero_input_verified", "native_verified",
                     "changed_claim_rejected", "independent_oracle_passed")) or
                type(edge.get("proof_bytes")) is not int or edge["proof_bytes"] <= 0):
            raise ValueError("power chain report has wrong scope or cost delta")
        for case in cases:
            if ((case.get("nodes"), case.get("raw_qm31_rows"),
                 case.get("padded_qm31_rows"), case.get("preprocessed_cells")) !=
                    expected[case["kind"]] or
                    case.get("native_verified") is not True or
                    case.get("changed_claim_rejected") is not True or
                    case.get("independent_oracle_passed") is not True or
                    case.get("symbolic_exponent_checked") is not True or
                    type(case.get("proof_bytes")) is not int or
                    case["proof_bytes"] <= 0):
                raise ValueError("power chain report failed geometry or proof control")
    elif fmt == "factor-power-native":
        cases = report.get("cases")
        expected = {"factor-chain": (47, 413, 512, 4096),
                    "binary": (128, 575, 1024, 8192)}
        if (report.get("schema") != "s31-factor-power-native-v2" or
                report.get("lanes") != 8 or report.get("stages") != 4 or
                report.get("exponent_per_stage") != 196605 or
                report.get("fused_exponent") != 2041318647 or
                report.get("binary_source_sha256") !=
                "0d84aa30895d22dd5c105c7a0a384913d53ef0b0f45364dcbd4470cf93b952a3" or
                report.get("saved_arithmetic_nodes") != 81 or
                report.get("saved_raw_qm31_rows") != 162 or
                report.get("halved_padded_rows") is not True or
                type(cases) is not list or len(cases) != 2 or
                {case.get("kind") for case in cases if type(case) is dict} != set(expected)):
            raise ValueError("factor power report has wrong scope or cost delta")
        for case in cases:
            if ((case.get("nodes"), case.get("raw_qm31_rows"),
                 case.get("padded_qm31_rows"), case.get("preprocessed_cells")) !=
                    expected[case["kind"]] or
                    case.get("native_verified") is not True or
                    case.get("changed_claim_rejected") is not True or
                    case.get("independent_oracle_passed") is not True or
                    case.get("symbolic_exponent_checked") is not True or
                    type(case.get("proof_bytes")) is not int or
                    case["proof_bytes"] <= 0):
                raise ValueError("factor power report failed geometry or proof control")
    elif fmt == "record-source-native":
        if (report.get("schema") != "s31-record-source-fragment-native-v2" or
                report.get("capability") != "source-to-relation-only" or
                report.get("native_verifier_accepted") is not True or
                report.get("abi_valid_changed_claim_rejected_by_proof") is not True):
            raise ValueError("record source fragment report failed a control")
    elif fmt == "combined-helper-tuple-native":
        root = report.get("fixed_root")
        if (report.get("schema") != "s31-combined-helper-tuple-native-rows-v1" or
                report.get("source_rows") != [{"id": 2, "in0": 16, "in1": 20,
                                               "op": "sub", "out": 21,
                                               "trace_row": 493}] or
                report.get("flat_air_equal") is not True or
                report.get("native_proof_verified") is not True or
                report.get("structural_lean_release_verified") is not True or
                report.get("structural_release_script_sha256") != digest(
                    (ROOT / "scripts/release/structural_lean_release.py").read_bytes()) or
                report.get("wrong_checker_pin_rejected") is not True or
                report.get("missing_structural_tree_rejected") is not True or
                report.get("changed_fixed_root_rejected") is not True or
                type(root) is not str or len(root) != 64 or
                any(char not in "0123456789abcdef" for char in root) or
                type(report.get("proof_bytes")) is not int or
                report["proof_bytes"] <= 0):
            raise ValueError("combined helper/tuple native report failed a control")
    elif fmt.startswith("record-u32-"):
        if (report.get("schema") != "s31-public-u32-record-v2" or
                report.get("native") is not check.native or
                report.get("limb_order") != "little-endian" or
                report.get("honest") != [0, 0xffffffff] or
                report.get("input_range_bits") != 32 or
                report.get("result_aliases_public_input") is not True):
            raise ValueError("public u32 record ABI report failed a range or alias control")
    elif fmt.startswith("record-u"):
        width = 8 if "u8" in fmt else 16
        if (report.get("schema") != f"s31-public-u{width}-record-v2" or
                report.get("native") is not check.native or
                report.get(f"result_u{width}_aliases_input") is not True or
                type(report.get("range_gates_per_input_word")) is not int or
                report["range_gates_per_input_word"] != width):
            raise ValueError("public record ABI report failed a range or alias control")
    else:
        raise ValueError(f"unknown report format: {fmt}")
    counted = report.get("proofs", []) if fmt == "static-enum-if-native" else report.get("cases", [])
    controls = {"schema": report.get("schema"), "cases": len(counted)}
    if fmt == "combined-helper-tuple-native":
        controls.update({field: report[field] for field in (
            "structural_lean_release_verified", "structural_release_script_sha256",
            "wrong_checker_pin_rejected", "missing_structural_tree_rejected")})
    return controls


def execute(check: Check) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(check.argv(), cwd=ROOT, capture_output=True,
                          timeout=3600, check=False)


def run_suite(mode: str, selected: set[str] | None = None, *,
              execute_fn: Callable[[Check], subprocess.CompletedProcess] = execute,
              fingerprint_fn: Callable[[], str] = s31.compiler_fingerprint) -> dict:
    inventory = checks(mode)
    ids = {check.id for check in inventory}
    selected = ids if selected is None else selected
    if not selected or selected - ids:
        raise ValueError(f"unknown or empty check selection: {sorted(selected - ids)}")
    rows: dict[str, dict] = {check.id: {"status": "not-run"} for check in inventory}
    report = {"schema": "s31-scoped-feature-gate-v1", "mode": mode,
              "release_claim": "not-established", "selected": sorted(selected),
              "gate_script_sha256": digest(Path(__file__).read_bytes()),
              "compiler_sha256_start": None, "compiler_sha256_end": None,
              "cases": rows}
    try:
        start = fingerprint_fn()
        if not valid_digest(start):
            raise ValueError("invalid compiler fingerprint")
        report["compiler_sha256_start"] = start
        script_digests = {check.id: digest((ROOT / check.script).read_bytes())
                          for check in inventory if check.id in selected}
    except Exception as exc:
        report["startup_error"] = f"compiler fingerprint: {type(exc).__name__}: {exc}"
        report.update(selected_passed=False, mode_complete=False, compiler_identity_consistent=False)
        return report
    for check in inventory:
        if check.id not in selected:
            continue
        argv = check.argv()
        script = ROOT / check.script
        command = {"argv": list(argv), "cwd": str(ROOT),
                   "script_sha256": script_digests[check.id]}
        row = {"status": "failed", "native": check.native,
               "command": command, "command_sha256": digest(canonical(command))}
        rows[check.id] = row
        begun = time.monotonic()
        try:
            before = fingerprint_fn()
            if before != start:
                raise ValueError("compiler fingerprint drift before command")
            if digest(script.read_bytes()) != command["script_sha256"]:
                raise ValueError("check script changed before command")
            result = execute_fn(check)
            row["duration_ms"] = round((time.monotonic() - begun) * 1000)
            row["returncode"] = result.returncode
            outcome = {"command_sha256": row["command_sha256"],
                       "returncode": result.returncode,
                       "stdout_sha256": digest(raw(result.stdout)),
                       "stderr_sha256": digest(raw(result.stderr))}
            row.update(outcome)
            row["result_sha256"] = digest(canonical(outcome))
            if digest(script.read_bytes()) != command["script_sha256"]:
                raise ValueError("check script changed during command")
            after = fingerprint_fn()
            if after != start:
                raise ValueError("compiler fingerprint drift during command")
            if result.returncode != 0:
                raise ValueError(f"check exited {result.returncode}: {failure_excerpt(result.stderr)}")
            row["controls"] = validate_output(check, raw(result.stdout).decode("utf-8"),
                                              raw(result.stderr).decode("utf-8"), start)
            row["status"] = "passed"
        except Exception as exc:
            row["error"] = f"{type(exc).__name__}: {exc}"
            break
    try:
        report["compiler_sha256_end"] = fingerprint_fn()
    except Exception as exc:
        report["fingerprint_end_error"] = f"{type(exc).__name__}: {exc}"
    report["compiler_identity_consistent"] = (
        report["compiler_sha256_start"] == report["compiler_sha256_end"] and
        valid_digest(report["compiler_sha256_end"]))
    try:
        report["script_identity_consistent"] = all(
            digest((ROOT / check.script).read_bytes()) == script_digests[check.id]
            for check in inventory if check.id in selected)
    except OSError:
        report["script_identity_consistent"] = False
    report["selected_passed"] = (all(rows[name]["status"] == "passed" for name in selected)
                                 and report["compiler_identity_consistent"]
                                 and report["script_identity_consistent"])
    report["mode_complete"] = report["selected_passed"] and selected == ids
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("source", "smoke", "full"), default="source")
    parser.add_argument("--case", action="append", help="select one check ID; repeatable")
    parser.add_argument("--list", action="store_true", help="list checks without running them")
    parser.add_argument("--out", type=Path, help="write the JSON report as well as stdout")
    args = parser.parse_args(argv)
    inventory = checks(args.mode)
    ids = {check.id for check in inventory}
    selected = set(args.case) if args.case else ids
    if not selected or selected - ids:
        parser.error(f"unknown check IDs for {args.mode}: {sorted(selected - ids)}")
    if args.list:
        report = {"schema": "s31-scoped-feature-gate-v1", "mode": args.mode,
                  "release_claim": "not-established", "selected": sorted(selected),
                  "compiler_sha256_start": None, "compiler_sha256_end": None,
                  "cases": {check.id: {"status": "not-run", "native": check.native,
                                       "argv": list(check.argv())} for check in inventory},
                  "selected_passed": False, "mode_complete": False}
        exit_code = 0
    else:
        report = run_suite(args.mode, selected)
        exit_code = 0 if report["selected_passed"] else 1
    data = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(data)
    sys.stdout.write(data)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
