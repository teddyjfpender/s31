#!/usr/bin/env python3
"""Live zero-extra-row and exact-byte Lean check for a static S31 tuple."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
import package.build as package_build  # noqa: E402
from package.source_relation_fragment import LEAN_EFFECTS_PROFILE  # noqa: E402

PRODUCT = """circuit tuple_case(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let p = (x, y);
    let out = p.0 + p.1;
    out
}
"""
SCALAR = """circuit tuple_case(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let out = x + y;
    out
}
"""


def checked(command: list[str], *, succeeds: bool = True) -> None:
    result = subprocess.run(command, capture_output=True, text=True, check=False,
                            timeout=45)
    if (result.returncode == 0) != succeeds:
        raise AssertionError(f"command had unexpected status: {command}\n"
                             f"{result.stdout}{result.stderr}")


def run(checker: Path) -> dict[str, object]:
    if not checker.is_file():
        raise FileNotFoundError(f"build the Lean checker first: {checker}")
    old_invoke = package_build.invoke

    def bounded_invoke(*args: str) -> str:
        if args[:2] == ("zig", "build"):
            args = (*args[:2], "-j12", *args[2:])
        return old_invoke(*args)

    package_build.invoke = bounded_invoke
    try:
        with tempfile.TemporaryDirectory(prefix="s31-static-tuple-") as directory:
            work = Path(directory)
            product_source, scalar_source = work / "product.s31", work / "scalar.s31"
            product_source.write_text(PRODUCT)
            scalar_source.write_text(SCALAR)
            product = s31.build(product_source, work / "product-package", "direct-gate")
            scalar = s31.build(scalar_source, work / "scalar-package", "direct-gate")
            relation = (product / "source.s31.json").read_bytes()
            if relation != (scalar / "source.s31.json").read_bytes():
                raise AssertionError("product changed normalized relation")
            product_cost = json.loads((product / "cost-report.json").read_text())
            scalar_cost = json.loads((scalar / "cost-report.json").read_text())
            if product_cost != scalar_cost:
                raise AssertionError("product changed native Gate cost report")
            certificate = json.loads((product / "source-relation-certificate.json").read_text())
            if (certificate["lean_semantic_profile"] != LEAN_EFFECTS_PROFILE or
                    certificate["unmodeled_features"]):
                raise AssertionError("static product escaped bounded Lean profile")
            assignment = work / "assignment.json"
            s31.write_json(assignment, {"public_inputs": {"x": [1, 2]},
                                        "private_inputs": {"y": [3, 4]},
                                        "public_outputs": {"out": [4, 6]}})
            words = work / "public_words.bin"
            words.write_bytes(b"".join(value.to_bytes(4, "little")
                                       for value in (1, 2, 4, 6, 0, 0, 0, 0)))
            static = [str(checker), "static", str(product / "source.s31"),
                      str(product / "source-relation-certificate.json"),
                      str(product / "source.s31.json"), str(product / "public-abi.json")]
            checked(static)
            checked([str(checker), "run", *static[2:], str(assignment), str(words)])
            changed = work / "changed.s31"
            changed.write_text(PRODUCT.replace("p.0 + p.1", "p.0 + p.0"))
            checked([str(checker), "static", str(changed), *static[3:]], succeeds=False)
            trials = {}
            for label, package in (("product", product), ("scalar", scalar)):
                trial = s31.trial(package, assignment, work / f"{label}-proof")
                if not trial["native_verifier_accepted"]:
                    raise AssertionError(f"native verifier rejected {label}")
                trials[label] = trial["proof_bytes"]
            return {"schema": "s31-static-tuple-erasure-v1",
                    "normalized_relation_equal": True, "complete_cost_report_equal": True,
                    "raw_qm31_rows": product_cost["raw"]["qm31_ops"],
                    "product_proof_bytes": trials["product"],
                    "scalar_proof_bytes": trials["scalar"],
                    "lean_static_and_assignment_accepted": True,
                    "changed_projection_rejected": True}
    finally:
        package_build.invoke = old_invoke


if __name__ == "__main__":
    checker = (Path(sys.argv[1]) if len(sys.argv) == 2 else
               ROOT / "formal/s31/.lake/build/bin/s31-general-linear-effects-package-check")
    print(json.dumps(run(checker.resolve()), sort_keys=True))
