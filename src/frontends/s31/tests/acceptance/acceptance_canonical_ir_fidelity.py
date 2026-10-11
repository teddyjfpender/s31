#!/usr/bin/env python3
"""Cross-check independent Python canonical IR against Zig's canonical.build.

This builds one small native oracle without a full proof/package build. Each
fixture is independently parsed from source text, compiled by the production
text frontend, serialized as normalized relation bytes, and hashed by Zig's
real relation parser and canonical builder. Digest mutations exercise output
selection, arithmetic, public input names, alias erasure, and two-digit IDs.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

from package.correspondence import canonical_ir_bytes, parse_source
from text_frontend import compile_text
from test_direct_alias_correspondence_generated import CORPUS_SHA256, corpus


def source(body: str, *, input_name: str = "x") -> str:
    return (f"circuit fidelity(public {input_name}: [m31; 4]) -> "
            f"public [m31; 4] {{ {body} }}")


def native_oracle(binary: Path, work: Path, name: str, text: str) -> tuple[str, str]:
    independent, syntax = parse_source(text.encode("ascii"))
    produced, _ = compile_text(text)
    if produced != independent:
        raise AssertionError(f"{name}: independent and production relations diverged")
    normalized = (json.dumps(produced, sort_keys=True, indent=2) + "\n").encode("ascii")
    relation_path = work / f"{name}.s31.json"
    relation_path.write_bytes(normalized)
    actual = subprocess.check_output([str(binary), str(relation_path)], text=True,
                                     cwd=ROOT).strip()
    expected = hashlib.sha256(canonical_ir_bytes(syntax)).hexdigest()
    if actual != expected:
        raise AssertionError(f"{name}: Zig {actual} != independent Python {expected}")
    return actual, normalized.decode("ascii")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-canonical-ir-fidelity-") as directory:
        work = Path(directory)
        binary = work / "canonical-ir-digest"
        try:
            subprocess.run([
                "zig", "build-exe", "-O", "ReleaseFast", "--dep", "stwo_s31_prototype",
                "-Mroot=src/frontends/s31/tests/acceptance/tools/canonical_ir_digest.zig",
                "--dep", "stwo_core", "-Mstwo_s31_prototype=src/frontends/s31/mod.zig",
                "-Mstwo_core=deps/stwo-zig/src/core/mod.zig",
                f"-femit-bin={binary}",
            ], cwd=ROOT, check=True, capture_output=True, text=True)
        except subprocess.CalledProcessError as exc:
            raise RuntimeError(f"native canonical IR oracle did not build:\n{exc.stderr}") from exc

        baseline = source(
            "let first = x + x; let second = x .* first; second")
        aliased = source(
            "let base = (x); let first = ((base) + (base)); "
            "let saved = (first); let second = ((base) .* (saved)); "
            "let returned = (second); (returned);")
        chosen_earlier = source(
            "let first = x + x; let second = x .* first; "
            "let returned = first; returned")
        changed_operation = source(
            "let first = x .* x; let second = x .* first; second")
        renamed_input = source(
            "let first = input + input; let second = input .* first; second",
            input_name="input")
        alpha_renamed = source(
            "let temporary = x + x; let second = x .* temporary; second")
        long_steps = []
        for index in range(1, 17):
            previous = "x" if index == 1 else f"y{index - 1}"
            op = "+" if index % 2 else ".*"
            long_steps.append(f"let y{index} = x {op} {previous};")
        long_chain = source(" ".join(long_steps) + " let selected = (y16); selected")

        cases = {
            "baseline": baseline, "aliased": aliased,
            "chosen-earlier": chosen_earlier,
            "changed-operation": changed_operation,
            "renamed-input": renamed_input,
            "alpha-renamed": alpha_renamed,
            "sixteen-steps": long_chain,
        }
        results = {name: native_oracle(binary, work, name, text)
                   for name, text in cases.items()}
        if results["baseline"] != results["aliased"]:
            raise AssertionError("aliases changed normalized relation or canonical IR")
        if results["baseline"][0] != results["alpha-renamed"][0]:
            raise AssertionError("an internal let rename changed canonical IR")
        for name in ("chosen-earlier", "changed-operation", "renamed-input"):
            if results[name][0] == results["baseline"][0]:
                raise AssertionError(f"{name}: canonical IR mutation was invisible")
        if results["sixteen-steps"][0] == results["baseline"][0]:
            raise AssertionError("two-digit SSA IDs were omitted from canonical IR")

        generated = corpus()
        corpus_bytes = b"\x00".join(
            case.source.encode() + b"\x01" + case.direct.encode()
            for case in generated)
        if hashlib.sha256(corpus_bytes).hexdigest() != CORPUS_SHA256:
            raise AssertionError("generated source corpus identity changed")
        for index, case in enumerate(generated):
            aliased = native_oracle(binary, work, f"generated-{index:03}-alias", case.source)
            direct = native_oracle(binary, work, f"generated-{index:03}-direct", case.direct)
            if aliased != direct:
                raise AssertionError(f"generated case {index}: alias erasure changed native IR")
        print(f"canonical IR fidelity: {len(cases)} handpicked and "
              f"{len(generated)} generated native/Python pairs passed")


if __name__ == "__main__":
    main()
