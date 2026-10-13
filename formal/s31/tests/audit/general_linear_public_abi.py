#!/usr/bin/env python3
"""Exercise the Lean ABI/assignment/public-word byte gate on three profiles."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def run(executable: Path, mode: str, paths: dict[str, Path], accepted: bool) -> None:
    result = subprocess.run(
        [str(executable), mode, *(str(paths[name]) for name in
            ("source", "certificate", "relation", "abi", "assignment", "public_words"))],
        capture_output=True, text=True, check=False, timeout=30,
    )
    if (result.returncode == 0) != accepted:
        raise AssertionError(
            f"{mode} {paths}: accepted={result.returncode == 0}, expected={accepted}; "
            f"{result.stdout} {result.stderr}"
        )


def main() -> None:
    formal = Path(__file__).resolve().parents[2]
    fixture = formal / "fixtures/correspondence/public_abi"
    executable = formal / ".lake/build/bin/s31-general-linear-public-abi-check"
    sources = {
        "pure": fixture / "pure.certificate.json",
        "effects": formal / "fixtures/correspondence/effects/affine_guard.certificate.json",
        "ordered": fixture / "ordered.certificate.json",
    }
    relations = {
        "pure": fixture / "pure.relation.json",
        "effects": formal / "fixtures/correspondence/effects/affine_guard.relation.json",
        "ordered": fixture / "ordered.relation.json",
    }
    source_texts = {
        "pure": fixture / "pure.s31",
        "effects": formal / "fixtures/correspondence/effects/affine_guard.s31",
        "ordered": fixture / "ordered.s31",
    }
    for mode in sources:
        paths = {
            "source": source_texts[mode],
            "certificate": sources[mode],
            "relation": relations[mode],
            "abi": fixture / f"{mode}.abi.json",
            "assignment": fixture / f"{mode}.assignment.json",
            "public_words": fixture / f"{mode}.public_words.bin",
        }
        run(executable, mode, paths, True)

    baseline = {
        "source": source_texts["ordered"],
        "certificate": sources["ordered"],
        "relation": relations["ordered"],
        "abi": fixture / "ordered.abi.json",
        "assignment": fixture / "ordered.assignment.json",
        "public_words": fixture / "ordered.public_words.bin",
    }
    descriptor = json.loads(baseline["abi"].read_bytes())
    assignment = json.loads(baseline["assignment"].read_bytes())
    certificate = json.loads(baseline["certificate"].read_bytes())
    mutants: list[tuple[str, str, bytes]] = []

    for label, change in (
        ("public-input-order", lambda value: value["public_inputs"].reverse()),
        ("wrong-input-width", lambda value: value["public_inputs"][1].update(length=3)),
        ("wrong-output-name", lambda value: value["public_outputs"][0].update(name="x")),
        ("wrong-encoding", lambda value: value.update(encoding="raw u32")),
        ("extra-abi-field", lambda value: value.update(extra=True)),
    ):
        value = copy.deepcopy(descriptor)
        change(value)
        mutants.append((label, "abi", canonical(value)))

    for label, change in (
        ("public-input-value", lambda value: value["public_inputs"]["x"].__setitem__(0, 9)),
        ("private-input-value", lambda value: value["private_inputs"]["salt"].__setitem__(0, 98)),
        ("noncanonical-word", lambda value: value["private_inputs"]["salt"].__setitem__(0, 2147483647)),
        ("wrong-output", lambda value: value["public_outputs"]["sum"].__setitem__(1, 7)),
        ("missing-private", lambda value: value["private_inputs"].clear()),
        ("extra-public", lambda value: value["public_inputs"].update(extra=[0, 0])),
    ):
        value = copy.deepcopy(assignment)
        change(value)
        mutants.append((label, "assignment", canonical(value)))

    changed = copy.deepcopy(certificate)
    changed["ssa"]["inputs"][0]["visibility"] = "private"
    mutants.append(("certificate-visibility", "certificate", canonical(changed)))
    changed = copy.deepcopy(certificate)
    changed["ssa"]["lane_count"] = 3
    mutants.append(("certificate-lane-count", "certificate", canonical(changed)))

    relation = json.loads(baseline["relation"].read_bytes())
    for label, change in (
        ("relation-visibility", lambda value: value["inputs"][0].update(visibility="private")),
        ("relation-lane-count", lambda value: value["inputs"][0].update(length=3)),
        ("relation-output-name", lambda value: value.update(public_outputs=["x"])),
        ("relation-circuit-name", lambda value: value.update(name="other_circuit")),
        ("relation-invalid-node", lambda value: value["nodes"][0].update(rhs="missing")),
        ("relation-arithmetic-op", lambda value: value["nodes"][0].update(op="sub")),
        ("relation-arithmetic-operand", lambda value: value["nodes"][0].update(rhs="x")),
        ("relation-extra-assertion", lambda value: value.update(
            assertions=[{"lhs": "x", "rhs": "y"}])),
        ("relation-proof-mode", lambda value: value.update(proof_mode="blinded")),
    ):
        value = copy.deepcopy(relation)
        change(value)
        mutants.append((label, "relation", canonical(value)))

    raw = baseline["public_words"].read_bytes()
    for label, value in (
        ("swapped-public-words", raw[8:16] + raw[:8] + raw[16:]),
        ("wrong-output-word", raw[:16] + bytes([5]) + raw[17:]),
        ("nonzero-padding", raw[:-1] + bytes([1])),
        ("short-public-statement", raw[:-1]),
        ("noncanonical-u32", raw[:4] + bytes([255, 255, 255, 127]) + raw[8:]),
    ):
        mutants.append((label, "public_words", value))

    abi_raw = baseline["abi"].read_bytes()
    mutants += [
        ("duplicate-abi-key", "abi", abi_raw.replace(
            b'  "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",',
            b'  "encoding": "bad",\n  "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",', 1)),
        ("noncanonical-abi-spacing", "abi", abi_raw.replace(
            b'  "schema":', b' "schema":', 1)),
        ("oversized-abi", "abi", abi_raw + b" " * 65536),
    ]
    source_raw = baseline["source"].read_bytes()
    mutants += [
        ("source-circuit-name", "source", source_raw.replace(
            b"circuit ordered", b"circuit renamed", 1)),
        ("source-public-visibility", "source", source_raw.replace(
            b"public x", b"private x", 1)),
        ("source-input-order", "source", source_raw.replace(
            b"x + y", b"y + x", 1)),
    ]
    with tempfile.TemporaryDirectory(prefix="s31-lean-public-abi-") as temp:
        renamed = copy.deepcopy(relation)
        renamed["name"] = "renamed"
        renamed_path = Path(temp) / "matching-renamed-relation.data"
        renamed_path.write_bytes(canonical(renamed))
        renamed_source_path = Path(temp) / "matching-renamed-source.s31"
        renamed_source_path.write_bytes(source_raw.replace(
            b"circuit ordered", b"circuit renamed", 1))
        run(executable, "ordered", {**baseline, "source": renamed_source_path,
                                    "relation": renamed_path}, True)
        for label, target, contents in mutants:
            path = Path(temp) / f"{label}.data"
            path.write_bytes(contents)
            candidate = dict(baseline)
            candidate[target] = path
            run(executable, "ordered", candidate, False)
        effect_relation = json.loads(relations["effects"].read_bytes())
        effects = {
            "source": source_texts["effects"],
            "certificate": sources["effects"],
            "relation": relations["effects"],
            "abi": fixture / "effects.abi.json",
            "assignment": fixture / "effects.assignment.json",
            "public_words": fixture / "effects.public_words.bin",
        }
        for label, change in (
            ("effects-constant", lambda value: value["nodes"][0].update(constant=8)),
            ("effects-op", lambda value: value["nodes"][1].update(op="add_const")),
            ("effects-assertion", lambda value: value["assertions"][0].update(rhs="shifted")),
        ):
            value = copy.deepcopy(effect_relation)
            change(value)
            path = Path(temp) / f"{label}.relation.json"
            path.write_bytes(canonical(value))
            run(executable, "effects", {**effects, "relation": path}, False)
    print(f"Lean public ABI controls: 3 fixtures + 1 matched rename accepted, "
          f"{len(mutants) + 3} rejected")


if __name__ == "__main__":
    main()
