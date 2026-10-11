#!/usr/bin/env python3
"""Finite native/Lean differential for record ABI v2 descriptor name bytes.

The base relation is compiled from text. Each case changes exactly one name
in its public descriptor and the matching leaf path, where applicable. The
native runner requires malformed cases to fail specifically at
``InvalidRecordAbi``; generated Lean propositions check the same named tree's
shape and lexical decision. This is a finite test, not a parser refinement
theorem or a proof-verification test.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
REPO = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
from text_frontend import compile_text  # noqa: E402

SCHEMA = "s31-record-descriptor-native-corpus-v2"
BASE_SOURCE = (
    "struct Box { x: [m31; 1] }\n"
    "circuit lexical(private a: [m31; 1]) -> public Box { Box { x: a } }\n"
)
# The exact source and case bytes are pinned. A changed corpus requires an
# intentional update so the finite differential cannot silently shrink.
EXPECTED_CORPUS_SHA256 = "04281617e87db8ea06476f831688c869de2904724c9df9bd43d78e8db32a7ecf"


@dataclass(frozen=True)
class Case:
    label: str
    source: dict
    accepted: bool


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def names() -> tuple[tuple[str, str, bool], ...]:
    return (
        ("empty", "", False),
        ("one_byte", "A", True),
        ("max_128_bytes", "A" + "x" * 127, True),
        ("over_129_bytes", "A" + "x" * 128, False),
        ("leading_digit", "9a", False),
        ("hyphen", "a-b", False),
        ("non_ascii_utf8", "é", False),
        ("underscore_digits", "_Az09", True),
    )


def cases() -> list[Case]:
    base, _ = compile_text(BASE_SOURCE)
    abi = base["public_abi"]
    assert abi["inputs"][0]["name"] == "a"
    assert abi["inputs"][0]["leaves"][0]["path"] == [{"root": "a"}]
    assert abi["result"]["type"]["record"] == "Box"
    assert abi["result"]["type"]["fields"][0]["name"] == "x"
    assert abi["result"]["leaves"][0]["path"] == [
        {"root": "result"}, {"field": "x"}]
    out = [Case("compiled_base", base, True)]
    for location in ("root", "nominal", "field"):
        for label, value, accepted in names():
            source = copy.deepcopy(base)
            binding = source["public_abi"]
            if location == "root":
                root = binding["inputs"][0]
                root["name"] = value
                root["leaves"][0]["path"][0]["root"] = value
            elif location == "nominal":
                binding["result"]["type"]["record"] = value
            else:
                result = binding["result"]
                result["type"]["fields"][0]["name"] = value
                result["leaves"][0]["path"][1]["field"] = value
            out.append(Case(f"{location}_{label}", source, accepted))
    assert len(out) == 25 and len({case.label for case in out}) == len(out)
    return out


def encoded_corpus(items: list[Case]) -> tuple[bytes, str]:
    encoded = canonical({
        "schema": SCHEMA,
        "cases": [{"label": case.label,
                   "source": canonical(case.source).decode("ascii"),
                   "expected_valid": case.accepted} for case in items],
    })
    digest = hashlib.sha256(encoded).hexdigest()
    if digest != EXPECTED_CORPUS_SHA256:
        raise AssertionError(f"lexical corpus changed: {digest}; review and repin")
    return encoded, digest


def lean_string(value: str) -> str:
    # Lean accepts literal UTF-8 in strings. JSON's ASCII \u spelling does
    # not have the same parser syntax, so retain the concrete UTF-8 character.
    return json.dumps(value, ensure_ascii=False)


def lean_descriptor(case: Case) -> str:
    """Translate this deliberately tiny source-derived descriptor exactly."""
    binding = case.source["public_abi"]
    input_root, = binding["inputs"]
    result = binding["result"]
    field, = result["type"]["fields"]
    assert input_root["visibility"] == "private"
    assert input_root["type"] == {"kind": "m31", "length": 1}
    assert field["type"] == {"kind": "m31", "length": 1}
    assert result["name"] == "result"
    return (
        "{ inputs := [{ name := " + lean_string(input_root["name"]) +
        ", visibility := .priv, layout := .leaf .m31 1 }],\n"
        "    result := { name := \"result\", layout := "
        ".record " + lean_string(result["type"]["record"]) +
        " 1 (fun _ => " + lean_string(field["name"]) +
        ") (fun _ => .leaf .m31 1) } }"
    )


def lean_checks(items: list[Case]) -> int:
    lines = [
        "import S31.Gadgets.Functional.RecordDescriptorLexicalV2",
        "open S31.Functional.RecordDescriptorValidationV2",
        "open S31.Functional.RecordDescriptorLexicalV2",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 2000000",
        "",
    ]
    for index, case in enumerate(items):
        lines.extend((
            f"-- {case.label}",
            f"def lexicalCase{index} : Descriptor :=",
            "  " + lean_descriptor(case),
            f"theorem lexicalCase{index}_shape :",
            f"    checkDescriptor lexicalCase{index} = true := by decide",
            f"theorem lexicalCase{index}_name :",
            f"    checkLexicalDescriptor lexicalCase{index} = " +
            ("true" if case.accepted else "false") + " := by decide",
            "",
        ))
    with tempfile.TemporaryDirectory(prefix="s31-record-lexical-lean-") as temp:
        path = Path(temp) / "LexicalCases.lean"
        path.write_text("\n".join(lines), encoding="utf-8")
        run = subprocess.run(("lake", "env", "lean", str(path)), cwd=REPO / "formal/s31",
                             capture_output=True, text=True, timeout=180)
        if run.returncode:
            raise AssertionError("Lean lexical fixture failed:\n" +
                                 (run.stdout + run.stderr)[:4000])
    return len(items)


def native_checks(encoded: bytes, accepted: int, rejected: int) -> dict:
    # Reuse the scoped Zig runner from whole_descriptor_shape_v2.py. It calls
    # production relation.parseProgram and insists on InvalidRecordAbi for
    # every negative, so an earlier JSON/relation failure cannot pass.
    with tempfile.TemporaryDirectory(prefix="s31-record-lexical-native-") as temp:
        path = Path(temp) / "corpus.json"
        path.write_bytes(encoded)
        run = subprocess.run(
            ("zig", "build", "record-descriptor-parser-corpus",
             "-Doptimize=ReleaseFast", "-j1", "--", str(path)),
            cwd=S31, capture_output=True, text=True, timeout=180)
        if run.returncode:
            raise AssertionError("native lexical fixture failed:\n" +
                                 (run.stdout + run.stderr)[:4000])
        result = json.loads(run.stdout.strip().splitlines()[-1])
        if result != {"accepted": accepted, "rejected": rejected}:
            raise AssertionError(f"native lexical counts differ: {result}")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static", action="store_true", help="skip both external checkers")
    parser.add_argument("--lean-only", action="store_true", help="skip the native Zig runner")
    parser.add_argument("--native-only", action="store_true", help="skip the Lean kernel")
    args = parser.parse_args()
    if args.lean_only and args.native_only:
        parser.error("--lean-only and --native-only are mutually exclusive")
    items = cases()
    encoded, digest = encoded_corpus(items)
    accepted = sum(case.accepted for case in items)
    rejected = len(items) - accepted
    result = {"schema": "s31-record-lexical-native-lean-differential-v2",
              "corpus_sha256": digest, "source_derived_programs": 1,
              "locations": ["root", "nominal", "field"],
              "cases": len(items), "expected": {"accepted": accepted,
                                                  "invalid_record_abi": rejected}}
    if not args.static:
        if not args.native_only:
            result["lean_kernel_checked_cases"] = lean_checks(items)
        if not args.lean_only:
            result["native_record_validator"] = native_checks(encoded, accepted, rejected)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
