#!/usr/bin/env python3
"""Focused manifest-resealed package corpus for the Lean record-v2 checker."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import abi  # noqa: E402
from package.record_source_fragment import check_package_record_source_relation  # noqa: E402
from package.structural_derivation import check_certificate, make_certificate  # noqa: E402
from text_frontend import compile_text  # noqa: E402


SOURCES = (
    """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit paired(public x: Pair, private y: Pair) -> public Pair {
    let z = x.left .* y.right;
    Pair { right: x.right, left: z }
}
""",
    """struct Quad { a: [m31; 1], b: [m31; 1], c: [m31; 1], d: [m31; 1] }
circuit mix(public x: Quad) -> public Quad {
    let p = x.a + x.b;
    let q = p .* x.c;
    Quad { d: x.d, c: q, b: x.b, a: p }
}
""",
    """struct Triple { a: [m31; 1], b: [m31; 1], c: [m31; 1] }
circuit copy(public x: Triple, private y: Triple) -> public Triple {
    let p = y.a + y.b;
    Triple { c: x.c, b: p, a: p }
}
""",
    """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let Pair { right: saved, left } = x;
    let Pair { right: secret } = y;
    let p = left .* secret;
    let q = p + saved;
    Pair { right: saved, left: q }
}
""",
    """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit interleave(public x: Pair, private y: Pair) -> public Pair {
    let Pair { left: saved } = x;
    let p = x.right + y.left;
    let Pair { right: secret } = y;
    let q = p .* secret;
    Pair { right: saved, left: q }
}
""",
)


def encode(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def package_files(source: str) -> dict[str, bytes]:
    source_bytes = source.encode()
    relation, _ = compile_text(source)
    relation_bytes = encode(relation)
    abi_bytes = encode(abi(relation, "direct-gate"))
    tree = make_certificate(source_bytes, relation_bytes, abi_bytes, "direct-gate")
    return {"source.s31": source_bytes, "typed-structural-derivation.json": encode(tree),
            "source.s31.json": relation_bytes, "public-abi.json": abi_bytes}


def run(checker: Path, files: dict[str, bytes], accepted: bool, reason: str) -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-v2-lean-") as directory:
        folder = Path(directory)
        for name, data in files.items():
            (folder / name).write_bytes(data)
        relation = json.loads(files["source.s31.json"])
        manifest = {"schema": "s31-package-v1", "name": relation["name"],
                    "lowering": "direct-gate", "text_frontend_version": 1,
                    "source_text_sha256": hashlib.sha256(files["source.s31"]).hexdigest(),
                    "program_sha256": hashlib.sha256(files["source.s31.json"]).hexdigest(),
                    "artifacts": {name: hashlib.sha256(data).hexdigest()
                                  for name, data in files.items()}}
        (folder / "manifest.json").write_bytes(encode(manifest))
        if accepted:
            check_package_record_source_relation(folder)
            check_certificate(files["source.s31"], files["source.s31.json"],
                              files["public-abi.json"], "direct-gate",
                              files["typed-structural-derivation.json"])
        command = [str(checker), *(str(folder / name) for name in
                   ("source.s31", "typed-structural-derivation.json",
                    "source.s31.json", "public-abi.json"))]
        result = subprocess.run(command, capture_output=True, text=True,
                                check=False, timeout=20)
        if (result.returncode == 0) != accepted:
            raise AssertionError(f"{reason}: unexpected status {result.returncode}: "
                                 f"{result.stdout}{result.stderr}")


def main() -> None:
    checker = (Path(sys.argv[1]) if len(sys.argv) == 2 else
               ROOT / "formal/s31/.lake/build/bin/s31-general-record-v2-source-check")
    for index, source in enumerate(SOURCES):
        run(checker, package_files(source), True, f"real source {index}")

    baseline = package_files(SOURCES[0])
    forged = copy.deepcopy(baseline)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["program"]["steps"][0]["expr"]["lhs"]["field"] = "right"
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed wrong source projection")

    forged = copy.deepcopy(baseline)
    relation = json.loads(forged["source.s31.json"])
    relation["nodes"][0]["rhs"] = "_s31_abi_input_2"
    forged["source.s31.json"] = encode(relation)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["relation_sha256"] = hashlib.sha256(forged["source.s31.json"]).hexdigest()
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed wrong normalized operand")

    forged = copy.deepcopy(baseline)
    boundary = json.loads(forged["public-abi.json"])
    boundary["boundary"]["result"]["leaves"].reverse()
    forged["public-abi.json"] = encode(boundary)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["public_abi_sha256"] = hashlib.sha256(forged["public-abi.json"]).hexdigest()
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed wrong public result order")

    forged = copy.deepcopy(baseline)
    forged["source.s31"] += b"junk\n"
    run(checker, forged, False, "extra source tokens")

    forged = copy.deepcopy(baseline)
    forged["source.s31.json"] = forged["source.s31.json"].replace(
        b'"version": 2', b'"version": 2, "version": 2')
    run(checker, forged, False, "duplicate relation key")

    pattern = package_files(SOURCES[3])
    forged = copy.deepcopy(pattern)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["program"]["steps"][0]["expr"]["field"] = "left"
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed wrong record-pattern field")

    forged = copy.deepcopy(pattern)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["program"]["steps"][2]["expr"]["source"]["name"] = "x"
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed private pattern source as public")

    forged = copy.deepcopy(pattern)
    relation = json.loads(forged["source.s31.json"])
    relation["nodes"][0]["rhs"] = "_s31_abi_input_1"
    forged["source.s31.json"] = encode(relation)
    tree = json.loads(forged["typed-structural-derivation.json"])
    tree["relation_sha256"] = hashlib.sha256(forged["source.s31.json"]).hexdigest()
    forged["typed-structural-derivation.json"] = encode(tree)
    run(checker, forged, False, "resealed pattern's private arithmetic wire")

    source = pattern["source.s31"]
    for old, new, reason in (
        (b"let Pair { right: saved, left }",
         b"let Pair { right: saved, left: saved }",
         "duplicate pattern binder"),
        (b"let Pair { right: saved, left }",
         b"let Other { right: saved, left }", "wrong nominal pattern"),
        (b"= x;", b"= Pair { left: x.left, right: x.right };",
         "computed pattern right side"),
        (b"let Pair { right: saved, left }",
         b"let Pair { left: saved, right: left }",
         "field swap differs from sealed relation"),
    ):
        if source.count(old) != 1:
            raise AssertionError(f"ambiguous pattern fixture: {reason}")
        forged = copy.deepcopy(pattern)
        forged["source.s31"] = source.replace(old, new)
        run(checker, forged, False, reason)

    print("record-v2 exact-source corpus: 5 accepted, 12 rejected")


if __name__ == "__main__":
    main()
