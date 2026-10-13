#!/usr/bin/env python3
"""Exercise the Lean source-byte/certificate checker on live bounded sources."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.source_relation_fragment import (  # noqa: E402
    make_source_relation_certificate,
    parse_source_fragment,
)


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def check(source: bytes, certificate: bytes, expected: bool, work: Path) -> None:
    source_path = work / "case.s31"
    certificate_path = work / "case.certificate.json"
    source_path.write_bytes(source)
    certificate_path.write_bytes(certificate)
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "S31/Audit/GeneralLinearSSASourceCheck.lean",
         str(source_path), str(certificate_path)],
        cwd=FORMAL, capture_output=True, text=True, check=False,
    )
    if (result.returncode == 0) != expected:
        raise AssertionError(result.stdout + result.stderr)


def certificate(source: bytes) -> bytes:
    relation = canonical(parse_source_fragment(source))
    return canonical(make_source_relation_certificate(source, relation))


def run() -> None:
    fixture = FORMAL / "fixtures/correspondence/source_relation_pure_text"
    base_source = fixture.with_suffix(".s31").read_bytes()
    base_certificate = fixture.with_suffix(".certificate.json").read_bytes()
    if certificate(base_source) != base_certificate:
        raise AssertionError("fixture differs from fresh independent source replay")

    sources = [
        base_source,
        b"circuit subtract(private left: [m31; 5], private right: [m31; 5]) "
        b"-> public [m31; 5] { let delta = left - right; "
        b"let doubled = delta + delta; doubled }\n",
        b"circuit pair(public x: [m31; 2], public y: [m31; 2]) "
        b"-> public [m31; 2] { let a = x .* y; let b = y - a; a }\n",
        b"circuit four(private a: [m31; 1], private b: [m31; 1], "
        b"private c: [m31; 1], private d: [m31; 1]) "
        b"-> public [m31; 1] { let out = c + d; out }\n",
    ]
    with tempfile.TemporaryDirectory(prefix="s31-lean-source-") as tmp:
        work = Path(tmp)
        for source in sources:
            check(source, certificate(source), True, work)
        changed_source = base_source.replace(b"a - x", b"x - a")
        changed_name = base_source.replace(b"let b", b"let renamed").replace(
            b"a .* b", b"a .* renamed")
        check(changed_source, base_certificate, False, work)
        check(changed_name, base_certificate, False, work)
        check(base_source + b"???", base_certificate, False, work)
        five_inputs = sources[-1].replace(
            b"private d: [m31; 1])",
            b"private d: [m31; 1], private e: [m31; 1])")
        check(five_inputs, certificate(sources[-1]), False, work)

        forged = json.loads(base_certificate)
        forged["ssa"]["nodes"][1]["rhs"] = 1
        check(base_source, canonical(forged), False, work)
        forged = json.loads(base_certificate)
        forged["ssa"]["inputs"][0]["visibility"] = "private"
        check(base_source, canonical(forged), False, work)
        check(base_source, base_certificate + b" " * 65_536, False, work)
    print("Lean source-byte bridge: 4 admitted, 7 rejected")


if __name__ == "__main__":
    run()
