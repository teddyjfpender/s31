#!/usr/bin/env python3
"""Compare independently parsed effectful source bytes with Lean certificates."""

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


def certificate(source: bytes) -> bytes:
    relation = canonical(parse_source_fragment(source))
    return canonical(make_source_relation_certificate(source, relation))


def check(source: bytes, cert: bytes, accepted: bool, work: Path,
          grammar_error: bool = False) -> None:
    source_path = work / "case.s31"
    cert_path = work / "case.certificate.json"
    source_path.write_bytes(source)
    cert_path.write_bytes(cert)
    result = subprocess.run(
        ["lake", "env", "lean", "--run",
         "S31/Audit/GeneralLinearSSAEffectsSourceCheck.lean",
         str(source_path), str(cert_path)],
        cwd=FORMAL, capture_output=True, text=True, check=False,
    )
    if (result.returncode == 0) != accepted:
        raise AssertionError(result.stdout + result.stderr)
    if grammar_error and "source outside effects text grammar" not in result.stderr:
        raise AssertionError(result.stderr)


def run() -> None:
    fixture = FORMAL / "fixtures/correspondence/effects/affine_guard"
    base_source = fixture.with_suffix(".s31").read_bytes()
    base_cert = fixture.with_suffix(".certificate.json").read_bytes()
    if certificate(base_source) != base_cert:
        raise AssertionError("affine fixture differs from independent replay")
    const_left = (
        b"circuit constleft(private x: [m31; 2]) -> public [m31; 2] {\n"
        b"  let a = splat<2>(3_m31) + x;\n"
        b"  let b = splat<2>(4_m31) .* a;\n  b\n}\n"
    )
    live_unused = (
        b"circuit guard(public x: [m31; 2], private y: [m31; 2]) "
        b"-> public [m31; 2] {\n"
        b"  let a = x - splat<2>(9_m31);\n"
        b"  assert_eq(y, a);\n"
        b"  let unused = y + x;\n  a\n}\n"
    )
    with tempfile.TemporaryDirectory(prefix="s31-lean-effects-source-") as tmp:
        work = Path(tmp)
        for source in (base_source, const_left, live_unused):
            check(source, certificate(source), True, work)

        # This Lean semantic gate validates digest spelling but does not
        # recompute SHA-256. The package verifier owns that separate check.
        digest_only = json.loads(base_cert)
        digest_only["source_sha256"] = "0" * 64
        digest_only["relation_sha256"] = "1" * 64
        check(base_source, canonical(digest_only), True, work)

        # These fail at source parsing, before comparing any certificate.
        check(base_source.replace(b"7_m31", b"07_m31"), base_cert,
              False, work, grammar_error=True)
        check(base_source.replace(b"7_m31", b"2147483647_m31"), base_cert,
              False, work, grammar_error=True)
        check(base_source.replace(b"assert_eq(y, scaled);",
                                  b"assert_eq(y, out);"), base_cert,
              False, work, grammar_error=True)
        check(base_source.replace(b"assert_eq(y, scaled);",
                                  b"assert_eq(y, scaled); assert_eq(scaled, y);"),
              base_cert, False, work, grammar_error=True)
        check(const_left.replace(b"3_m31) + x", b"3_m31) - x"),
              certificate(const_left), False, work, grammar_error=True)

        # These remain grammatical but disagree with the certificate roster.
        check(base_source.replace(b"y - x", b"x - y"), base_cert,
              False, work)
        check(base_source.replace(b"assert_eq(y, scaled);", b"assert_eq(x, scaled);"),
              base_cert, False, work)
        forged = json.loads(base_cert)
        forged["ssa"]["nodes"][0]["constant"] = 8
        check(base_source, canonical(forged), False, work)
        forged = json.loads(base_cert)
        forged["ssa"]["assertions"] = []
        check(base_source, canonical(forged), False, work)
        check(base_source, base_cert + b" " * 65536, False, work)
    print("Lean effects source-byte bridge: 3 semantic pairs plus 1 digest-boundary control admitted, 10 rejected")


if __name__ == "__main__":
    run()
