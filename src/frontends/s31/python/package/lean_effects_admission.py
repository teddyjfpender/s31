"""Pinned Lean admission for the bounded effectful S31 text fragment.

The static package gate and per-proof statement gate are separate because a
compiled package has no private assignment. This opt-in API fails closed for
any source outside Lean's bounded effectful grammar. The checker binary and
package identities must be pinned by a caller outside the package.
"""

from __future__ import annotations

import hmac
import os
import stat
import subprocess
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from package.context import invoke
from package.source_relation_fragment import (
    LEAN_EFFECTS_PROFILE, check_source_relation_certificate,
)
from package.trust import PIN_RE, admitted_snapshot
from runtime.proof_inputs import (
    _bounded_digest, _copy_bounded, proof_inputs_snapshot,
)

MAX_CHECKER_BYTES = 256 << 20
MAX_LEAN_INPUT_BYTES = 65536
CHECKER_TIMEOUT_SECONDS = 30


def _run_checker(checker: Path, mode: str, *paths: Path) -> None:
    if any(path.stat().st_size > MAX_LEAN_INPUT_BYTES for path in paths):
        raise ValueError("Lean effects gate input exceeds 65536 bytes")
    try:
        result = subprocess.run(
            [str(checker), mode, *(str(path) for path in paths)],
            capture_output=True, text=True, timeout=CHECKER_TIMEOUT_SECONDS,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError("pinned Lean effects checker could not complete") from exc
    if result.returncode:
        detail = (result.stderr + result.stdout).strip()[:512]
        raise ValueError(f"Lean effects {mode} gate rejected: {detail}")


@contextmanager
def _pinned_checker(checker_path: Path, checker_sha256: str) -> Iterator[Path]:
    if not isinstance(checker_sha256, str) or not PIN_RE.fullmatch(checker_sha256):
        raise ValueError("Lean effects checker requires a lowercase external SHA-256 pin")
    with tempfile.TemporaryDirectory(prefix="s31-lean-effects-checker-") as temporary:
        captured = Path(temporary) / "checker"
        digest = _copy_bounded(checker_path, captured, MAX_CHECKER_BYTES)
        if not hmac.compare_digest(digest.hex(), checker_sha256):
            raise ValueError("Lean effects checker SHA-256 pin mismatch")
        os.chmod(captured, stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
        yield captured
        if _bounded_digest(captured, MAX_CHECKER_BYTES) != digest:
            raise ValueError("Lean effects checker snapshot changed during admission")


@contextmanager
def bounded_effects_snapshot(
    package: Path, pins: dict[str, str], checker_path: Path,
    checker_sha256: str,
) -> Iterator[tuple[Path, dict, Path]]:
    """Yield a pinned package only after exact Lean effectful static admission.

    Ordinary `verify_package` is an integrity check. This stronger path also
    needs a trusted checker digest and an effectful source certificate. It
    never treats package-provided hashes as external authentication.
    """
    with _pinned_checker(checker_path, checker_sha256) as checker:
        with admitted_snapshot(package, pins) as (snapshot, manifest):
            if "source_text_sha256" not in manifest:
                raise ValueError("Lean effects admission requires a text package")
            artifacts = manifest["artifacts"]
            if "source-relation-certificate.json" not in artifacts:
                raise ValueError("Lean effects admission requires a source relation certificate")
            source = snapshot / "source.s31"
            certificate = snapshot / "source-relation-certificate.json"
            relation = snapshot / "source.s31.json"
            abi = snapshot / "public-abi.json"
            checked = check_source_relation_certificate(
                source.read_bytes(), relation.read_bytes(), certificate.read_bytes())
            if (checked.get("lean_semantic_profile") != LEAN_EFFECTS_PROFILE or
                    checked.get("unmodeled_features") != []):
                raise ValueError("package is outside bounded Lean effects profile")
            _run_checker(checker, "static", source, certificate, relation, abi)
            yield snapshot, manifest, checker


def verify_effectful_proof(
    package: Path, proof: Path, assignment: Path, statement: Path | None,
    pins: dict[str, str], checker_path: Path, checker_sha256: str,
) -> str:
    """Admit exact source and statement bytes, then invoke native verification.

    The same private copy of the public statement is checked by Lean and
    passed to the native verifier. The assignment is copied before package
    admission and checked for changes after native verification.
    """
    with proof_inputs_snapshot(proof, statement,
                               statement_limit=MAX_LEAN_INPUT_BYTES) as (captured_proof, captured_statement):
        with tempfile.TemporaryDirectory(prefix="s31-effects-assignment-") as temporary:
            captured_assignment = Path(temporary) / "assignment.json"
            assignment_digest = _copy_bounded(
                assignment, captured_assignment, MAX_LEAN_INPUT_BYTES)
            with bounded_effects_snapshot(package, pins, checker_path,
                                          checker_sha256) as (snapshot, manifest, checker):
                source = snapshot / "source.s31"
                certificate = snapshot / "source-relation-certificate.json"
                relation = snapshot / "source.s31.json"
                abi = snapshot / "public-abi.json"
                _run_checker(checker, "statement", source, certificate, relation,
                             abi, captured_assignment, captured_statement)
                verifier = snapshot / "bin" / f"s31-{manifest['name']}-native-verifier"
                key = snapshot / "verification-key.json"
                invoke(str(verifier), "check-key", str(key))
                result = invoke(str(verifier), str(captured_proof),
                                str(captured_statement), str(key))
            if _bounded_digest(captured_assignment,
                               MAX_LEAN_INPUT_BYTES) != assignment_digest:
                raise ValueError("Lean effects assignment snapshot changed during verification")
            return result
