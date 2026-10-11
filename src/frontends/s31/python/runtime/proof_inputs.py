"""Capture untrusted proof inputs before admitting a verifier package.

The native verifier reads paths after package admission. A caller can replace
those paths while admission runs, so both inputs must be private copies before
the first admission check. The limits match ``mvp_runtime.zig::verify``.
"""

from __future__ import annotations

import hashlib
import os
import stat
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator


MAX_PROOF_BYTES = 16 << 20
MAX_STATEMENT_BYTES = 1 << 20
_CHUNK_BYTES = 1 << 20
_READ_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
_DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def _regular_input(path: Path) -> int:
    """Open every path component without following a caller-owned symlink."""
    absolute = Path(os.path.abspath(path))
    # macOS presents its root-owned /var and /tmp directories through aliases
    # to /private. Normalize only those two system links; all user-controlled
    # descendants still receive O_NOFOLLOW checks.
    if sys.platform == "darwin" and len(absolute.parts) > 1:
        first = absolute.parts[1]
        alias = Path("/") / first
        if (first in {"var", "tmp"} and alias.is_symlink() and
                alias.lstat().st_uid == 0 and
                os.path.realpath(alias) == f"/private/{first}"):
            absolute = Path("/private") / absolute.relative_to("/")
    directory = os.open(absolute.anchor, _DIR_FLAGS)
    try:
        for part in absolute.parts[1:-1]:
            next_directory = os.open(part, _DIR_FLAGS, dir_fd=directory)
            os.close(directory)
            directory = next_directory
        source = os.open(absolute.name, _READ_FLAGS, dir_fd=directory)
    except OSError as exc:
        raise ValueError(f"proof input is missing, linked, or inaccessible: {absolute}") from exc
    finally:
        os.close(directory)
    if not stat.S_ISREG(os.fstat(source).st_mode):
        os.close(source)
        raise ValueError(f"proof input is not a regular file: {absolute}")
    return source


def _copy_bounded(source: Path, target: Path, limit: int) -> bytes:
    digest = hashlib.sha256()
    length = 0
    descriptor = _regular_input(source)
    with os.fdopen(descriptor, "rb") as original, target.open("xb") as captured:
        while chunk := original.read(_CHUNK_BYTES):
            length += len(chunk)
            if length > limit:
                raise ValueError(f"proof input exceeds {limit} bytes: {source}")
            captured.write(chunk)
            digest.update(chunk)
    return digest.digest()


def _bounded_digest(path: Path, limit: int) -> bytes:
    digest = hashlib.sha256()
    length = 0
    descriptor = _regular_input(path)
    with os.fdopen(descriptor, "rb") as source:
        while chunk := source.read(_CHUNK_BYTES):
            length += len(chunk)
            if length > limit:
                raise ValueError("proof input snapshot changed during native verification")
            digest.update(chunk)
    return digest.digest()


@contextmanager
def proof_inputs_snapshot(proof: Path, statement: Path | None = None,
                          *, statement_limit: int = MAX_STATEMENT_BYTES) -> Iterator[tuple[Path, Path]]:
    """Yield private, size-bounded bytes used for exactly one native verify call.

    A single-proof verifier enters before package admission so admission cannot
    race a change to the caller's original paths. A fold-chain audit may
    capture each checkpoint later, authenticating that captured checkpoint.
    Print native success only after this context exits successfully.
    """
    if not 0 < statement_limit <= MAX_STATEMENT_BYTES:
        raise ValueError("invalid proof statement size limit")
    proof_path = Path(os.path.abspath(proof))
    statement_path = (Path(os.path.abspath(statement)) if statement is not None
                      else Path(str(proof_path) + ".statement.json"))
    with tempfile.TemporaryDirectory(prefix="s31-proof-inputs-") as temporary:
        captured_proof = Path(temporary) / "proof.bin"
        captured_statement = Path(temporary) / "statement.json"
        proof_digest = _copy_bounded(proof_path, captured_proof, MAX_PROOF_BYTES)
        statement_digest = _copy_bounded(statement_path, captured_statement, statement_limit)
        yield captured_proof, captured_statement
        if (_bounded_digest(captured_proof, MAX_PROOF_BYTES) != proof_digest or
                _bounded_digest(captured_statement, statement_limit) != statement_digest):
            raise ValueError("proof input snapshot changed during native verification")
