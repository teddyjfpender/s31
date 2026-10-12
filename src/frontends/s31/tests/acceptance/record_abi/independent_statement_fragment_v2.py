"""Independent source-to-public-claim check for the bounded record fragment.

This deliberately imports only the independent source parser, not the S31
compiler, ABI codec, relation validator, or proof verifier. Its capability is
limited to the M31 single-word record grammar in record_source_fragment.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any

from package.record_source_fragment import parse_record_source_fragment

CAPABILITY = "source-to-statement-projection-only"
M31_MODULUS = 2**31 - 1
MAX_STATEMENT_BYTES = 1_000_000
ABI_DOMAIN = b"s31-public-record-boundary-v2\0"


class InvalidRecordStatementFragment(ValueError):
    """Statement bytes differ from the source-derived v2 public claim."""


def _canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise InvalidRecordStatementFragment("duplicate JSON key")
        result[key] = value
    return result


def _invalid_constant(value: str) -> None:
    raise InvalidRecordStatementFragment(f"invalid JSON constant: {value}")


def _parse_statement(encoded: bytes) -> dict[str, Any]:
    if type(encoded) is not bytes or not 0 < len(encoded) <= MAX_STATEMENT_BYTES:
        raise InvalidRecordStatementFragment("invalid statement byte size")
    try:
        statement = json.loads(encoded, object_pairs_hook=_unique_object,
                               parse_constant=_invalid_constant)
        if encoded != _canonical(statement):
            raise InvalidRecordStatementFragment("noncanonical statement bytes")
    except InvalidRecordStatementFragment:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError,
            OverflowError, RecursionError, TypeError) as exc:
        raise InvalidRecordStatementFragment("invalid statement JSON") from exc
    if type(statement) is not dict or set(statement) != {"version", "abi_sha256", "leaves"}:
        raise InvalidRecordStatementFragment("invalid statement envelope")
    if type(statement["version"]) is not int or statement["version"] != 2:
        raise InvalidRecordStatementFragment("invalid statement version")
    if type(statement["leaves"]) is not list:
        raise InvalidRecordStatementFragment("invalid statement leaves")
    return statement


def check_record_source_statement(source_bytes: bytes, statement_bytes: bytes) -> dict[str, Any]:
    """Derive the final eight public words from exact source and claim bytes.

    A successful check establishes ABI parsing and projection only. It does
    not establish that a proof authenticates those words or that the claimed
    values satisfy the source computation.
    """
    relation = parse_record_source_fragment(source_bytes)
    boundary = relation["public_abi"]
    digest = hashlib.sha256(ABI_DOMAIN + _canonical(boundary)).hexdigest()
    statement = _parse_statement(statement_bytes)
    if type(statement["abi_sha256"]) is not str or statement["abi_sha256"] != digest:
        raise InvalidRecordStatementFragment("statement ABI digest differs from source")

    expected = [leaf for root in boundary["inputs"] if root["visibility"] == "public"
                for leaf in root["leaves"]] + boundary["result"]["leaves"]
    claims = statement["leaves"]
    if len(claims) != len(expected):
        raise InvalidRecordStatementFragment("statement leaf count differs from source")
    wire_values: dict[str, int] = {}
    for declared, actual in zip(expected, claims):
        if (type(actual) is not dict or set(actual) != {"path", "words"} or
                actual["path"] != declared["path"]):
            raise InvalidRecordStatementFragment("statement leaf path differs from source")
        words = actual["words"]
        if (type(words) is not list or len(words) != 1 or
                type(words[0]) is not int or not 0 <= words[0] < M31_MODULUS):
            raise InvalidRecordStatementFragment("noncanonical M31 statement word")
        wire = declared["wire"]
        if wire in wire_values and wire_values[wire] != words[0]:
            raise InvalidRecordStatementFragment("aliased public claims disagree")
        wire_values[wire] = words[0]

    words = [wire_values[item["name"]] for item in relation["inputs"]
             if item["visibility"] == "public"]
    words.extend(wire_values[wire] for wire in relation["public_outputs"])
    if not 1 <= len(words) <= 8:
        raise InvalidRecordStatementFragment("public proof-word budget exceeded")
    return {"capability": CAPABILITY,
            "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "statement_sha256": hashlib.sha256(statement_bytes).hexdigest(),
            "abi_sha256": digest,
            "proof_words": words + [0] * (8 - len(words))}
