"""Validate V7's saved positive and changed public-statement controls."""

from __future__ import annotations

import copy
import json
import re
from pathlib import Path

from abi.binding_v2 import (decode_typed_public_statement,
                            flat_assignment_from_typed, statement_from_assignment)
from package.context import abi


FLAT_FIELD = re.compile(r"(public_inputs|public_outputs)\.([A-Za-z_][A-Za-z0-9_]*)\[0\]\Z")
RECORD_FIELD = re.compile(r"leaves\[([0-9]+)\]\.words\[([0-9]+)\]\Z")


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError("duplicate public statement JSON key")
        result[name] = value
    return result


def _flat_statement(source: dict, encoded: bytes) -> dict:
    statement = json.loads(encoded, object_pairs_hook=_unique_object)
    layout = abi(source, "direct-gate")
    if type(statement) is not dict or set(statement) != {"public_inputs", "public_outputs"}:
        raise ValueError("public statement has wrong top-level fields")
    for category in ("public_inputs", "public_outputs"):
        fields = layout[category]
        values = statement[category]
        if type(values) is not dict or set(values) != {field["name"] for field in fields}:
            raise ValueError("public statement fields differ from sealed ABI")
        for field in fields:
            words = values[field["name"]]
            bound = 65536 if field["kind"] == "u16" else (1 << 31) - 1
            if (type(words) is not list or len(words) != field["length"] or
                    any(type(word) is not int or word < 0 or word >= bound for word in words)):
                raise ValueError("public statement has noncanonical ABI words or shape")
    return statement


def check_trial_statement(source: dict, assignment: dict, directory: Path,
                          changed_field: str) -> None:
    """Require a valid changed *claim*, so parser rejection cannot pass the control."""
    original_bytes = (directory / "statement.json").read_bytes()
    changed_bytes = (directory / "changed-statement.json").read_bytes()
    if source["version"] == 1:
        original = _flat_statement(source, original_bytes)
        changed = _flat_statement(source, changed_bytes)
        expected_original = {key: assignment[key] for key in ("public_inputs", "public_outputs")}
        if original != expected_original:
            raise ValueError("saved public statement differs from assignment")
        match = FLAT_FIELD.fullmatch(changed_field)
        if match is None:
            raise ValueError("changed public field is not canonical")
        category, name = match.groups()
        try:
            before = original[category][name][0]
            after = changed[category][name][0]
        except (KeyError, IndexError, TypeError) as error:
            raise ValueError("changed public field is missing") from error
        expected = copy.deepcopy(original)
        expected[category][name][0] = after
        descriptor = next(field for field in abi(source, "direct-gate")[category]
                          if field["name"] == name)
        bound = 65536 if descriptor["kind"] == "u16" else (1 << 31) - 1
    elif source["version"] == 2:
        decode_typed_public_statement(source, original_bytes)
        decode_typed_public_statement(source, changed_bytes)
        flat = (flat_assignment_from_typed(
            source, json.dumps(assignment, sort_keys=True, separators=(",", ":")).encode())
            if assignment.get("version") == 2 else assignment)
        if original_bytes != statement_from_assignment(source, flat):
            raise ValueError("saved record statement differs from assignment")
        match = RECORD_FIELD.fullmatch(changed_field)
        if match is None:
            raise ValueError("changed record leaf is not canonical")
        leaf, word = map(int, match.groups())
        original = json.loads(original_bytes)
        changed = json.loads(changed_bytes)
        try:
            before = original["leaves"][leaf]["words"][word]
            after = changed["leaves"][leaf]["words"][word]
        except (KeyError, IndexError, TypeError) as error:
            raise ValueError("changed record leaf is missing") from error
        expected = copy.deepcopy(original)
        expected["leaves"][leaf]["words"][word] = after
        bound = (1 << 31) - 1
    else:
        raise ValueError("unsupported V7 public statement version")
    if before == after or expected != changed:
        raise ValueError("changed public statement modifies the wrong fields")
    if after != (before + 1) % bound:
        raise ValueError("changed public statement differs from frozen trial mutation")
