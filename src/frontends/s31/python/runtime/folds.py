"""Check recursive fold checkpoint proofs and claim continuity."""

from __future__ import annotations

import json
from pathlib import Path

from package.context import invoke


def replay_state_step(previous: list[int], body: list[dict]) -> list[int]:
    """Independent scalar M31 replay of a sealed four-lane fold transition."""
    p = (1 << 31) - 1
    if len(previous) != 4 or any(type(word) is not int or not 0 <= word < p for word in previous):
        raise ValueError("invalid state-fold checkpoint state")
    values = previous.copy()
    for operation in body:
        op = operation.get("op")
        constant = operation.get("constant")
        if op == "square" and constant is None:
            values = [(value * value) % p for value in values]
        elif op in {"add_const", "mul_const"} and type(constant) is int and 0 <= constant < p:
            values = [((value + constant) if op == "add_const" else (value * constant)) % p
                      for value in values]
        elif op == "mix4" and constant is None:
            total = sum(values) % p
            values = [(value + total) % p for value in values]
        else:
            raise ValueError("unsupported sealed state-fold step operation")
    return values


def audit_fold_chain(package: Path, manifest: dict, proofs: list[Path], state: bool,
                     max_step: int | None) -> dict:
    """Verify every checkpoint and replay its public claim continuity."""
    if not proofs:
        raise ValueError("a fold chain needs at least one proof")
    if max_step is not None and not (0 <= max_step <= 0xffffffff):
        raise ValueError("--max-step must fit u32")
    if len(proofs) - 1 > 0xffffffff or (max_step is not None and len(proofs) - 1 > max_step):
        raise ValueError("fold chain exceeds the locally trusted depth")
    wide = manifest["lowering"] == "sparse-wide-gate"
    if state and (manifest["lowering"] != "gate" or
                  "state-fold-verification-key.json" not in manifest["artifacts"]):
        raise ValueError("state-fold chain requires a supported gate recurrence package")
    if not state and manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
        raise ValueError("fixed-fold chain requires a gate or sparse-wide package")
    expected_schema = ("s31-state-fold-statement-v2" if state else
                       "s31-fixed-fold-statement-v4" if wide else "s31-fixed-fold-statement-v3")
    key_field = "state_fold_key_sha256" if state else "fold_key_sha256"
    native_command = "state-fold-verify" if state else "fold-verify"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    body = None
    if state:
        key = json.loads((package / "state-fold-verification-key.json").read_text())
        body = key["step_body"]
    previous = None
    for index, raw_proof in enumerate(proofs):
        proof = raw_proof.resolve()
        statement_path = Path(str(proof) + ".statement.json")
        item = json.loads(statement_path.read_text())
        if item.get("schema") != expected_schema or type(item.get("step")) is not int or item["step"] != index:
            raise ValueError(f"fold checkpoint must have contiguous step {index}: {proof}")
        if previous is not None:
            for field in (key_field, "fold_preprocessed_root", "fold_circuit_hash",
                          "leaf_public_words", "base_public_words"):
                if item[field] != previous[field]:
                    raise ValueError(f"fold checkpoint changed {field} at step {index}")
        if state:
            if item["initial_state"] != item["leaf_public_words"][4:8]:
                raise ValueError("state-fold initial state differs from leaf output")
            if index == 0:
                if item["current_state"] != item["initial_state"]:
                    raise ValueError("state-fold base current state differs from initial state")
            elif (item["initial_state"] != previous["initial_state"] or
                  item["current_state"] != replay_state_step(previous["current_state"], body)):
                raise ValueError(f"state-fold transition mismatch at step {index}")
        invoke(str(verifier), native_command, str(proof), str(statement_path),
               *(("--max-step", str(max_step)) if max_step is not None else ()))
        previous = item
    result = {
        "schema": "s31-fold-chain-audit-v1",
        "kind": "state" if state else "fixed",
        "proofs_verified": len(proofs),
        "top_step": len(proofs) - 1,
        "leaf_public_words": previous["leaf_public_words"],
        "base_public_words": previous["base_public_words"],
        "fold_preprocessed_root": previous["fold_preprocessed_root"],
    }
    if state:
        result["initial_state"] = previous["initial_state"]
        result["current_state"] = previous["current_state"]
    return result
