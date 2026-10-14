#!/usr/bin/env python3
"""P02 gate lookup-budget and public-closure diagnostic; not a certificate.

The sealed package's verifier is executed for check-key, and optionally for a
proof plus a one-claimed-sum mutation. Execute only locally trusted binaries.
Internal hashes do not establish binary provenance or full AIR soundness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_final_domain import ROOT, extract_gate
from src.frontends.s31.python.package.gate_component_roster import FACTS, FIXED_LOGS, NAMES

P = 2147483647
SHIFT = 16
MAX_SHIFTED = 1 << (31 - SHIFT)
NATIVE_SOURCES = {
    "deps/stwo-zig/src/frontends/circuit/common/component_list.zig":
        "d2f1e8facad581464f365958fb8e9fb9270fb28c09363b8361898df4136ceb2b",
    "deps/stwo-zig/src/frontends/circuit/witness/trace.zig":
        "3ca09043577c5f3aeb2df0a9110ad5228fe0941fcfe46cbd69b41044d0455bdb",
    "deps/stwo-zig/src/frontends/circuit/stark_verifier/verify.zig":
        "53d0b3c5e0d902a579cf1305d70ca34914666cac48ba1598f3c256e686d8ecc0",
    "src/frontends/s31/runtime/native_verifier.zig":
        "42c33c4823679ac9ea5ffd2d4968a3344457d67783188153a02fcbac115b4ffc",
    "src/frontends/s31/runtime/pcs_mode_binding.zig":
        "db61e2e740ee890a92460db1a5545b7f14d1353c15fcd944a4a760867255e0b4",
}


def check_sources(root: Path) -> dict[str, str]:
    digests = {}
    for name, expected in NATIVE_SOURCES.items():
        actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"native gate interaction source changed: {name}")
        digests[name] = actual
    return digests


def derive_budget(roster: dict, geometry: dict) -> list[dict]:
    """Replay `checkRelationUses`'s shifted bound, plus exact integer uses."""
    components = roster.get("components")
    if not isinstance(components, list) or len(components) != len(FACTS):
        raise ValueError("gate component roster is incomplete")
    if len(geometry.get("components", [])) != len(FACTS):
        raise ValueError("gate geometry is incomplete")
    totals: dict[str, dict[str, int]] = {}
    for index, (component, parsed) in enumerate(zip(components, geometry["components"], strict=True)):
        base, interaction, source, uses = FACTS[index]
        if (component.get("name") != NAMES[index] or
                component.get("proof_index") != index or
                component.get("claimed_sum_index") != index or
                component.get("base_trace_columns") != base or
                component.get("interaction_trace_columns") != interaction or
                component.get("log_size_source") != source or
                component.get("lookup_uses_per_row") != [
                    {"relation_id": relation, "uses": count}
                    for relation, count in uses] or
                (index in FIXED_LOGS and
                 component.get("trace_log_size") != FIXED_LOGS[index]) or
                parsed.get("trace_log_size") != component.get("trace_log_size") or
                parsed.get("name") != NAMES[index]):
            raise ValueError("gate relation facts differ from reviewed AIR")
        log = component["trace_log_size"]
        if type(log) is not int or not 0 <= log <= 30:
            raise ValueError("invalid gate component height")
        rows = 1 << log
        shifted_rows_plus_one = (rows >> SHIFT) + 1
        for relation, count in uses:
            totals.setdefault(relation, {"exact_uses": 0, "shifted_bound": 0})
            totals[relation]["exact_uses"] += rows * count
            totals[relation]["shifted_bound"] += shifted_rows_plus_one * count
    result = []
    for relation, values in sorted(totals.items()):
        exact, shifted = values["exact_uses"], values["shifted_bound"]
        if shifted >= MAX_SHIFTED or exact >= P or exact > (1 << SHIFT) * shifted:
            raise ValueError(f"gate relation use bound exceeds M31: {relation}")
        result.append({"relation": relation, "exact_uses": exact,
                       "native_shifted_bound": shifted,
                       "native_shifted_bound_limit": MAX_SHIFTED,
                       "canonical_m31_use_count": exact < P})
    if len(result) != 8:
        raise ValueError("gate relation set changed")
    return result


def verify_claim_mutation(package: Path, proof: Path, statement: Path) -> dict:
    manifest = json.loads((package / "manifest.json").read_text())
    binary = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key = package / "verification-key.json"
    args = [str(binary), str(proof), str(statement), str(key)]
    accepted = subprocess.run(args, capture_output=True, text=True, timeout=90, check=False)
    if accepted.returncode:
        raise ValueError(f"native gate proof rejected: {accepted.stderr.strip()[:200]}")
    raw = proof.read_bytes()
    prefix = b"S31NAT1\x00"
    offset = len(prefix) + 8
    if len(raw) < offset + 11 * 16 or raw[:len(prefix)] != prefix:
        raise ValueError("not a complete legacy gate proof header")
    with tempfile.TemporaryDirectory(prefix="s31-p02-claim-") as directory:
        adversarial = Path(directory) / "changed-claim.proof"
        for slot in range(11):
            limb_offset = offset + 16 * slot
            old = int.from_bytes(raw[limb_offset:limb_offset + 4], "little")
            if old >= P:
                raise ValueError("noncanonical gate claimed sum")
            mutated = bytearray(raw)
            mutated[limb_offset:limb_offset + 4] = ((old + 1) % P).to_bytes(4, "little")
            adversarial.write_bytes(mutated)
            rejected = subprocess.run([str(binary), str(adversarial), str(statement), str(key)],
                                      capture_output=True, text=True, timeout=90, check=False)
            if rejected.returncode == 0 or "InvalidLookupSum" not in rejected.stderr:
                raise ValueError(f"native gate verifier failed to reject changed lookup claim {slot}")
    return {"original_proof": "accepted", "changed_claims": "rejected_InvalidLookupSum",
            "claimed_sum_slots_mutated": 11,
            "proof_sha256": hashlib.sha256(raw).hexdigest(),
            "statement_sha256": hashlib.sha256(statement.read_bytes()).hexdigest(),
            "verifier_sha256": hashlib.sha256(binary.read_bytes()).hexdigest()}


def extract_interaction(package: Path, root: Path = ROOT,
                        proof: Path | None = None,
                        statement: Path | None = None) -> dict:
    if (proof is None) != (statement is None):
        raise ValueError("proof and public statement must be supplied together")
    geometry = extract_gate(package, root)
    sources = check_sources(root)
    roster = json.loads((package / "gate-component-roster.json").read_text())
    budget = derive_budget(roster, geometry)
    report = {
        "schema": "s31-gate-interaction-p02-v1",
        "status": "conditional_native_gate_interaction_slice",
        "p02_complete": False,
        "proven_release_admissible": False,
        "native_proven_security_bits": None,
        "proof_package_manifest_sha256": geometry["package_checks"]["package_manifest_sha256"],
        "verification_key_sha256": geometry["package_checks"]["verification_key_sha256"],
        "engine_gitlink": geometry["source_binding"]["engine_gitlink"],
        "source_sha256": sources,
        "component_claims": len(roster["components"]),
        "public_gate_terms": 9,
        "public_gate_addresses": list(range(3, 11)) + [2],
        "relation_use_bounds": budget,
        "proof_control": None,
        "remaining_premises": [
            "installed verifier binary corresponds to pinned source and reaches successful proof verification",
            "all committed base and interaction columns realize the modeled per-row AIR relations",
            "all lookup denominators avoid poles or their exceptional event is budgeted",
            "all components, including table multiplicities, satisfy the global authenticated LogUp relation",
            "the native transcript and PCS/FRI satisfy the published IOP and cryptographic reductions",
        ],
    }
    if proof is not None:
        report["proof_control"] = verify_claim_mutation(package, proof, statement)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--statement", type=Path)
    parser.add_argument("--require-p02", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = extract_interaction(args.package.resolve(), proof=args.proof, statement=args.statement)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"PCS/FRI gate interaction rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_p02 else 0


if __name__ == "__main__":
    raise SystemExit(main())
