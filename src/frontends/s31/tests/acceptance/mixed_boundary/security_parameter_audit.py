#!/usr/bin/env python3
"""Diagnostic, source-pinned parameter audit for the closed mixed N1–N8 profile.

This checks a reviewed source snapshot and reports one conditional algebraic
lookup bound. It does not establish whole-proof STARK soundness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Mapping


ENGINE_REVISION = "041ef9d43d341089d45670bd045de7ddbffc79bb"
SOURCE_SHA256 = {
    "deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig": "9119ff9fe58c343d66e437e6236aa1feca3660fc5d2bdafa3173ad48d0bf888d",
    "deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_schedule.zig": "55c4aeec92520828c173640335688bb9b7837fafd7bea7ff1dfb50150b50a326",
    "deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig": "3c5b2b6c3996a5a1886f4fc57d92082f7eb91578df0b63f9f585fd45acc2899c",
    "deps/stwo-zig/src/core/pcs/config_v2.zig": "b58f464074d5c8ca5e002764e529afc9f3e1fe81f12320a180fc1f850ef05178",
    "deps/stwo-zig/src/core/pcs/verifier.zig": "e119335172e17db5fd1345f476c7f6ad7fdf67e394a5b18d5c2085e892ffe3d5",
    "deps/stwo-zig/src/core/fri.zig": "faf714cff9965603535b747f8abad63b1e6dc55699b331e5cab0716ddf50de8e",
    "deps/stwo-zig/src/core/fri/config.zig": "de08fde01ea6e6b871ca41d63627be765d00a8dfe607e8c2c58194eec8d9359a",
    "deps/stwo-zig/src/core/queries.zig": "68e13fbb48c0cd684b94198c5452e003984237a2fe2000dd332ac57234328bce",
    "deps/stwo-zig/src/core/channel/blake2s.zig": "407a80a913acb15b7e0138a593f1d2636f4297969714932cce59ed928e29f575",
    "deps/stwo-zig/src/core/channel/lookup_transcript.zig": "3180e2d704a07547a1df3a4c2da3b2dc675b7e18fb8715e39d889f8ddc9bc991",
    "deps/stwo-zig/src/prover/air/logup_columns.zig": "a4bc2efa8ba1a29c959b4d6b2f279a5032dde1ff7b8354675e87e02b4ebc4469",
    "deps/stwo-zig/src/frontends/circuit/common/component_list.zig": "d2f1e8facad581464f365958fb8e9fb9270fb28c09363b8361898df4136ceb2b",
    "src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig": "9c9547a7265e18a6330b3342b6e5763d7b68fbe341dd4f6c8968921e21b02bc6",
    "src/frontends/s31/runtime/mixed_boundary/inspection.zig": "ec1106af5a075aee5fa53d434beb2f9e62f7a9fffb4792f8ba3a1b17757d0ba9",
    "src/frontends/s31/runtime/mixed_boundary/registry_manifest.zig": "67c3f6c6ebfe3b9f1133b9c15d94680759c67072fc80b02b97be39d5660a6e5a",
    "src/frontends/s31/runtime/mixed_boundary/general_package.zig": "9cf45bc4a34ae27a60e68942e8e745c3033e693dbb5a4fd3b2480c48631dd11c",
    "src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig": "5e7e6eb0e963d7106c1ef973d7e50b539dfc772d4b4f1cff227bf0e65bed9f26",
    "src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig": "f2e34b432be5ec28661da6d104486dde93790ca39164d56c317c4a0a33a21ac9",
}


class AuditError(ValueError):
    """A source or policy mismatch; no error bound may be reported."""


def _section(text: str, start: str, end: str, code: str) -> str:
    try:
        a = text.index(start)
        b = text.index(end, a + len(start))
    except ValueError as exc:
        raise AuditError(f"{code}: missing source section") from exc
    return text[a:b]


def _ordered(text: str, anchors: tuple[str, ...], code: str) -> None:
    at = 0
    for anchor in anchors:
        found = text.find(anchor, at)
        if found < 0:
            raise AuditError(f"{code}: absent or reordered: {anchor}")
        at = found + len(anchor)


def _constant(text: str, name: str, expected: int) -> int:
    match = re.search(rf"\bpub const {re.escape(name)}:\s*\w+\s*=\s*(1\s*<<\s*\d+|\d+)\s*;", text)
    if match is None:
        raise AuditError(f"GEOMETRY: missing {name}")
    value = match.group(1).replace(" ", "")
    parsed = 1 << int(value.split("<<")[1]) if "<<" in value else int(value)
    if parsed != expected:
        raise AuditError(f"GEOMETRY: {name}={parsed}, expected {expected}")
    return parsed


def audit(repo_root: Path, overrides: Mapping[str, bytes] | None = None) -> dict[str, object]:
    """Audit pinned sources; overrides are for isolated mutation tests only."""
    root = repo_root.resolve()
    override = overrides or {}
    sources: dict[str, bytes] = {}
    for path in SOURCE_SHA256:
        try:
            sources[path] = override[path] if path in override else (root / path).read_bytes()
        except OSError as exc:
            raise AuditError(f"SOURCE_MISSING: {path}: {exc}") from exc
    decoded = {path: data.decode("utf-8") for path, data in sources.items()}

    preflight = decoded["deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig"]
    fixed_pcs = _section(preflight, "pub fn fixedPcs(", "pub fn inspect(", "PCS_CONFIG")
    match = re.search(r"FriConfigV2\.init\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)", fixed_pcs)
    if match is None or tuple(map(int, match.groups())) != (26, 0, 1, 70, 1):
        raise AuditError("PCS_CONFIG: expected fixed (26,0,1,70,1) profile")
    schedule = decoded["deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_schedule.zig"]
    if "const pcs = try v4.fixedPcs(plan, pp.traceLogSize());" not in schedule:
        raise AuditError("PCS_CONFIG: mixed schedule no longer calls fixedPcs")
    package = decoded["src/frontends/s31/runtime/mixed_boundary/general_package.zig"]
    if "const pcs = geometry.pcs;" not in package or "postcard.proof_preflight.validateFor(4, raw[at..]" not in package:
        raise AuditError("PCS_CONFIG: package preflight not pinned to source geometry")
    entry = decoded["src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig"]
    if (
        'const source = @embedFile("s31_program_source");' not in entry
        or 'const air = @embedFile("s31_air_programs");' not in entry
        or entry.count("package.verifyEmbeddedAndInspect(source, air,") != 2
    ):
        raise AuditError("SOURCE_ENTRY: verifier no longer uses embedded source/AIR package entrypoint")
    prover_entry = decoded["src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig"]
    if (
        'const source = @embedFile("s31_program_source");' not in prover_entry
        or 'const air = @embedFile("s31_air_programs");' not in prover_entry
        or "package.proveSealedAndInspectWithTiming(" not in prover_entry
    ):
        raise AuditError("SOURCE_ENTRY: prover no longer uses embedded source/AIR package entrypoint")

    logup = decoded["deps/stwo-zig/src/prover/air/logup_columns.zig"]
    fill_chunk = _section(logup, "fn fillChunk(self: *Worker", "fn inclusivePrefixSum(", "DENOMINATOR_POLICY")
    _ordered(fill_chunk, (
        "try fillRow(shared.context, first_row + offset, row_fractions);",
        "if (fraction.denominator.isZero()) return error.DegenerateDenominator;",
        "try fields.batchInverseInPlace(QM31, self.denominators, self.inverses);",
    ), "DENOMINATOR_POLICY")

    mixed = decoded["deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig"]
    prover = _section(mixed, "pub fn proveSourceBoundWithTiming(", "fn collectFriPowStage(", "ORDER_PROVER")
    verifier = _section(mixed, "pub fn verifySourceBoundBorrowed(", "pub fn auditVerifiedSourceBoundWitness(", "ORDER_VERIFY")
    prefix = (
        "mixProfile(&channel, selected);",
        "core.channel.lookup_transcript.mixChannelSalt(&channel, 0);",
        "pcs.fri_config.mixInto(&channel);",
    )
    _ordered(prover, prefix + (
        "try commit(&scheme, allocator, &pp_views, &channel);",
        "MC.mixRoot(&channel, identity);",
        "channel.mixFelts(base.output_values);",
        "try commit(&scheme, allocator, main_views[0..main_width], &channel);",
        "channel.grind(circuit.common.component_list.INTERACTION_POW_BITS);",
        "channel.mixU64(nonce);",
        "core.channel.lookup_transcript.drawLookupElements(allocator, &channel);",
        "core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..selected.geometry.slot_count]);",
        "try commit(&scheme, allocator, interaction_views[0..interaction_width], &channel);",
    ), "ORDER_PROVER")
    _ordered(verifier, prefix + (
        "try scheme.commit(allocator, roots[0], &pp_logs, &channel);",
        "MC.mixRoot(&channel, identity);",
        "channel.mixFelts(&outputs);",
        "try scheme.commit(allocator, roots[1], main_logs[0..main_width], &channel);",
        "channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, proof.interaction_pow_nonce)",
        "channel.mixU64(proof.interaction_pow_nonce);",
        "core.channel.lookup_transcript.drawLookupElements(allocator, &channel);",
        "core.channel.lookup_transcript.mixInteractionClaim(&channel, proof.claimed_sums[0..selected.geometry.slot_count]);",
        "try scheme.commit(allocator, roots[2], interaction_logs[0..interaction_width], &channel);",
    ), "ORDER_VERIFY")
    pcs_verifier = decoded["deps/stwo-zig/src/core/pcs/verifier.zig"]
    _ordered(pcs_verifier, (
        "channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)",
        "channel.mixU64(proof.proof_of_work);",
        "fri_verifier.sampleQueryPositionsWithRaw(",
    ), "ORDER_FRI_QUERY")
    component_list = decoded["deps/stwo-zig/src/frontends/circuit/common/component_list.zig"]
    if "pub const INTERACTION_POW_BITS: u32 = 20;" not in component_list:
        raise AuditError("INTERACTION_POW: expected 20 bits")

    geometry = decoded["src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig"]
    calls = _constant(geometry, "max_calls", 8)
    rows = _constant(geometry, "max_circuit_rows", 1 << 16)
    rounds = _constant(geometry, "max_chip_rounds", 1 << 18)
    outputs = _constant(geometry, "public_output_addresses", 9)
    bridge_rows = _constant(geometry, "bridge_rows", 16)
    events = 3 * rows + 2 * rounds + 10 * bridge_rows * calls + outputs
    weight = 16 * (4 * rows + 8 * calls + 2 * outputs + 2 * rounds) + 10 * bridge_rows * calls
    p = (1 << 31) - 1
    if weight >= p:
        raise AuditError("GEOMETRY: integerized multiplicity reaches field characteristic")
    numerator = 7 * events - 6

    for path, expected in SOURCE_SHA256.items():
        actual = hashlib.sha256(sources[path]).hexdigest()
        if actual != expected:
            raise AuditError(f"SOURCE_DIGEST: {path}: expected {expected}, got {actual}")
    try:
        gitlink = subprocess.check_output(
            ["git", "-C", str(root), "ls-tree", "HEAD", "deps/stwo-zig"],
            text=True, stderr=subprocess.PIPE,
        ).strip()
        revision = subprocess.check_output(
            ["git", "-C", str(root / "deps/stwo-zig"), "rev-parse", "HEAD"],
            text=True, stderr=subprocess.PIPE,
        ).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(root / "deps/stwo-zig"), "status", "--porcelain", "--untracked-files=all"],
            text=True, stderr=subprocess.PIPE,
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise AuditError(f"ENGINE_REVISION: cannot inspect stwo-zig: {exc}") from exc
    if gitlink != f"160000 commit {ENGINE_REVISION}\tdeps/stwo-zig" or revision != ENGINE_REVISION or dirty:
        raise AuditError("ENGINE_REVISION: superproject gitlink, submodule HEAD or clean worktree differs from reviewed revision")

    return {
        "schema": "s31-mixed-conditional-security-parameters-v1",
        "engine_revision": revision,
        "call_range": [1, calls],
        "fri": {"pow_bits": 26, "log_last_layer_degree_bound": 0,
                "log_blowup_factor": 1, "n_queries_raw": 70, "fold_step": 1},
        "interaction_pow_bits": 20,
        "lookup": {"event_occurrences_max": events,
                   "integerized_absolute_weight_max": weight,
                   "field_order": p**4,
                   "conditional_numerator": numerator,
                   "conditional_bound": f"{numerator}/((2^31-1)^4)",
                   "attacker_attempt_factor": "Q_L valid transcript continuations"},
        "whole_proof_security_bits": None,
        "unbounded_terms": ["AIR composition", "OODS", "FRI/PCS", "Merkle binding",
                            "Fiat-Shamir/adaptive nonce trials", "transcript domain separation"],
    }


def _default_root() -> Path:
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "deps/stwo-zig").exists() and (candidate / "src/frontends/s31").exists():
            return candidate
    raise AuditError("REPO_ROOT: could not locate S31 source tree")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, help="S31 repository root")
    parser.add_argument("--json", action="store_true", help="print canonical JSON")
    args = parser.parse_args(argv)
    try:
        result = audit(args.repo_root or _default_root())
    except AuditError as exc:
        print(f"security parameter audit refused: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("Pinned mixed N1–N8 profile: PASS")
        print("Conditional lookup bound:", result["lookup"]["conditional_bound"])
        print("Whole-proof security bits: UNBOUNDED (AIR/FRI/PCS/Fiat–Shamir proof absent)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
