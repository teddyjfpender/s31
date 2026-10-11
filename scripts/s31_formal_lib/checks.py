"""Exact source/theorem inventories and fail-closed S31 proof checks."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Callable

APPROVED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REUSED = (
    "formal/riscv-refinement/RiscvRefinement/Field/M31.lean",
    "formal/riscv-refinement/RiscvRefinement/Recursion/CompactPoseidon.lean",
)
# Lean's source-range audit also sees a Prop-valued instance and Mathlib's
# generated extensionality iff theorem. Proof-field projections belong in the
# source-aware roster below, never in this name-only derived declaration list.
DERIVED_THEOREMS = {
    "formal/s31/S31/Gadgets/Field.lean": ("S31.Field.instFactPrimeOfNatNat_s31",),
    "formal/s31/S31/Gadgets/Packed.lean": ("S31.Gadgets.Packed.Quad.ext_iff",),
}
# Versioned, reviewed roster of Lean-generated theorem projections for proof
# fields. Each entry binds a kernel declaration to a concrete source structure
# and field. Unknown generated theorems still fail the exact live audit; a
# removed or renamed source field fails inventory generation. These reviewed fields
# are separate from explicit `theorem` declarations and the two non-field
# derived declarations above.
PROOF_FIELD_PROJECTIONS_V1 = {
    REUSED[0]: {
        "RiscvRefinement.M31": ("isLt",),
    },
    "formal/s31/S31/Gadgets/Functional/SSATextBytes.lean": {
        "S31.Functional.SSATextBytes.Parsed": ("checked",),
    },
    "formal/s31/S31/Gadgets/Functional/SSAPublicInputBinding.lean": {
        "S31.Functional.SSAPublicInputBinding.InputBoundary": (
            "zero", "copies", "pins", "basis1", "basis2", "basis3", "packMuls", "packAdds",
        ),
    },
    "formal/s31/S31/Gadgets/Air/TaggedPairSourceComposition.lean": {
        "S31.Gadgets.Air.TaggedPairSourceComposition.ChipRows": (
            "bitReverseInvolutive", "rowCountNonzero", "arithmeticAccepted", "interactionAccepted",
        ),
        "S31.Gadgets.Air.TaggedPairSourceComposition.BridgeRows": (
            "sixteenNonzero", "mainAccepted", "interactionAccepted", "nonzeroD0", "nonzeroD1",
            "nonzeroFirst", "nonzeroLast",
        ),
    },
    "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean": {
        "S31.Functional.RecordAbiV2.WordBlock": ("exactWidth",),
        "S31.Functional.RecordAbiV2.ValidatedPaths": ("injective",),
        "S31.Functional.RecordAbiV2.TaggedPublicBlock": ("bitWidth", "range"),
    },
    "formal/s31/S31/Gadgets/Functional/SSAInstalledBytecodePublicOutput.lean": {
        "S31.Functional.SSAInstalledBytecodePublicOutput.OutputBoundary": (
            "zero", "maskBasis", "inverseBasis", "masks", "inverses", "copies", "pins",
        ),
    },
    "formal/s31/S31/Gadgets/Air/DirectGateOodsOpenings.lean": {
        "S31.Gadgets.Air.DirectGateOodsOpenings.Shape": (
            "fixed", "main", "interactionFirst", "interactionLast",
        ),
    },
    "formal/s31/S31/Gadgets/Air/DirectGatePcsOpeningLink.lean": {
        "S31.Gadgets.Air.DirectGatePcsOpeningLink.PcsOpeningAssumption": (
            "bound", "fixed", "main", "interactionFirst", "interactionLast", "composition",
        ),
    },
    "formal/s31/S31/Gadgets/Functional/Correspondence/RawGateSoundness.lean": {
        "S31.Functional.Correspondence.RawGateSoundness.PhysicalTraceContext": (
            "partition", "fixed", "arithmetic", "unique", "zero", "basis1", "basis2",
            "basis3", "maskBasis", "inverseBasis", "inputPins", "outputPins",
        ),
        "S31.Functional.Correspondence.RawGateSoundness.FixedTraceContext": ("relation",),
    },
    "formal/s31/S31/Gadgets/Functional/Correspondence/AliasRawGateSoundness.lean": {
        "S31.Functional.Correspondence.AliasRawGateSoundness.AliasFixedTraceContext": (
            "relation",
        ),
    },
    "formal/s31/S31/Gadgets/Air/SourceMixedLookupBound.lean": {
        "S31.Gadgets.Air.SourceMixedLookupBound.SourceShape": (
            "rows", "multiplicity", "baselineUses", "baselineYields", "rounds",
        ),
    },
    "formal/s31/S31/Gadgets/Air/SourceMixedFalseClaimBound.lean": {
        "S31.Gadgets.Air.SourceMixedFalseClaimBound.LocalPublicPath": (
            "addresses", "unique", "first", "constants", "step", "packedInitial",
            "packedFinal", "zero", "add", "mul", "outputs",
        ),
    },
    "formal/s31/S31/Gadgets/Air/SourceMixedAuthenticatedTrace.lean": {
        "S31.Gadgets.Air.SourceMixedAuthenticatedTrace.GateRows": (
            "arithmeticResidual", "use0Nonzero", "use1Nonzero", "yieldNonzero", "pairResidual",
            "yieldResidual",
        ),
        "S31.Gadgets.Air.SourceMixedAuthenticatedTrace.AuthenticatedMixedTrace": (
            "gateRowsEq", "publicWordsEq", "positiveAligned", "negativeAligned",
            "claimFoldZero",
        ),
    },
    "formal/s31/S31/Gadgets/Air/SourceMixedScheduledPublicPath.lean": {
        "S31.Gadgets.Air.SourceMixedScheduledPublicPath.LocalPublicSchedule": (
            "addresses", "unique", "first", "constants", "step", "packedInitial",
            "packedFinal", "zero", "add", "mul", "outputs",
        ),
    },
    "formal/s31/S31/Gadgets/Air/SourceMixedEventAlignment.lean": {
        "S31.Gadgets.Air.SourceMixedEventAlignment.EventProjection": (
            "circuitUses", "circuitYields", "chipInputs", "bridgeFinish",
            "chipOutputs", "bridgeStart",
        ),
    },
}
# Lean also generates proof projections for inherited Prop-valued contexts.
# Require the actual `extends` clause in the reviewed structure header before
# accepting the kernel declaration in the theorem inventory.
INHERITED_PROJECTIONS_V1 = {
    "formal/s31/S31/Gadgets/Functional/Correspondence/RawGateSoundness.lean": {
        "S31.Functional.Correspondence.RawGateSoundness.FixedTraceContext":
            ("PhysicalTraceContext", "toPhysicalTraceContext"),
    },
    "formal/s31/S31/Gadgets/Functional/Correspondence/AliasRawGateSoundness.lean": {
        "S31.Functional.Correspondence.AliasRawGateSoundness.AliasFixedTraceContext":
            ("PhysicalTraceContext", "toPhysicalTraceContext"),
    },
}
CONTROLS = frozenset("S31.Evidence." + name for name in (
    "honest_byte_boundary", "byte_out_of_range", "honest_carry", "honest_borrow",
    "checked_overflow_rejected", "checked_underflow_rejected", "zero_inverse_witness_free",
    "nonboolean_rejected", "illegal_selector_rejected", "signed_positive_overflow",
    "signed_negative_overflow", "signed_subtraction_overflow", "negative_interpretation",
    "honest_division", "wrong_quotient_rejected", "oversized_remainder_rejected",
    "high_product_not_truncated", "terminal_carry_is_necessary", "invalid_exponent_rejected",
    "honest_exponent", "digest_last_word", "honest_field_hash_gate", "forged_field_hash_gate",
    "padding_requires_widths", "private_binding_honest", "private_binding_forged_witness",
    "private_binding_forged_output",
))


class FormalError(RuntimeError):
    """Missing, stale, or invalid formal evidence."""


def scan_source(source: str, label: str, lexer: Callable[[str], str]) -> None:
    for match in re.finditer(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", lexer(source)):
        line = source.count("\n", 0, match.start()) + 1
        raise FormalError(f"{label}:{line}: forbidden proof term {match.group()}")


def theorem_names(source: str, lexer: Callable[[str], str]) -> list[str]:
    """Inventory this package's explicit namespace/section declaration style.

    Compilation and the live Lean metadata audit are authoritative. This
    independent source inventory prevents an omitted root import from hiding
    a theorem from that audit. New unsupported declaration syntax fails closed.
    """
    scopes: list[tuple[str, str]] = []
    names = []
    for line in lexer(source).splitlines():
        if match := re.fullmatch(r"\s*(namespace|section)(?:\s+([\w.]+))?\s*", line):
            scopes.append((match[1], match[2] or ""))
        elif match := re.fullmatch(r"\s*end(?:\s+([\w.]+))?\s*", line):
            if not scopes or (match[1] and match[1] != scopes[-1][1]):
                raise FormalError("unmatched Lean namespace/section")
            scopes.pop()
        elif re.search(r"\btheorem\b", line):
            match = re.match(r"\s*(?:@\[[^\]]+\]\s*)*(?:(private|protected)\s+)?"
                             r"theorem\s+([\w.?!']+)(?=\s|[:({]|$)", line)
            if not match:
                raise FormalError(f"unsupported theorem declaration: {line.strip()}")
            if match[1] != "private":
                namespace = ".".join(name for kind, name in scopes if kind == "namespace")
                names.append(namespace + "." + match[2] if namespace else match[2])
    if scopes:
        raise FormalError("unterminated Lean namespace/section")
    if len(names) != len(set(names)):
        raise FormalError("duplicate theorem declaration")
    return names


def _qualified_structure_headers(lines: list[str], qualified: str, label: str) -> list[int]:
    """Locate a reviewed structure in its actual Lean namespace, not by basename."""
    scopes: list[tuple[str, str]] = []
    headers = []
    for index, line in enumerate(lines):
        if match := re.fullmatch(r"\s*(namespace|section)(?:\s+([\w.]+))?\s*", line):
            scopes.append((match[1], match[2] or ""))
        elif match := re.fullmatch(r"\s*end(?:\s+([\w.]+))?\s*", line):
            if not scopes or (match[1] and match[1] != scopes[-1][1]):
                raise FormalError(f"{label}: unmatched Lean namespace/section")
            scopes.pop()
        elif match := re.match(r"^structure\s+([A-Za-z_][A-Za-z_0-9]*)\b", line):
            namespace = ".".join(name for kind, name in scopes if kind == "namespace")
            if (namespace + "." if namespace else "") + match[1] == qualified:
                headers.append(index)
    if scopes:
        raise FormalError(f"{label}: unterminated Lean namespace/section")
    return headers


def proof_field_projection_names(source: str, label: str,
                                 lexer: Callable[[str], str]) -> list[str]:
    """Bind each reviewed generated theorem to a field in its source structure.

    This is deliberately a small roster, not a wildcard for Lean-generated
    declarations. Parse only code surviving the same nested-comment,
    line-comment and string lexer used for explicit theorem inventory, and
    require the actual enclosing namespace. A
    commented field must not license a hand-written theorem with the expected
    projection name. The live axiom audit checks these names like all other
    theorems and rejects both missing and unexpected declarations.
    """
    names = []
    lines = lexer(source).splitlines()
    for qualified, expected_fields in PROOF_FIELD_PROJECTIONS_V1.get(label, {}).items():
        structure = qualified.rsplit(".", 1)[1]
        headers = _qualified_structure_headers(lines, qualified, label)
        if len(headers) != 1:
            raise FormalError(f"{label}: expected one structure {structure}")
        cursor = headers[0]
        while not re.search(r"\bwhere\b", lines[cursor]):
            cursor += 1
            if cursor >= len(lines) or cursor > headers[0] + 10 or not lines[cursor].strip():
                raise FormalError(f"{label}: missing structure body {structure}")
        fields = set()
        for line in lines[cursor + 1:]:
            if not line.strip():
                continue
            if not line.startswith(" "):
                break
            if match := re.match(r"^  ([A-Za-z_][A-Za-z_0-9]*)\s*:", line):
                if match[1] in fields:
                    raise FormalError(f"{label}: duplicate structure field {structure}.{match[1]}")
                fields.add(match[1])
        if len(expected_fields) != len(set(expected_fields)) or not set(expected_fields) <= fields:
            raise FormalError(f"{label}: stale proof-field projection roster for {structure}")
        names.extend(f"{qualified}.{field}" for field in expected_fields)
    return names


def inherited_projection_names(source: str, label: str,
                               lexer: Callable[[str], str]) -> list[str]:
    """Inventory reviewed `extends` projections from source-bound headers."""
    lines = lexer(source).splitlines()
    names = []
    for qualified, (parent, projection) in INHERITED_PROJECTIONS_V1.get(label, {}).items():
        headers = _qualified_structure_headers(lines, qualified, label)
        if len(headers) != 1:
            raise FormalError(f"{label}: expected one inherited structure {qualified}")
        cursor = headers[0]
        while not re.search(r"\bwhere\b", lines[cursor]):
            cursor += 1
            if cursor >= len(lines) or cursor > headers[0] + 10 or not lines[cursor].strip():
                raise FormalError(f"{label}: missing inherited structure body {qualified}")
        header = " ".join(lines[headers[0]:cursor + 1])
        if not re.search(rf"\bextends\s+{re.escape(parent)}\b.*\bwhere\b", header):
            raise FormalError(f"{label}: stale inherited projection roster for {qualified}")
        if projection != "to" + parent:
            raise FormalError(f"{label}: unexpected inherited projection {projection}")
        names.append(f"{qualified}.{projection}")
    return names


def source_paths(root: Path) -> list[Path]:
    formal = root / "formal/s31"
    required = [formal / "S31.lean", formal / "S31/Semantics/Node.lean",
                formal / "S31/Evidence/NonVacuity.lean", formal / "S31/Evidence/Coverage.lean",
                formal / "S31/Evidence/AxiomAudit.lean", *(root / path for path in REUSED)]
    for path in required:
        if not path.is_file() or path.is_symlink():
            raise FormalError(f"missing regular proof source: {path.relative_to(root)}")
    sources = sorted({formal / "S31.lean", *formal.joinpath("S31").rglob("*.lean"),
                      *(root / path for path in REUSED)})
    if any(not p.is_file() or p.is_symlink() for p in sources):
        raise FormalError("proof source closure contains a non-regular file")
    return sources


def inventory(root: Path, lexer: Callable[[str], str]) -> dict:
    files, declarations = {}, []
    for path in source_paths(root):
        source = path.read_text(encoding="utf-8")
        label = path.relative_to(root).as_posix()
        scan_source(source, label, lexer)
        files[label] = hashlib.sha256(path.read_bytes()).hexdigest()
        declarations.extend(theorem_names(source, lexer))
        declarations.extend(DERIVED_THEOREMS.get(label, ()))
        declarations.extend(proof_field_projection_names(source, label, lexer))
        declarations.extend(inherited_projection_names(source, label, lexer))
    if len(declarations) != len(set(declarations)):
        raise FormalError("duplicate theorem in proof closure")
    if not CONTROLS <= set(declarations):
        raise FormalError("missing required non-vacuity theorem controls")
    return {"schema": "s31-lean-inventory-v1", "files": files, "theorems": sorted(declarations)}


def check_coverage(root: Path, ops: list[str], coverage: dict, theorems: set[str]) -> None:
    if coverage.get("schema") != "s31-operation-coverage-v1":
        raise FormalError("unsupported operation coverage schema")
    if coverage.get("boundary") != "normalized relation IR v1 and local constraint models":
        raise FormalError("operation coverage claim boundary changed")
    if coverage.get("production_compiler_correctness_proved") is not False:
        raise FormalError("coverage cannot claim production compiler correctness")
    entries = coverage.get("operations", [])
    if [row.get("op") for row in entries] != ops or len(ops) != len(set(ops)):
        raise FormalError("operation coverage is not the exact source inventory")
    for row in entries:
        name = row["op"]
        if not row.get("semantics", "").startswith("S31."):
            raise FormalError(f"{name}: missing executable semantics declaration")
        if not row.get("gadget_theorems") or not set(row["gadget_theorems"]) <= theorems:
            raise FormalError(f"{name}: missing or unknown gadget theorem")
        source = root / row["source"]["path"]
        if not source.is_file() or not re.search(
            rf"\bfn\s+{re.escape(row['source']['function'])}\b", source.read_text()):
            raise FormalError(f"{name}: missing production source function")


def render_coverage(coverage: dict) -> str:
    rows = coverage["operations"]
    names = sorted({name for row in rows for name in row["gadget_theorems"]})
    result = "/- Generated by scripts/s31_formal.py from reviewed coverage.json. -/\n"
    result += "import S31.Gadgets\n\n"
    result += "".join(f"#check {name}\n" for name in names)
    result += "\n" + "".join(f"#check {name}\n" for name in sorted({r['semantics'] for r in rows}))
    result += "\nnamespace S31.Evidence\n\n"
    result += "def operationCoverage : List (Op × List String) := [\n"
    result += ",\n".join("  (." + row["op"] + ", " + json.dumps(row["gadget_theorems"]) + ")"
                           for row in rows)
    result += "]\n\n"
    result += "theorem operation_inventory_exact : operationCoverage.map Prod.fst = allOps := rfl\n\n"
    result += "theorem operation_inventory_complete (op : Op) :\n"
    result += "    op ∈ operationCoverage.map Prod.fst := by cases op <;> simp [operationCoverage]\n\n"
    result += f"theorem operation_inventory_size : operationCoverage.length = {len(rows)} := rfl\n\n"
    result += "end S31.Evidence\n"
    return result


def check_audit(output: str, expected: set[str]) -> dict:
    found: dict[str, set[str]] = {}
    if not expected:
        raise FormalError("empty expected theorem inventory")
    if "error:" in output:
        raise FormalError("Lean audit reported an error")
    for line in output.splitlines():
        if line.startswith("S31_THEOREM "):
            parts = line.split()
            if len(parts) != 2 or parts[1] in found:
                raise FormalError("malformed or duplicate theorem audit record")
            found[parts[1]] = set()
        elif line.startswith("S31_AXIOM "):
            parts = line.split()
            if len(parts) != 3 or parts[1] not in found or parts[2] in found[parts[1]]:
                raise FormalError("malformed or duplicate axiom audit record")
            if parts[2] not in APPROVED_AXIOMS:
                raise FormalError(f"unapproved axiom: {parts[2]}")
            found[parts[1]].add(parts[2])
    if set(found) != expected:
        raise FormalError("live theorem inventory differs from source inventory: "
                          f"missing={sorted(expected - set(found))}, extra={sorted(set(found) - expected)}")
    return {"theorems": len(found), "approved_axioms": sorted(APPROVED_AXIOMS),
            "theorem_axioms": {name: sorted(found[name]) for name in sorted(found)}}


def check_kernel_log(output: str, files: dict[str, str]) -> dict:
    expected = set()
    for path in files:
        if path.startswith("formal/s31/"):
            expected.add(path.removeprefix("formal/s31/").removesuffix(".lean").replace("/", "."))
        elif path in REUSED:
            expected.add(path.removeprefix("formal/riscv-refinement/").removesuffix(".lean").replace("/", "."))
    actual = [line.removeprefix("replaying ") for line in output.splitlines() if line.startswith("replaying ")]
    if len(actual) != len(set(actual)) or set(actual) != expected:
        raise FormalError("kernel replay module inventory is incomplete or duplicated")
    if any(marker in output for marker in ("error", "exception", "found a problem")):
        raise FormalError("kernel replay reported a failure")
    return {"replayed_modules": len(actual)}


def check_schedule_report(output: str) -> dict:
    """Require every supported hash schedule and both malformed controls."""
    expected_profiles = ["poseidon_pair", *(f"poseidon_leaf_{n}" for n in (4, 8, 12, 16)),
                         "sha256_compression",
                         *(f"blake2s_{n}_{kind}" for n in range(17)
                           for kind in ("plain", "leaf", "pair"))]
    try:
        report = json.loads(output)
    except json.JSONDecodeError as error:
        raise FormalError("invalid Lean schedule report") from error
    expected = {"all_valid": True, "checked": len(expected_profiles), "failed": [],
                "malformed_rejected": 2, "profiles": expected_profiles}
    if report != expected:
        raise FormalError("Lean schedule validity report differs from the required profiles")
    return report
