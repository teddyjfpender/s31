#!/usr/bin/env python3
"""Gate-profile composition and FRI-domain diagnostic for locally trusted packages.

This describes the configured domain of a *successful* pinned native verifier.
It does not modify package artifacts, but executes the package's own native
verifier for check-key. Manifest hashes check internal consistency, not binary
provenance. Run only with a locally trusted package executable. This is not a
PCS/FRI soundness certificate and --require-complete stays closed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_package_geometry import ROOT, extract_package

BUNDLE = "deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin"
SOURCE_TOKENS = {
    "src/frontends/s31/build.zig": (
        'deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin',
    ),
    "src/frontends/s31/runtime/mvp_runtime.zig": (
        "fn parseAirBundle(allocator: std.mem.Allocator) !cpu.air.Bundle",
        "return cpu.air.parse(allocator, air_program_bytes);",
        "if (key.trace_log_size != expected_trace_log or",
    ),
    "src/frontends/s31/runtime/native_verifier.zig": (
        "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;",
        "var bound = try cpu.air.bind(allocator, template, component_logs, layout);",
        "runtime.* = .init(allocator, source, &pp_logs, lifting_bound, lookup.z, lookup.alpha, claimed);",
        "handle.* = runtime.asVerifierComponent();",
        "handles[0..component_count]",
    ),
    "deps/stwo-zig/src/integrations/circuit_cpu/air.zig": (
        "const evaluation_delta = std.math.sub(u32, source.evaluation_log_size, source.trace_log_size)",
        "const evaluation_log = trace_log + evaluation_delta;",
        "component.* = try bindComponent(allocator, source, trace_log, &recorded_layout, layout);",
        "if (!std.mem.eql(u8, component.label, name)) return error.InvalidCircuitBundle;",
    ),
    "deps/stwo-zig/src/frontends/cairo/witness/composition_bundle.zig": (
        'pub const magic = "STWZEVA\\x00".*;',
        "const label_len = try reader.int(u16);",
        "const trace_log = try reader.int(u32);",
        "const eval_log = try reader.int(u32);",
        "const denom_count = try reader.int(u32);",
        "const expected_denoms: u64 = @as(u64, 1) << @intCast(eval_log - trace_log);",
        "if (reader.cursor != bytes.len) return error.TrailingData;",
    ),
    "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig": (
        ".maxConstraintLogDegreeBound = maxConstraintLogDegreeBound,",
        "return cast(ctx).captured.evaluation_log_size;",
    ),
    "deps/stwo-zig/src/core/air/components.zig": (
        "max_bound = @max(max_bound, c.maxConstraintLogDegreeBound());",
        "return verifier_types.COMPOSITION_LOG_SPLIT;",
    ),
    "deps/stwo-zig/src/core/verifier_types.zig": (
        "pub const COMPOSITION_LOG_SPLIT: u32 = 1;",
        "return composition_log_size - split_depth;",
    ),
    "deps/stwo-zig/src/core/verifier.zig": (
        "const composition_log_size = components.compositionLogDegreeBound();",
        "const component_mask_log = verifier_types.compositionMaskLogSize(",
        "const max_log_degree_bound = if (comptime @import(\"protocol_revision.zig\").Revision.of(MC) == .proving_5a7c5ed) blk: {",
        "break :blk @max(component_mask_log, lifted_mask_log);",
        "@memset(\n        composition_commitment_log_sizes,\n        max_log_degree_bound,\n    );",
        "try commitment_scheme.commit(\n        allocator,\n        composition_commitment,",
    ),
    "deps/stwo-zig/src/core/pcs/config_v2.zig": (
        "return fromFriAndLiftingSize(config, trace_log_size + config.log_blowup_factor);",
        "if (log_size > height) return error.InvalidTreeHeight;",
        "return height;",
    ),
    "deps/stwo-zig/src/core/pcs/verifier.zig": (
        "const explicit_heights = verifier_revision == .proving_5a7c5ed;",
        "try verifier_revision.treeHeight(self.revision_config, self.trees.items.len, extended_log_sizes)",
        "break :blk self.trees.items[self.trees.items.len - 1].height;",
        "const bound = fri.CirclePolyDegreeBound.init(lifting_log_size - self.config.fri_config.log_blowup_factor);",
    ),
    "deps/stwo-zig/src/core/fri.zig": (
        ".new(column_bound.logDegreeBound() + config.log_blowup_factor)",
        ".circleDomain();",
    ),
    "deps/stwo-zig/src/core/poly/circle/canonic.zig": (
        "return domain.CircleDomain.new(self.halfCoset());",
        "return Coset.halfOdds(self.logSize() - 1);",
    ),
    "deps/stwo-zig/src/core/poly/circle/domain.zig": (
        "pub const MAX_CIRCLE_DOMAIN_LOG_SIZE: u32 = circle.M31_CIRCLE_LOG_ORDER - 1;",
        "return @as(usize, 1) << @intCast(self.logSize());",
        "return self.half_coset.log_size + 1;",
    ),
    "deps/stwo-zig/src/core/circle.zig": (
        "pub const M31_CIRCLE_LOG_ORDER: u32 = 31;",
        "return new(CirclePointIndex.subgroupGen(log_size + 1), log_size);",
    ),
    "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig": (
        "pub const profiles = core.vcs_lifted.channel_profile.proving_5a7c5ed;",
    ),
}


def check_source_texts(sources: dict[str, str]) -> str:
    for name, tokens in SOURCE_TOKENS.items():
        source = sources[name]
        if any(token not in source for token in tokens):
            raise ValueError(f"gate final-domain source changed: {name}")
    text = sources["deps/stwo-zig/src/integrations/circuit_cpu/air.zig"]
    matches = re.findall(r'pub const bundle_sha256 = "([0-9a-f]{64})";', text)
    if len(matches) != 1:
        raise ValueError("AIR bundle digest source changed")
    resident = sources["deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig"]
    vtable = resident.split("pub fn asComponent(self: *const RuntimeComponent)", 1)[1].split("fn cast(", 1)[0]
    if "compositionLogSplit" in vtable:
        raise ValueError("runtime component split override changed")
    return matches[0]


@dataclass(frozen=True)
class BundleComponent:
    label: str
    evaluation_delta: int
    constraints: int
    parts: int


def bundle_components(data: bytes) -> list[BundleComponent]:
    """Read only the checked bundle envelope and component geometry metadata.

    This is intentionally not a second AIR semantic parser. The native parser
    and verifier remain trusted premises of the source-bound diagnostic.
    """
    cursor = 0

    def take(fmt: str):
        nonlocal cursor
        size = struct.calcsize("<" + fmt)
        if cursor + size > len(data):
            raise ValueError("truncated AIR bundle")
        result = struct.unpack_from("<" + fmt, data, cursor)
        cursor += size
        return result[0] if len(result) == 1 else result

    def skip(size: int) -> None:
        nonlocal cursor
        if cursor + size > len(data):
            raise ValueError("truncated AIR bundle body")
        cursor += size

    if take("8s") != b"STWZEVA\x00" or take("I") not in (1, 2):
        raise ValueError("unreviewed AIR bundle format")
    max_instructions, total_constraints, max_eval, count, plan_hash = (
        take("I"), take("Q"), take("I"), take("I"), take("Q"))
    if not (0 < max_instructions <= 1_000_000 and 0 < total_constraints and
            0 < max_eval <= 31 and 0 < count <= 4096 and plan_hash):
        raise ValueError("invalid AIR bundle header")
    components: list[BundleComponent] = []
    next_constraint = 0
    found_max_eval = 0
    for _ in range(count):
        label_len, reserved = take("H"), take("H")
        (instance, trace, evaluation, constraints, random_offset, spans,
         preprocessed, denominators, sources, parts) = take("10I")
        if (not 0 < label_len <= 256 or reserved or not 0 < trace <= evaluation <= max_eval or
                not 0 < constraints or not 0 < spans <= 64 or preprocessed > 4096 or
                not 0 < denominators <= 65536 or sources > 65536 or
                not 0 < parts <= constraints or evaluation - trace > 16 or
                denominators != 1 << (evaluation - trace) or
                random_offset != next_constraint):
            raise ValueError("invalid AIR component geometry")
        if cursor + label_len > len(data):
            raise ValueError("truncated AIR component label")
        try:
            label = data[cursor:cursor + label_len].decode("ascii")
        except UnicodeDecodeError as exc:
            raise ValueError("invalid AIR component label") from exc
        skip(label_len + spans * 12 + preprocessed * 4 + denominators * 4 + sources * 32)
        for _ in range(parts):
            _, program_len, _ = take("IIQ")
            if not 0 < program_len <= 256 * 1024 * 1024:
                raise ValueError("invalid AIR program length")
            skip(program_len)
        components.append(BundleComponent(label, evaluation - trace, constraints, parts))
        next_constraint += constraints
        found_max_eval = max(found_max_eval, evaluation)
    if cursor != len(data) or next_constraint != total_constraints or found_max_eval != max_eval:
        raise ValueError("invalid AIR bundle end or header totals")
    return components


def bundle_offsets(data: bytes) -> list[tuple[str, int]]:
    """Preserve the original degree-only interface for existing diagnostics."""
    return [(item.label, item.evaluation_delta) for item in bundle_components(data)]


def derive_gate_constraint_roster(report: dict, components: list[BundleComponent]) -> dict:
    """Expose the AIR bundle's native count fields without treating them as paper k_t."""
    roster = report["components"]
    if len(roster) != len(components) or any(
            row["name"] != item.label for row, item in zip(roster, components, strict=True)):
        raise ValueError("AIR constraint counts and sealed gate roster order differ")
    if any(item.constraints <= 0 or item.parts <= 0 or item.parts > item.constraints
           for item in components):
        raise ValueError("invalid AIR constraint count or part count")
    report["gate_air_constraint_roster"] = {
        "status": "conditional_bundle_metadata",
        "components": [
            {"name": item.label, "native_constraint_count": item.constraints,
             "native_program_parts": item.parts}
            for item in components
        ],
        "native_total_constraints": sum(item.constraints for item in components),
        "identified_as_published_k_t": False,
    }
    return report


def derive_gate(report: dict, offsets: list[tuple[str, int]]) -> dict:
    if (report["lowering"], report["key_schema"], report["profile"]) != (
            "gate", "s31-verification-key-gate-roster-v1", "circuit-v1"):
        raise ValueError("only the sealed gate profile is reviewed")
    if report["package_checks"]["native_check_key"] != "accepted":
        raise ValueError("gate key needs a native check-key acceptance")
    components = report["components"]
    if len(components) != len(offsets) or any(
            row["name"] != name for row, (name, _) in zip(components, offsets, strict=True)):
        raise ValueError("AIR bundle and sealed gate roster order differ")
    degree_logs = [row["trace_log_size"] + delta
                   for row, (_, delta) in zip(components, offsets, strict=True)]
    if any(log > 31 for log in degree_logs):
        raise ValueError("AIR degree log exceeds native domain")
    unsplit = max(degree_logs)
    split = 1  # source-guarded default for these runtime components
    if unsplit <= split:
        raise ValueError("invalid split composition bound")
    split_log = unsplit - split
    trace_log = report["max_trace_log_size"]
    blowup_log = report["fri"]["log_blowup_factor"]
    committed_composition_log = max(split_log, trace_log)
    lifting_log = report["configured_trace_lifting_log_size"]
    if lifting_log > 30 or trace_log < report["fri"]["fold_step"]:
        raise ValueError("gate FRI domain exceeds circle or fold geometry")
    if committed_composition_log + blowup_log > lifting_log:
        raise ValueError("composition column cannot fit the configured lifted tree")
    if lifting_log != trace_log + blowup_log:
        raise ValueError("configured lifting formula changed")
    report["gate_final_domain"] = {
        "status": "conditional_source_bound_geometry",
        "template_evaluation_offsets": dict(offsets),
        "component_constraint_degree_logs": dict(zip((row["name"] for row in components), degree_logs, strict=True)),
        "unsplit_composition_log_degree_bound": unsplit,
        "composition_split_depth": split,
        "split_composition_log_degree_bound": split_log,
        "committed_composition_column_log_size": committed_composition_log,
        "composition_tree_height_log": lifting_log,
        "fri_input_degree_bound_log": lifting_log - blowup_log,
        "fri_input_domain_log": lifting_log,
        "fri_input_domain_rows": 1 << lifting_log,
        "formula": "D = 2^(key.trace_log_size + key.fri.log_blowup_factor), conditional on successful pinned gate verification",
    }
    # A derived FRI domain is one theorem input, not the P01 theorem.
    report["theorem_inputs"]["D_final_fri_domain"] = 1 << lifting_log
    report["missing_theorem_inputs"] = [item for item in report["missing_theorem_inputs"]
                                        if not item.startswith("split composition log-degree bound")]
    report["missing_theorem_inputs"].append(
        "native binary/source correspondence and successful verifier execution for this package")
    return report


def extract_gate(package: Path, root: Path = ROOT) -> dict:
    report = extract_package(package, root)
    sources = {name: (root / name).read_text() for name in SOURCE_TOKENS}
    digest = check_source_texts(sources)
    key = json.loads((package / "verification-key.json").read_text())
    data = (root / BUNDLE).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != digest or key.get("air_bundle_sha256") != digest:
        raise ValueError("AIR bundle, source digest, and sealed gate key differ")
    components = bundle_components(data)
    report = derive_gate(report, [(item.label, item.evaluation_delta) for item in components])
    report = derive_gate_constraint_roster(report, components)
    report["gate_final_domain"]["air_bundle_sha256"] = digest
    report["gate_final_domain"]["source_sha256"] = {
        name: hashlib.sha256(text.encode()).hexdigest() for name, text in sources.items()}
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = extract_gate(args.package.resolve())
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"PCS/FRI gate final domain rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_complete else 0


if __name__ == "__main__":
    raise SystemExit(main())
