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
from scripts.release.pcs_fri_package_geometry import ROOT, extract_package, uint

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
        "try scheme.commit(allocator, roots[0], &pp_logs, &channel);",
        "try scheme.commit(allocator, roots[1], main_logs, &channel);",
        "try scheme.commit(allocator, roots[2], interaction_logs, &channel);",
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
        "return @as(usize, 1) << @intCast(split_depth);",
        "return std.math.mul(usize, chunks, extension_degree) catch null;",
        "return composition_log_size - split_depth;",
    ),
    "deps/stwo-zig/src/core/verifier.zig": (
        "const composition_log_size = components.compositionLogDegreeBound();",
        "const component_mask_log = verifier_types.compositionMaskLogSize(",
        "const max_log_degree_bound = if (comptime @import(\"protocol_revision.zig\").Revision.of(MC) == .proving_5a7c5ed) blk: {",
        "break :blk @max(component_mask_log, lifted_mask_log);",
        "@memset(\n        composition_commitment_log_sizes,\n        max_log_degree_bound,\n    );",
        "const composition_column_count = verifier_types.compositionColumnCount(",
        "qm31.SECURE_EXTENSION_DEGREE,",
        "try commitment_scheme.commit(\n        allocator,\n        composition_commitment,",
    ),
    "deps/stwo-zig/src/core/fields/qm31.zig": (
        "pub const SECURE_EXTENSION_DEGREE: usize = 4;",
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
        "var fri_verifier = try FriVerifier.commit(",
        "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {",
        "channel.mixU64(proof.proof_of_work);",
        "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(",
    ),
    "deps/stwo-zig/src/core/fri.zig": (
        "proof_in.inner_layers.len != config_mod.nFoldSteps(",
        "const first_line_log = column_bound.logDegreeBound() - config.fold_step;",
        "const column_commitment_domain = canonic.CanonicCoset",
        "var layer_bound = column_bound.foldToLineWithStep(config.fold_step);",
        "const remaining = layer_bound.logDegreeBound() - config.log_last_layer_degree_bound;",
        "const this_fold_step: u32 = config_mod.foldStepAt(config.fold_step, remaining);",
        "layer_bound = layer_bound.fold(this_fold_step)",
        "layer_domain = layer_domain.double();",
        "channel.mixFelts(last_layer_poly.coefficients());",
        "self.config.n_queries,",
        ".new(column_bound.logDegreeBound() + config.log_blowup_factor)",
        ".circleDomain();",
    ),
    "deps/stwo-zig/src/core/fri/config.zig": (
        "return @min(fold_step, remaining);",
        "return std.math.divCeil(u32, degree_log_ratio, fold_step) catch unreachable;",
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
    for name, ordered in (
        ("src/frontends/s31/runtime/native_verifier.zig", (
            "try scheme.commit(allocator, roots[0], &pp_logs, &channel);",
            "try scheme.commit(allocator, roots[1], main_logs, &channel);",
            "try scheme.commit(allocator, roots[2], interaction_logs, &channel);",
        )),
        ("deps/stwo-zig/src/core/pcs/verifier.zig", (
            "var fri_verifier = try FriVerifier.commit(",
            "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {",
            "channel.mixU64(proof.proof_of_work);",
            "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(",
        )),
    ):
        positions = [sources[name].index(token) for token in ordered]
        if positions != sorted(positions):
            raise ValueError(f"gate final-domain source order changed: {name}")
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
    # Protocol 4 starts with the composition quotient on D0 = N*B^2.
    # This cap applies even though the quotient-only native FRI uses N*B.
    paper_full_ensemble_log = trace_log + 2 * blowup_log
    if paper_full_ensemble_log > 30:
        raise ValueError("candidate paper N*B^2 exceeds the circle domain cap")
    if committed_composition_log + blowup_log > lifting_log:
        raise ValueError("composition column cannot fit the configured lifted tree")
    if lifting_log != trace_log + blowup_log:
        raise ValueError("configured lifting formula changed")
    blowup = 1 << blowup_log
    smallest_component_rows = 1 << min(row["trace_log_size"] for row in components)
    # For 0 < theta < (1-1/B)/2, alpha=1-theta is strictly greater
    # than (1+1/B)/2. The paper's small-table condition
    # alpha > (1/B)*(1+2/N_t) follows for every such theta when
    # (B-1)*N_t >= 4. Component/table identification remains unproved.
    uniform_small_table_condition = (blowup - 1) * smallest_component_rows >= 4
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
        "candidate_paper_protocol4_D0_if_N_is_trace_rows": 1 << paper_full_ensemble_log,
        "candidate_paper_domain_cap_rows": 1 << 30,
        "native_fri_domain_equals_candidate_paper_protocol4_D0": lifting_log == paper_full_ensemble_log,
        "candidate_smallest_component_rows": smallest_component_rows,
        "conditional_small_table_ood_for_every_udr_theta_if_components_are_tables": uniform_small_table_condition,
        "formula": "D = 2^(key.trace_log_size + key.fri.log_blowup_factor), conditional on successful pinned gate verification",
    }
    # A derived FRI domain is one theorem input, not the P01 theorem.
    report["theorem_inputs"]["D_final_fri_domain"] = 1 << lifting_log
    report["missing_theorem_inputs"] = [item for item in report["missing_theorem_inputs"]
                                        if not item.startswith("split composition log-degree bound")]
    report["missing_theorem_inputs"].append(
        "native binary/source correspondence and successful verifier execution for this package")
    return report


def derive_gate_trace_and_fri_schedule(report: dict, roster: dict) -> dict:
    """Inventory the checked Gate roster and native fold-step-1 schedule.

    The production caller first verifies the package and runs its native
    check-key. This arithmetic function still validates its inputs so a test
    or future caller cannot turn a malformed report into a plausible schedule.
    It never estimates a security level or identifies a published theorem rate.
    """
    if (report.get("lowering"), report.get("key_schema"), report.get("profile")) != (
            "gate", "s31-verification-key-gate-roster-v1", "circuit-v1"):
        raise ValueError("only the sealed gate profile is reviewed")
    if report.get("package_checks", {}).get("native_check_key") != "accepted":
        raise ValueError("gate schedule needs a native check-key acceptance")
    final = report.get("gate_final_domain", {})
    fri = report.get("fri", {})
    fold_step = uint(fri.get("fold_step"), "gate fold step", minimum=1)
    last_degree_bound = uint(fri.get("last_layer_degree_bound"), "terminal degree bound", minimum=1)
    queries = uint(fri.get("raw_queries"), "raw query count", maximum=100000, minimum=1)
    blowup_log = uint(fri.get("log_blowup_factor"), "FRI blowup log", minimum=1)
    pow_bits = uint(fri.get("pow_bits"), "FRI PoW bits", maximum=31)
    if (final.get("status") != "conditional_source_bound_geometry" or
            (fold_step, last_degree_bound, queries, blowup_log, pow_bits) !=
            (1, 1, 70, 1, 26)):
        raise ValueError("unreviewed gate FRI schedule")
    components = report.get("components")
    raw_components = roster.get("components")
    fixed_columns = report.get("preprocessed_columns")
    raw_fixed = roster.get("preprocessed_columns")
    if (not isinstance(components, list) or len(components) != 11 or
            not isinstance(raw_components, list) or len(raw_components) != 11 or
            not isinstance(fixed_columns, list) or len(fixed_columns) != 45 or
            not isinstance(raw_fixed, list) or len(raw_fixed) != 45):
        raise ValueError("incomplete sealed gate component or fixed-column roster")
    tables = []
    for index, (row, raw) in enumerate(zip(components, raw_components, strict=True)):
        main_width = uint(raw.get("base_trace_columns"), "main trace width", maximum=100000, minimum=1)
        interaction_width = uint(raw.get("interaction_trace_columns"), "interaction trace width", maximum=100000, minimum=1)
        trace_log = uint(row.get("trace_log_size"), "reported table trace log")
        raw_trace_log = uint(raw.get("trace_log_size"), "sealed table trace log")
        trace_rows = uint(row.get("trace_rows"), "table trace rows", maximum=1 << 30, minimum=1)
        extended_log = uint(row.get("configured_extended_log_size"), "table extended log", maximum=31)
        extended_rows = uint(row.get("configured_extended_rows"), "table extended rows", maximum=1 << 31, minimum=1)
        if (raw.get("name") != row.get("name") or
                uint(raw.get("proof_index"), "sealed table proof index", maximum=100000) != index or
                uint(raw.get("source_index"), "sealed table source index", maximum=100000) != index or
                uint(raw.get("claimed_sum_index"), "sealed table claimed sum index", maximum=100000) != index or
                raw_trace_log != trace_log or trace_rows != 1 << trace_log or
                extended_log != trace_log + blowup_log or extended_rows != 1 << extended_log):
            raise ValueError("sealed gate trace width or height differs from checked roster")
        tables.append({
            "name": row["name"], "proof_index": index,
            "trace_log_size": row["trace_log_size"],
            "trace_rows": row["trace_rows"],
            "main_trace_columns": main_width,
            "interaction_trace_columns": interaction_width,
            "configured_extended_log_size": row["configured_extended_log_size"],
            "configured_extended_rows": row["configured_extended_rows"],
        })
    for index, (row, raw) in enumerate(zip(fixed_columns, raw_fixed, strict=True)):
        log = uint(row.get("log_size"), "reported fixed-column log")
        raw_log = uint(raw.get("log_size"), "sealed fixed-column log")
        rows = uint(row.get("rows"), "reported fixed-column rows", maximum=1 << 30, minimum=1)
        raw_rows = uint(raw.get("rows"), "sealed fixed-column rows", maximum=1 << 30, minimum=1)
        if (raw.get("id") != row.get("id") or
                uint(raw.get("commitment_index"), "fixed-column commitment index", maximum=100000) != index or
                raw_log != log or rows != 1 << log or raw_rows != rows):
            raise ValueError("sealed gate fixed-column height differs from checked roster")

    domain_log = uint(final.get("fri_input_domain_log"), "FRI input domain log")
    degree_log = uint(final.get("fri_input_degree_bound_log"), "FRI input degree log")
    split_depth = uint(final.get("composition_split_depth"), "composition split depth", minimum=1)
    composition_log = uint(final.get("committed_composition_column_log_size"), "composition column log")
    max_trace_log = uint(report.get("max_trace_log_size"), "maximum trace log")
    lifting_log = uint(report.get("configured_trace_lifting_log_size"), "trace lifting log", maximum=31)
    domain_rows = uint(final.get("fri_input_domain_rows"), "FRI input domain rows", maximum=1 << 30, minimum=1)
    if (split_depth != 1 or
            domain_log != degree_log + blowup_log or
            domain_log != lifting_log or domain_log != max_trace_log + blowup_log or
            domain_rows != 1 << domain_log or composition_log != degree_log or
            not 1 <= domain_log <= 30 or degree_log < 1):
        raise ValueError("gate input degree or domain differs from checked FRI geometry")
    last_degree_log = 0  # key value 1 denotes at most one terminal coefficient
    rounds = []
    while degree_log > last_degree_log:
        index = len(rounds)
        rounds.append({
            "commitment_index": index,
            "kind": "circle_first" if index == 0 else "line_inner",
            "commitment_domain_log_size": domain_log,
            "degree_log_bound_before_fold": degree_log,
            "fold_step": 1,
            "degree_log_bound_after_fold": degree_log - 1,
            "next_domain_log_size": domain_log - 1,
        })
        degree_log -= 1
        domain_log -= 1
    if domain_log != blowup_log or len(rounds) < 2:
        raise ValueError("gate terminal FRI domain or layer count differs")
    report["gate_trace_and_fri_schedule"] = {
        "status": "conditional_source_bound_geometry",
        "tables": tables,
        "preprocessed_columns": fixed_columns,
        "main_trace_column_count": sum(row["main_trace_columns"] for row in tables),
        "interaction_trace_column_count": sum(row["interaction_trace_columns"] for row in tables),
        "main_trace_column_cells": sum(row["main_trace_columns"] * row["trace_rows"] for row in tables),
        "interaction_trace_column_cells": sum(row["interaction_trace_columns"] * row["trace_rows"] for row in tables),
        "preprocessed_column_cells": sum(row["rows"] for row in fixed_columns),
        "pcs_commitment_trees": [
            {"tree_index": 0, "kind": "preprocessed", "column_count": len(fixed_columns),
             "lifted_height_log_size": final["fri_input_domain_log"]},
            {"tree_index": 1, "kind": "main", "column_count": sum(row["main_trace_columns"] for row in tables),
             "lifted_height_log_size": final["fri_input_domain_log"]},
            {"tree_index": 2, "kind": "interaction", "column_count": sum(row["interaction_trace_columns"] for row in tables),
             "lifted_height_log_size": final["fri_input_domain_log"]},
            {"tree_index": 3, "kind": "composition", "column_count": (1 << split_depth) * 4,
             "column_log_size": composition_log,
             "lifted_height_log_size": final["fri_input_domain_log"]},
        ],
        "fri_commitment_and_fold_rounds": rounds,
        "fri_first_circle_commitments": 1,
        "fri_inner_line_commitments": len(rounds) - 1,
        "fri_folding_challenges": len(rounds),
        "terminal_line_domain_log_size": domain_log,
        "terminal_line_domain_rows": 1 << domain_log,
        "terminal_polynomial_max_coefficients": last_degree_bound,
        "raw_query_draws": queries,
        "unique_query_count": None,
        "published_theorem_parameter_mapping": None,
    }
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
    roster = json.loads((package / "gate-component-roster.json").read_text())
    report = derive_gate_trace_and_fri_schedule(report, roster)
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
