"""Pinned-source and independent integer-index check for lifted circle queries.

The finite enumeration is a geometry check, not a PCS/FRI security theorem.
"""
from __future__ import annotations

from pathlib import Path

PROJECTION_SOURCE_FILES = (
    "deps/stwo-zig/src/core/pcs/utils.zig",
    "deps/stwo-zig/src/prover/vcs_lifted/leaves.zig",
    "deps/stwo-zig/src/core/pcs/verifier.zig",
    "deps/stwo-zig/src/prover/pcs/scheme_views.zig",
    "deps/stwo-zig/src/core/poly/circle/domain.zig",
    "deps/stwo-zig/src/core/fri/folding.zig",
    "deps/stwo-zig/src/core/vcs_lifted/verifier.zig",
    "deps/stwo-zig/src/core/pcs/config_v2.zig",
    "deps/stwo-zig/src/prover/vcs_lifted/prover.zig",
    "src/frontends/s31/runtime/native_verifier.zig",
    "deps/stwo-zig/src/prover/vcs_lifted/expand.zig",
    "deps/stwo-zig/src/prover/vcs_lifted/columns.zig",
    "deps/stwo-zig/src/frontends/circuit/witness/trace.zig",
    "deps/stwo-zig/src/core/verifier_types.zig",
    "deps/stwo-zig/src/core/fields/qm31.zig",
    "deps/stwo-zig/src/core/verifier.zig",
)


def require(source: str, anchor: str, label: str) -> None:
    if anchor not in source:
        raise ValueError(f"{label}: pinned source mapping changed: {anchor!r}")


def check_projection_sources(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    prover = root / "deps/stwo-zig/src/prover"
    s31 = root / "src/frontends/s31"
    sources = {name: (root / name).read_text() for name in PROJECTION_SOURCE_FILES}

    def pinned(path: Path) -> str:
        return sources[path.relative_to(root).as_posix()]

    require(pinned(core / "pcs/utils.zig"),
            "out[i] = (pos >> @intCast(max_log_size - tree_log_size + 1) << 1) + (pos & 1);",
            "PCS smaller-tree query")
    require(pinned(core / "pcs/utils.zig"),
            "out[i] = (pos >> 1 << @intCast(tree_log_size - max_log_size + 1)) + (pos & 1);",
            "PCS larger-tree query")
    require(pinned(prover / "vcs_lifted/leaves.zig"),
            "const column_index = ((position >> shift_amt) << 1) + (position & 1);",
            "lifted prover leaf")
    require(pinned(core / "pcs/verifier.zig"),
            "positions.* = try pcs_utils.prepareTreeQueryPositions(",
            "PCS verifier tree query")
    require(pinned(prover / "pcs/scheme_views.zig"),
            "out[tree_index] = try pcs_utils.prepareTreeQueryPositions(",
            "PCS prover tree query")
    require(pinned(core / "poly/circle/domain.zig"),
            "if (i < half_size) return self.half_coset.indexAt(i);",
            "circle half coset")
    require(pinned(core / "poly/circle/domain.zig"),
            "return self.half_coset.indexAt(i - half_size).neg();",
            "circle conjugate half")
    require(pinned(core / "fri/folding.zig"),
            "core_utils.bitReverseIndex(subset_start, queries.log_domain_size)",
            "FRI circle point index")
    pcs = pinned(core / "pcs/verifier.zig")
    for anchor in (
            "const explicit_heights = verifier_revision == .proving_5a7c5ed;",
            "break :blk self.trees.items[self.trees.items.len - 1].height;",
            "const height = self.trees.items[i].height;",
            "return if (height == 0) null else height;",
            "const raw_tree_positions = try pcs_utils.prepareTreeQueryPositions(",
            "query_capture.raw,\n                        lifting_log_size,\n                        tree_log_size,",
            "tree.verifyWithPathCapture(\n                        allocator,\n                        raw_tree_positions,\n                        raw_columns.items,",
    ):
        require(pcs, anchor, "PCS captured lifted tree query")
    lifted = pinned(core / "vcs_lifted/verifier.zig")
    for anchor in (
            "if (maxLogSize(column_log_sizes) > height) return error.InvalidTreeHeight;",
            "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
            "std.sort.heap(usize, col_indices, self.column_log_sizes, lessByLogSize);",
            "return MerkleVerificationError.DuplicateQueryMismatch;",
            "row[col_i] = col[col_pos[col_i]];",
            "hasher.updateLeaf(row);",
            "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root)) {",
            ".positions = try allocator.dupe(usize, query_positions),",
            ".path_depth = self.height,",
            "if (lhs_size == rhs_size) return lhs < rhs;",
    ):
        require(lifted, anchor, "captured lifted Merkle verifier")
    config = pinned(core / "pcs/config_v2.zig")
    for anchor in (
            "return fromFriAndLiftingSize(config, trace_log_size + config.log_blowup_factor);",
            "if (log_size > height) return error.InvalidTreeHeight;",
            "return height;",
    ):
        require(config, anchor, "configured lifted tree height")
    lifted_prover = pinned(prover / "vcs_lifted/prover.zig")
    for anchor in (
            "if (lifting_log_size == natural) return;",
            "if (lifting_log_size < natural) return error.InvalidTreeHeight;",
            "HashExpandOps.expandHashers(lifted, leaves, @intCast(log_ratio + 1));",
    ):
        require(lifted_prover, anchor, "lifted prover leaf expansion")
    native = pinned(s31 / "runtime/native_verifier.zig")
    for anchor in (
            "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;",
            "const widths = circuit.witness.trace.traceWidths();",
            "const interaction_widths = circuit.witness.trace.interactionWidths();",
            "@memset(logs[cursor..][0..width], log);",
            "var capture: core.verifier.ProofCapture(H) = undefined;",
            "try core.verifier.verifyBorrowedExWithProofCapture(",
            "handles[0..component_count],",
            "&capture,",
    ):
        require(native, anchor, "S31 native gate proof capture")
    require(pinned(prover / "vcs_lifted/leaves.zig"),
            "const column_index = ((position >> shift_amt) << 1) + (position & 1);",
            "lifted prover per-column leaf value")
    for anchor in (
            "const even = ctx.src[2 * run];",
            "const odd = ctx.src[2 * run + 1];",
            "ctx.dst[at] = if ((at & 1) == 0) even else odd;",
    ):
        require(pinned(prover / "vcs_lifted/expand.zig"), anchor,
                "lifted prover leaf replication")
    require(pinned(prover / "vcs_lifted/columns.zig"),
            "if (lhs.log_size == rhs.log_size) return lhs.original_index < rhs.original_index;",
            "lifted prover stable column order")
    trace = pinned(root / "deps/stwo-zig/src/frontends/circuit/witness/trace.zig")
    for anchor in (
            "for (component_list.component_facts.toArray(), &out) |facts, *width| width.* = facts.trace_columns;",
            "for (component_list.component_facts.toArray(), &out) |facts, *width| width.* = facts.interaction_columns;",
    ):
        require(trace, anchor, "gate trace column widths")
    for anchor in (
            "pub const COMPOSITION_LOG_SPLIT: u32 = 1;",
            "return std.math.mul(usize, chunks, extension_degree) catch null;",
    ):
        require(pinned(core / "verifier_types.zig"), anchor,
                "gate composition column count")
    require(pinned(core / "fields/qm31.zig"),
            "pub const SECURE_EXTENSION_DEGREE: usize = 4;",
            "gate composition extension width")
    for anchor in (
            "const composition_column_count = verifier_types.compositionColumnCount(",
            "qm31.SECURE_EXTENSION_DEGREE,",
    ):
        require(pinned(core / "verifier.zig"), anchor,
                "gate composition column count")


def bit_reverse(value: int, width: int) -> int:
    result = 0
    for _ in range(width):
        result = (result << 1) | (value & 1)
        value >>= 1
    return result


def circle_group_index(log_size: int, raw_query: int) -> int:
    """Independent canonical-circle index from Coset + CircleDomain formulas."""
    if not 1 <= log_size <= 30 or not 0 <= raw_query < 1 << log_size:
        raise ValueError("outside canonical circle domain")
    natural = bit_reverse(raw_query, log_size)
    half_size = 1 << (log_size - 1)
    sign = -1 if natural >= half_size else 1
    coset_index = (1 << (30 - log_size)) + \
        (natural % half_size) * (1 << (32 - log_size))
    return sign * coset_index % (1 << 31)


def tree_query_position(raw_query: int, max_log_size: int, tree_log_size: int) -> int:
    """Reference for both branches of pinned `prepareTreeQueryPositions`."""
    if max_log_size < tree_log_size:
        return ((raw_query >> 1) << (tree_log_size - max_log_size + 1)) + (raw_query & 1)
    if max_log_size == tree_log_size:
        return raw_query
    return ((raw_query >> (max_log_size - tree_log_size + 1)) << 1) + (raw_query & 1)


def check_projection_geometry(max_log_size: int = 10) -> int:
    """Exhaust small domains, both tree-height directions and conjugate pairs."""
    checked = 0
    for source_log in range(1, max_log_size + 1):
        for tree_log in range(1, max_log_size + 1):
            for raw in range(1 << source_log):
                tree_raw = tree_query_position(raw, source_log, tree_log)
                if tree_raw >= 1 << tree_log or (tree_raw & 1) != (raw & 1):
                    raise ValueError("lifted query index leaves domain or changes conjugate bit")
                if source_log >= tree_log:
                    projected = circle_group_index(source_log, raw) << (source_log - tree_log)
                    expected = circle_group_index(tree_log, tree_raw)
                else:
                    projected = circle_group_index(tree_log, tree_raw) << (tree_log - source_log)
                    expected = circle_group_index(source_log, raw)
                if projected % (1 << 31) != expected:
                    raise ValueError("lifted query disagrees with circle-group squaring")
                checked += 1
    return checked


def check_pcs_fri_projection(root: Path) -> int:
    check_projection_sources(root)
    return check_projection_geometry()
