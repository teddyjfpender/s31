"""Pinned-source and independent integer-index check for lifted circle queries.

The finite enumeration is a geometry check, not a PCS/FRI security theorem.
"""
from __future__ import annotations

from pathlib import Path


def require(source: str, anchor: str, label: str) -> None:
    if anchor not in source:
        raise ValueError(f"{label}: pinned source mapping changed: {anchor!r}")


def check_projection_sources(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    prover = root / "deps/stwo-zig/src/prover"
    require((core / "pcs/utils.zig").read_text(),
            "out[i] = (pos >> @intCast(max_log_size - tree_log_size + 1) << 1) + (pos & 1);",
            "PCS smaller-tree query")
    require((core / "pcs/utils.zig").read_text(),
            "out[i] = (pos >> 1 << @intCast(tree_log_size - max_log_size + 1)) + (pos & 1);",
            "PCS larger-tree query")
    require((prover / "vcs_lifted/leaves.zig").read_text(),
            "const column_index = ((position >> shift_amt) << 1) + (position & 1);",
            "lifted prover leaf")
    require((core / "pcs/verifier.zig").read_text(),
            "positions.* = try pcs_utils.prepareTreeQueryPositions(",
            "PCS verifier tree query")
    require((prover / "pcs/scheme_views.zig").read_text(),
            "out[tree_index] = try pcs_utils.prepareTreeQueryPositions(",
            "PCS prover tree query")
    require((core / "poly/circle/domain.zig").read_text(),
            "if (i < half_size) return self.half_coset.indexAt(i);",
            "circle half coset")
    require((core / "poly/circle/domain.zig").read_text(),
            "return self.half_coset.indexAt(i - half_size).neg();",
            "circle conjugate half")
    require((core / "fri/folding.zig").read_text(),
            "core_utils.bitReverseIndex(subset_start, queries.log_domain_size)",
            "FRI circle point index")


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
