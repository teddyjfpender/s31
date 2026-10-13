"""Pin the post-success PCS lifted-row/root admission and its native inputs.

This is a source-order guard, not Zig semantics or cryptographic soundness.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


CALL = "try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);"


def check_sources(verifier: str, admission: str, pcs: str, lifted: str,
                  config: str, hasher: str, collision: str) -> None:
    if verifier.count('const pcs_lifted_capture_admission = @import("pcs_lifted_capture_admission.zig");') != 1:
        raise ValueError("PCS lifted admission import changed")
    if verifier.count(CALL) != 4:
        raise ValueError("all four S31 native profiles must admit lifted PCS captures")
    for start, end in (
        ("fn verifyProfile(", "fn logsFor("),
        ("pub fn verifySparse(", "pub fn serializeSparseWide("),
        ("fn verifySparseWideInternal(", "pub fn serializeDirect("),
        ("fn verifyDirectProfile(", "fn sparseLogs("),
    ):
        part = region(verifier, start, end)
        ordered_once(part, start,
                     "try core.verifier.verifyBorrowedExWithProofCapture(",
                     "try deep_capture_admission.validate(",
                     "try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);",
                     CALL)
        if part.count(CALL) != 1:
            raise ValueError(f"PCS lifted admission path changed: {start}")

    ordered_once(admission, "PCS lifted admission",
                 "raw.len != pcs.fri_config.n_queries",
                 "const source_height = pcs.trace_lifting_log_size;",
                 "if (!std.mem.eql(u8, &root, &capture.commitments[tree_index]))",
                 "const height = pcs.treeHeight(tree_index, logs)",
                 "path.positions.len != raw.len",
                 "if (value_end > capture.queried_values.len)",
                 "while (j > 0 and comesBefore(logs, index, order[j - 1]))",
                 "try seen.ensureTotalCapacity(@intCast(raw.len));",
                 "const column_position = projectedPosition(tree_position, height, log);",
                 "const entry = try seen.getOrPut(column_position);",
                 "if (!entry.value_ptr.*.eql(value)) return error.InvalidPcsLiftedCapture;",
                 "if (path.positions[slot] != tree_position)",
                 "hasher.updateLeaf(row);",
                 "for (path.path(slot)) |sibling| {",
                 "H.hashChildren(.{ .left = sibling, .right = hash });",
                 "!std.mem.eql(u8, &hash, &root)",
                 "if (value_offset != capture.queried_values.len)")
    pcs_capture = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    for source, anchor, label in (
        (admission, "return ((position >> @intCast(source_log - target_log + 1)) << 1) | (position & 1);",
         "smaller lifted column projection"),
        (admission, "return ((position >> 1) << @intCast(target_log - source_log + 1)) | (position & 1);",
         "larger lifted tree projection"),
        (pcs_capture, "if (!std.meta.eql(tree.root, commitment))", "PCS proof root ownership"),
        (pcs_capture, "for (raw_columns.items) |column| {", "PCS capture value ordering"),
        (pcs_capture, "try expanded_queried_values.appendSlice(allocator, column);", "PCS capture value flattening"),
        (pcs_capture, ".commitments = commitments,", "PCS capture root custody"),
        (pcs_capture, ".column_log_sizes = captured_column_log_sizes,", "PCS capture log custody"),
        (pcs_capture, ".trace_paths = trace_paths.?,", "PCS capture path custody"),
        (lifted, "row[col_i] = col[col_pos[col_i]];", "native lifted row"),
        (lifted, ".positions = try allocator.dupe(usize, query_positions),", "native path order"),
        (config, "const height = self.liftingLogSize(tree_index);", "configured tree height"),
        (hasher, "self.inner.update(std.mem.sliceAsBytes(column_values));", "native row encoding"),
        (hasher, "pub const Blake2sPlainMerkleHasher = Blake2sPlainMerkleHasherGeneric(false);",
         "selected plain BLAKE2s hasher"),
        (hasher, "return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);",
         "plain parent encoding"),
    ):
        if anchor not in source:
            raise ValueError(f"{label} source mapping changed: {anchor!r}")

    ordered_once(collision, "native duplicate-query audit",
                 "pub fn auditDuplicateQueries(",
                 "positions.len != paths.len)",
                 "const row_width = rows[0].len;",
                 "if (position >= domain_size or row_width == 0 or",
                 "row.len != row_width or !canonical(row) or",
                 "for (positions[0..i], 0..) |prior_position, j| {",
                 "if (!rowsEq(row, rows[j]) or !std.mem.eql(Hash, path, paths[j]))",
                 "return error.DuplicateMismatch;")
    ordered_once(collision, "native Merkle collision reduction",
                 "first_path.len != height or second_path.len != height or",
                 "!canonical(first_row) or !canonical(second_row))",
                 "if (!hashEq(pathRoot(position, first_row, first_path), root) or",
                 "if (rowsEq(first_row, second_row)) return error.SameRow;",
                 "if (hashEq(first, second)) {",
                 "const first_children = children(index, first, first_sibling);",
                 "const next_first = H.hashChildren(first_children);",
                 "if (!childrenEq(first_children, second_children) and",
                 "return error.InternalInvariant;")


def check_pcs_fri_lifted_capture(root: Path) -> None:
    s31 = root / "src/frontends/s31/runtime"
    core = root / "deps/stwo-zig/src/core"
    check_sources(
        (s31 / "native_verifier.zig").read_text(),
        (s31 / "pcs_lifted_capture_admission.zig").read_text(),
        (core / "pcs/verifier.zig").read_text(),
        (core / "vcs_lifted/verifier.zig").read_text(),
        (core / "pcs/config_v2.zig").read_text(),
        (core / "vcs_lifted/blake2_merkle.zig").read_text(),
        (root / "formal/s31/tests/lib/pcs_merkle_collision_reduction.zig").read_text(),
    )
