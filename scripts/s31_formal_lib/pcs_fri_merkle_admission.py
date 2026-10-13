"""Pin S31's post-success FRI Merkle row/path replay barrier.

This guards source order and shape, not a verified semantics of Zig or BLAKE2s.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(verifier: str, admission: str, qm31: str, hasher: str,
                  fri: str) -> None:
    if verifier.count('const fri_merkle_admission = @import("fri_merkle_admission.zig");') != 1:
        raise ValueError("FRI Merkle admission import changed")
    call = "try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);"
    if verifier.count(call) != 4:
        raise ValueError("all four S31 verifier paths must run FRI Merkle admission")
    barrier = (
        "        capture.last_layer_coefficients,\n"
        "    );\n"
        "    " + call
    )
    if verifier.count(barrier) != 4:
        raise ValueError("FRI Merkle admission must follow operational replay")
    for start, end in (
        ("fn verifyProfile(", "fn logsFor("),
        ("pub fn verifySparse(", "pub fn serializeSparseWide("),
        ("fn verifySparseWideInternal(", "pub fn serializeDirect("),
        ("fn verifyDirectProfile(", "fn sparseLogs("),
    ):
        part = region(verifier, start, end)
        if part.count(call) != 1:
            raise ValueError(f"FRI Merkle admission path changed: {start}")

    if admission.count("pub fn validate(") != 1:
        raise ValueError("FRI Merkle admission entry point changed")
    validate = admission
    ordered_once(
        validate, "FRI Merkle admission replay",
        "if (raw.len == 0 or captured.layers.len == 0)",
        "const positions = try allocator.dupe(usize, raw);",
        "for (captured.layers) |layer| {",
        "const source_log = std.math.add(u32, layer.path_depth, step)",
        "const leaf_log: u32 = if (source_log >= LOG_PACKED_LEAF_SIZE and step > 1)",
        "const width: usize = @as(usize, 1) << @intCast(step);",
        "layer.siblings.len != siblings_count",
        "if (layer.positions[slot] != position or",
        "const subset = layer.queryValues(slot);",
        "const coords = subset[leaf * leaf_width + offset].toM31Array();",
        "row[offset * 4 + coordinate] = coords[coordinate];",
        "hasher.updateLeaf(row[0 .. leaf_width * 4]);",
        "nodes[i] = H.hashChildren(.{ .left = nodes[2 * i], .right = nodes[2 * i + 1] });",
        "var parent_position = position >> @intCast(step);",
        "for (layer.queryPath(slot)) |sibling| {",
        "H.hashChildren(.{ .left = sibling, .right = hash });",
        "!std.mem.eql(u8, hash[0..], layer.commitment[0..])",
        "positions[slot] = position >> @intCast(step);",
    )
    if qm31.count("return .{ self.c0.a, self.c0.b, self.c1.a, self.c1.b };") != 1:
        raise ValueError("QM31 native coordinate order changed")
    if hasher.count("self.inner.update(std.mem.sliceAsBytes(column_values));") != 1 or \
            hasher.count("const value_bytes = column_values[at + i].toBytesLe();") != 1:
        raise ValueError("Merkle leaf M31 byte encoding changed")

    commit = region(fri, "pub fn commit(", "pub fn sampleQueryPositions(")
    ordered_once(
        commit, "first FRI layer packing decision",
        ".pack_leaves = column_commitment_domain.logSize() >= LOG_PACKED_LEAF_SIZE and\n"
        "                    config.fold_step > 1,",
    )
    ordered_once(
        commit, "inner FRI layer packing decision",
        ".pack_leaves = layer_domain.logSize() >= LOG_PACKED_LEAF_SIZE and\n"
        "                        this_fold_step > 1,",
    )
    for start, end in (
        ("fn verifyImpl(", "fn FriInnerLayerVerifier("),
        ("fn verifyAndFoldImpl(", "const FoldedLayerState"),
    ):
        part = region(fri, start, end)
        ordered_once(
            part, "FRI proof root into verified capture",
            "const leaf_log_size: u32 = if (self.pack_leaves) LOG_PACKED_LEAF_SIZE else 0;",
            "var merkle_verifier = try vcs_verifier.MerkleVerifierLifted(H).init(",
            "merkle_verifier.verifyWithPathCapture(",
            "destination.* = try buildFriLayerQueryCapture(\n"
            "                    H,\n"
            "                    allocator,\n"
            "                    self.proof.commitment,",
        )


def check_pcs_fri_merkle_admission(root: Path) -> None:
    check_sources(
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (root / "src/frontends/s31/runtime/fri_merkle_admission.zig").read_text(),
        (root / "deps/stwo-zig/src/core/fields/qm31.zig").read_text(),
        (root / "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig").read_text(),
        (root / "deps/stwo-zig/src/core/fri.zig").read_text(),
    )
