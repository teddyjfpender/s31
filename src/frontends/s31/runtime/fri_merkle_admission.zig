//! Rehash verifier-owned FRI subsets and upper paths before S31 reports success.
//!
//! This checks the concrete native-opening side of the conditional Lean
//! `FriMerkleBinding.authenticatedSlot` premise. It does not establish that a
//! fixed putative oracle generated the commitment or rule out hash collisions.
const std = @import("std");
const core = @import("stwo_core");

const M31 = core.fields.m31.M31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const LOG_PACKED_LEAF_SIZE = core.fri.LOG_PACKED_LEAF_SIZE;

comptime {
    if (LOG_PACKED_LEAF_SIZE != 2)
        @compileError("S31 FRI Merkle admission expects four QM31 values per packed leaf");
}

/// Verify every raw-query subset against its recorded FRI commitment using
/// independent leaf materialization and path replay. `raw` is the transcript
/// draw in exact order and multiplicity. Call only after core PCS verification;
/// this gate rejects a corrupted or mismapped post-verification capture.
pub fn validate(
    allocator: std.mem.Allocator,
    raw: []const usize,
    captured: core.fri.FriQueryCapture(H),
) !void {
    if (raw.len == 0 or captured.layers.len == 0) return error.InvalidFriMerkleCapture;
    const positions = try allocator.dupe(usize, raw);
    defer allocator.free(positions);

    for (captured.layers) |layer| {
        const step = layer.fold_step;
        if (step == 0 or step >= @bitSizeOf(usize) or
            layer.path_depth >= @bitSizeOf(usize))
            return error.InvalidFriMerkleCapture;
        const source_log = std.math.add(u32, layer.path_depth, step) catch
            return error.InvalidFriMerkleCapture;
        if (source_log > core.circle.M31_CIRCLE_LOG_ORDER)
            return error.InvalidFriMerkleCapture;

        // `FriVerifier.commit` packs iff the source domain has at least four
        // evaluations and this layer performs more than one fold.
        const leaf_log: u32 = if (source_log >= LOG_PACKED_LEAF_SIZE and step > 1)
            LOG_PACKED_LEAF_SIZE
        else
            0;
        const width: usize = @as(usize, 1) << @intCast(step);
        const leaf_width: usize = @as(usize, 1) << @intCast(leaf_log);
        const path_depth: usize = @intCast(layer.path_depth);
        const values_count = std.math.mul(usize, raw.len, width) catch
            return error.InvalidFriMerkleCapture;
        const siblings_count = std.math.mul(usize, raw.len, path_depth) catch
            return error.InvalidFriMerkleCapture;
        if (layer.fold_width != width or layer.query_count != raw.len or
            layer.positions.len != raw.len or layer.values.len != values_count or
            layer.siblings.len != siblings_count)
            return error.InvalidFriMerkleCapture;

        const nodes = try allocator.alloc(H.Hash, width / leaf_width);
        defer allocator.free(nodes);
        for (positions, 0..) |position, slot| {
            if (layer.positions[slot] != position or
                position >= (@as(usize, 1) << @intCast(source_log)))
                return error.InvalidFriMerkleCapture;
            const subset = layer.queryValues(slot);
            for (nodes, 0..) |*node, leaf| {
                var row: [4 * (1 << LOG_PACKED_LEAF_SIZE)]M31 = undefined;
                for (0..leaf_width) |offset| {
                    const coords = subset[leaf * leaf_width + offset].toM31Array();
                    inline for (0..4) |coordinate| {
                        row[offset * 4 + coordinate] = coords[coordinate];
                    }
                }
                var hasher = H.defaultWithInitialState();
                hasher.updateLeaf(row[0 .. leaf_width * 4]);
                node.* = hasher.finalize();
            }

            // The subset consists of consecutive packed leaves. Reconstruct
            // its complete Merkle subtree before following the captured upper
            // path. This covers both packed and unpacked partial folds.
            var count = nodes.len;
            while (count > 1) {
                for (0..count / 2) |i| {
                    nodes[i] = H.hashChildren(.{ .left = nodes[2 * i], .right = nodes[2 * i + 1] });
                }
                count /= 2;
            }
            var hash = nodes[0];
            var parent_position = position >> @intCast(step);
            for (layer.queryPath(slot)) |sibling| {
                hash = if ((parent_position & 1) == 0)
                    H.hashChildren(.{ .left = hash, .right = sibling })
                else
                    H.hashChildren(.{ .left = sibling, .right = hash });
                parent_position >>= 1;
            }
            if (parent_position != 0 or
                !std.mem.eql(u8, hash[0..], layer.commitment[0..]))
                return error.InvalidFriMerkleCapture;
            positions[slot] = position >> @intCast(step);
        }
    }
}
