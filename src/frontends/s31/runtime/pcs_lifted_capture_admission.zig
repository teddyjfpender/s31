//! Recheck the native PCS capture against the proof's four commitments.
//!
//! This is an executable local opening relation, not a polynomial commitment
//! soundness theorem. In particular, equal projected values at sampled indices
//! do not establish that an arbitrary committed tree is a lifted codeword.
const std = @import("std");
const core = @import("stwo_core");

const M31 = core.fields.m31.M31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const Capture = core.verifier.ProofCapture(H);

fn projectedPosition(position: usize, source_log: u32, target_log: u32) usize {
    if (source_log < target_log)
        return ((position >> 1) << @intCast(target_log - source_log + 1)) | (position & 1);
    return ((position >> @intCast(source_log - target_log + 1)) << 1) | (position & 1);
}

fn comesBefore(logs: []const u32, left: usize, right: usize) bool {
    return logs[left] < logs[right] or (logs[left] == logs[right] and left < right);
}

/// Rehash each raw-order row and full path against its proof commitment, then
/// require all sampled occurrences of one projected column index to agree.
/// Call after the native verifier accepts and before using its capture.
pub fn validate(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    proof_roots: []const H.Hash,
    capture: *const Capture,
) !void {
    const raw = capture.queries.raw;
    if (proof_roots.len != 4 or capture.commitments.len != proof_roots.len or
        capture.column_log_sizes.len != proof_roots.len or
        capture.trace_paths.len != proof_roots.len or
        raw.len == 0 or raw.len != pcs.fri_config.n_queries or
        pcs.trace_lifting_log_size == 0 or
        pcs.trace_lifting_log_size >= @bitSizeOf(usize))
        return error.InvalidPcsLiftedCapture;

    const source_height = pcs.trace_lifting_log_size;
    const source_size: usize = @as(usize, 1) << @intCast(source_height);
    for (raw) |position| {
        if (position >= source_size) return error.InvalidPcsLiftedCapture;
    }

    var value_offset: usize = 0;
    for (proof_roots, 0..) |root, tree_index| {
        if (!std.mem.eql(u8, &root, &capture.commitments[tree_index]))
            return error.InvalidPcsLiftedCapture;
        const logs = capture.column_log_sizes[tree_index];
        const path = capture.trace_paths[tree_index];
        const height = pcs.treeHeight(tree_index, logs) catch
            return error.InvalidPcsLiftedCapture;
        if (height == 0 or height >= @bitSizeOf(usize) or
            logs.len == 0 or path.path_depth != height or
            path.positions.len != raw.len or
            path.siblings.len != std.math.mul(usize, raw.len, @as(usize, height)) catch
                return error.InvalidPcsLiftedCapture)
            return error.InvalidPcsLiftedCapture;
        for (logs) |log| {
            if (log == 0 or log > height) return error.InvalidPcsLiftedCapture;
        }
        const value_count = std.math.mul(usize, logs.len, raw.len) catch
            return error.InvalidPcsLiftedCapture;
        const value_end = std.math.add(usize, value_offset, value_count) catch
            return error.InvalidPcsLiftedCapture;
        if (value_end > capture.queried_values.len)
            return error.InvalidPcsLiftedCapture;

        const order = try allocator.alloc(usize, logs.len);
        defer allocator.free(order);
        const row = try allocator.alloc(M31, logs.len);
        defer allocator.free(row);
        for (order, 0..) |*index, i| index.* = i;
        // Independent stable insertion sort: native leaf hashing sorts by
        // (extended column log, original column index).
        for (1..order.len) |i| {
            const index = order[i];
            var j = i;
            while (j > 0 and comesBefore(logs, index, order[j - 1])) : (j -= 1)
                order[j] = order[j - 1];
            order[j] = index;
        }

        // Check the sampled lift relation in linear expected time. Reusing
        // one table for each column avoids a quadratic query-pair scan and
        // keeps the work proportional to the published opening size.
        var seen = std.AutoHashMap(usize, M31).init(allocator);
        defer seen.deinit();
        try seen.ensureTotalCapacity(@intCast(raw.len));
        for (logs, 0..) |log, column| {
            seen.clearRetainingCapacity();
            for (raw, 0..) |position, slot| {
                const tree_position = projectedPosition(position, source_height, height);
                const column_position = projectedPosition(tree_position, height, log);
                const value = capture.queried_values[value_offset + column * raw.len + slot];
                const entry = try seen.getOrPut(column_position);
                if (entry.found_existing) {
                    if (!entry.value_ptr.*.eql(value)) return error.InvalidPcsLiftedCapture;
                } else entry.value_ptr.* = value;
            }
        }

        for (raw, 0..) |position, slot| {
            const tree_position = projectedPosition(position, source_height, height);
            if (path.positions[slot] != tree_position)
                return error.InvalidPcsLiftedCapture;
            for (order, 0..) |column, row_index| {
                const value = capture.queried_values[value_offset + column * raw.len + slot];
                row[row_index] = value;
            }
            var hasher = H.defaultWithInitialState();
            hasher.updateLeaf(row);
            var hash = hasher.finalize();
            var current = tree_position;
            for (path.path(slot)) |sibling| {
                hash = if ((current & 1) == 0)
                    H.hashChildren(.{ .left = hash, .right = sibling })
                else
                    H.hashChildren(.{ .left = sibling, .right = hash });
                current >>= 1;
            }
            if (current != 0 or !std.mem.eql(u8, &hash, &root))
                return error.InvalidPcsLiftedCapture;
        }
        value_offset = value_end;
    }
    if (value_offset != capture.queried_values.len)
        return error.InvalidPcsLiftedCapture;
}
