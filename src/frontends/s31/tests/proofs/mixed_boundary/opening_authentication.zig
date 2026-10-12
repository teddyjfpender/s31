//! Authenticated queried openings for the source-pinned general mixed proof.
//!
//! These are proof-byte mutations, not changes to a witness before proving.
//! A full trace is not decoded by succinct verification: the test exercises
//! one opened value in the fixed tree and in every circuit/chip/bridge slot
//! of the main and interaction trees, including both registered chip kinds.
//! It also changes an authentication-path hash in each commitment tree.
const std = @import("std");
const core = @import("stwo_core");
const cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("interop_postcard");
const relation = @import("../../../language/relation.zig");
const package = @import("../../../runtime/mixed_boundary/general_package.zig");
const family = @import("../../../runtime/mixed_boundary/test_source.zig");

const M31 = core.fields.m31.M31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const call_count = 3;
const slot_count = 1 + 2 * call_count;
const proof_offset = "S31MIX07".len + 4 + 3 * 32 + 8 + slot_count * 16;

test "mixed circuit pair and many chip bridge queried openings authenticate to their roots" {
    const allocator = std.heap.smp_allocator;
    const source = comptime family.forCount(call_count);
    const air = @embedFile("s31_air_programs");
    const initial = [4]M31{ M31.fromCanonical(1), M31.fromCanonical(2), M31.fromCanonical(3), M31.fromCanonical(4) };
    var final = initial;
    for (0..call_count) |call_id| for (0..16) |_| {
        for (&final) |*word| word.* = word.*.mul(word.*).add(M31.fromCanonical(@intCast(13 + call_id)));
    };
    var sum: [4]u32 = undefined;
    var product: [4]u32 = undefined;
    for (initial, final, &sum, &product) |start, end, *s, *p| {
        s.* = start.add(end).toU32();
        p.* = start.mul(end).toU32();
    }
    const words = sum ++ product;
    const assigned = try std.fmt.allocPrint(allocator, "{{\"public_inputs\":{{}},\"private_inputs\":{{\"x\":[1,2,3,4]}},\"public_outputs\":{{\"sum\":[{d},{d},{d},{d}],\"product\":[{d},{d},{d},{d}]}}}}", .{ sum[0], sum[1], sum[2], sum[3], product[0], product[1], product[2], product[3] });
    defer allocator.free(assigned);
    var assignment = try relation.parseAssignment(allocator, assigned);
    defer assignment.deinit();
    const sealed = try package.proveSealedAndInspect(allocator, source, air, assignment.value);
    defer allocator.free(sealed.bytes);
    try package.verifyEmbedded(source, air, allocator, words, sealed.bytes);
    try std.testing.expect(sealed.bytes.len > proof_offset);

    var stream = std.io.fixedBufferStream(sealed.bytes[proof_offset..]);
    var stark = try postcard.deserializeProof(H, allocator, stream.reader());
    defer stark.deinit(allocator);
    try std.testing.expectEqual(sealed.bytes.len - proof_offset, stream.pos);
    try std.testing.expectEqual(@as(usize, 4), stark.commitment_scheme_proof.queried_values.items.len);

    // Establish that the decode/encode path itself leaves the accepted proof
    // byte-for-byte unchanged before interpreting any mutant rejection.
    var roundtrip: std.ArrayList(u8) = .empty;
    defer roundtrip.deinit(allocator);
    try roundtrip.appendSlice(allocator, sealed.bytes[0..proof_offset]);
    try postcard.serializeProof(H, roundtrip.writer(allocator), stark);
    try std.testing.expectEqualSlices(u8, sealed.bytes, roundtrip.items);

    const geometry = sealed.inspection.schedule.native_geometry.?;
    try std.testing.expectEqual(@as(usize, slot_count), geometry.slot_count);
    try std.testing.expectEqual(@as(?cpu.direct_mixed_admission.SourceKind, null), geometry.slots[0].kind);
    try std.testing.expectEqual(cpu.direct_mixed_admission.SourceKind.pair_chip, geometry.slots[1].kind.?);
    try std.testing.expectEqual(cpu.direct_mixed_admission.SourceKind.pair_bridge, geometry.slots[2].kind.?);
    try std.testing.expectEqual(cpu.direct_mixed_admission.SourceKind.many_chip, geometry.slots[5].kind.?);
    try std.testing.expectEqual(cpu.direct_mixed_admission.SourceKind.many_bridge, geometry.slots[6].kind.?);
    const pcs = geometry.pcs;
    var sample_width_limits: [4]u32 = .{ 0, 0, 0, 1 };
    for (geometry.tree_columns[0..3], 0..) |width, tree| {
        for (geometry.columns[tree][0..width]) |column|
            sample_width_limits[tree] = @max(sample_width_limits[tree], column.mask_width);
    }
    for (0..3) |tree| {
        const columns = stark.commitment_scheme_proof.queried_values.items[tree];
        try std.testing.expectEqual(geometry.tree_columns[tree], columns.len);
        const targets: usize = if (tree == 0) 1 else geometry.slot_count;
        for (0..targets) |slot_index| {
            const first: usize = if (tree == 0) 0 else @intCast(if (tree == 1)
                geometry.slots[slot_index].main_offset
            else
                geometry.slots[slot_index].interaction_offset);
            const width: usize = if (tree == 0) columns.len else @intCast(if (tree == 1)
                geometry.slots[slot_index].main_columns
            else
                geometry.slots[slot_index].interaction_columns);
            try std.testing.expect(width > 1);
            // The first column catches a missing component opening; the last
            // catches a truncated span that still authenticates its prefix.
            for ([_]usize{ first, first + width - 1 }) |column_index| {
                try std.testing.expect(column_index < columns.len);
                try std.testing.expect(columns[column_index].len > 0);
                const original = columns[column_index][0];
                columns[column_index][0] = original.add(M31.one());
                defer columns[column_index][0] = original;
                var changed: std.ArrayList(u8) = .empty;
                defer changed.deinit(allocator);
                try changed.appendSlice(allocator, sealed.bytes[0..proof_offset]);
                try postcard.serializeProof(H, changed.writer(allocator), stark);
                try std.testing.expectEqual(sealed.bytes.len, changed.items.len);
                try std.testing.expect(!std.mem.eql(u8, sealed.bytes, changed.items));
                try postcard.proof_preflight.validateFor(4, changed.items[proof_offset..], .{
                    .config = .{
                        .pow_bits = pcs.fri_config.pow_bits,
                        .log_blowup_factor = pcs.fri_config.log_blowup_factor,
                        .n_queries = pcs.fri_config.n_queries,
                        .log_last_layer_degree_bound = pcs.fri_config.log_last_layer_degree_bound,
                        .fold_step = pcs.fri_config.fold_step,
                        .lifting_log_size = null,
                    },
                    .tree_columns = geometry.tree_columns,
                    .max_column_log_size = geometry.max_column_log_size,
                    .sample_width_limits = sample_width_limits,
                    .hash_size = @sizeOf(H.Hash),
                    .max_wire_bytes = (16 << 20) - proof_offset,
                });
                try std.testing.expectError(error.RootMismatch, package.verifyEmbedded(source, air, allocator, words, changed.items));
                columns[column_index][0] = original;
            }
        }
    }

    // A changed queried value must not be the only negative PCS control:
    // decommitment witnesses are separately supplied by the proof. Keep the
    // values and transcript commitments intact, and change one sibling hash
    // in each tree (fixed, main, interaction, quotient). All four serialized
    // proofs remain structurally valid; each must fail at its own Merkle root.
    try std.testing.expectEqual(@as(usize, 4), stark.commitment_scheme_proof.decommitments.items.len);
    for (stark.commitment_scheme_proof.decommitments.items) |*decommitment| {
        try std.testing.expect(decommitment.hash_witness.len > 0);
        const original = decommitment.hash_witness[0];
        decommitment.hash_witness[0][0] ^= 1;
        var changed: std.ArrayList(u8) = .empty;
        defer changed.deinit(allocator);
        try changed.appendSlice(allocator, sealed.bytes[0..proof_offset]);
        try postcard.serializeProof(H, changed.writer(allocator), stark);
        try std.testing.expectEqual(sealed.bytes.len, changed.items.len);
        var changed_bytes: usize = 0;
        for (sealed.bytes, changed.items) |before, after| {
            if (before != after) changed_bytes += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), changed_bytes);
        try postcard.proof_preflight.validateFor(4, changed.items[proof_offset..], .{
            .config = .{
                .pow_bits = pcs.fri_config.pow_bits,
                .log_blowup_factor = pcs.fri_config.log_blowup_factor,
                .n_queries = pcs.fri_config.n_queries,
                .log_last_layer_degree_bound = pcs.fri_config.log_last_layer_degree_bound,
                .fold_step = pcs.fri_config.fold_step,
                .lifting_log_size = null,
            },
            .tree_columns = geometry.tree_columns,
            .max_column_log_size = geometry.max_column_log_size,
            .sample_width_limits = sample_width_limits,
            .hash_size = @sizeOf(H.Hash),
            .max_wire_bytes = (16 << 20) - proof_offset,
        });
        try std.testing.expectError(error.RootMismatch, package.verifyEmbedded(source, air, allocator, words, changed.items));
        decommitment.hash_witness[0] = original;
    }
}
