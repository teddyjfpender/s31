//! Independently rehash published FRI subsets and upper Merkle paths.
//! This checks packed and unpacked leaves on the actual S31 channel profile.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const admission = @import("fri_merkle_admission");

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
const Hasher = Profile.MerkleHasher;
const Channel = Profile.Channel;
const Verifier = core.fri.FriVerifier(Hasher, Profile);

comptime {
    if (Channel != core.channel.blake2s.Blake2sM31Channel)
        @compileError("Merkle binding regression requires the S31 M31 channel");
    if (Hasher != core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher)
        @compileError("Merkle binding regression requires the S31 plain Merkle hasher");
}

fn replay(
    allocator: std.mem.Allocator,
    layer: core.fri.FriLayerQueryCapture(Hasher),
    slot: usize,
    leaf_log: u32,
) !bool {
    const step = layer.fold_step;
    if (slot >= layer.query_count or leaf_log > step or step >= @bitSizeOf(usize))
        return error.InvalidShape;
    const width: usize = @as(usize, 1) << @intCast(step);
    const leaf_width: usize = @as(usize, 1) << @intCast(leaf_log);
    if (layer.fold_width != width) return error.InvalidShape;
    const subset = layer.queryValues(slot);
    if (subset.len != width) return error.InvalidShape;

    const row = try allocator.alloc(M31, 4 * leaf_width);
    defer allocator.free(row);
    const nodes = try allocator.alloc(Hasher.Hash, width / leaf_width);
    defer allocator.free(nodes);
    for (nodes, 0..) |*node, leaf| {
        for (0..leaf_width) |offset| {
            const coordinates = subset[leaf * leaf_width + offset].toM31Array();
            @memcpy(row[offset * 4 ..][0..4], coordinates[0..]);
        }
        var hasher = Hasher.defaultWithInitialState();
        hasher.updateLeaf(row);
        node.* = hasher.finalize();
    }
    var count = nodes.len;
    while (count > 1) {
        for (0..count / 2) |i| {
            nodes[i] = Hasher.hashChildren(.{ .left = nodes[2 * i], .right = nodes[2 * i + 1] });
        }
        count /= 2;
    }
    var hash = nodes[0];
    var position = layer.positions[slot] >> @intCast(step);
    for (layer.queryPath(slot)) |sibling| {
        hash = if ((position & 1) == 0)
            Hasher.hashChildren(.{ .left = hash, .right = sibling })
        else
            Hasher.hashChildren(.{ .left = sibling, .right = hash });
        position >>= 1;
    }
    return position == 0 and std.mem.eql(u8, hash[0..], layer.commitment[0..]);
}

fn runAdmissionCase(column_log_size: u32, fold_step: u32, n_queries: usize) !void {
    const allocator = std.testing.allocator;
    var config = try core.fri.FriConfig.init(0, 1, n_queries);
    config.fold_step = fold_step;
    const domain = core.poly.circle.canonic.CanonicCoset.new(column_log_size).circleDomain();

    const values = try allocator.alloc(QM31, domain.size());
    defer allocator.free(values);
    for (values, 0..) |*value, i| {
        const natural_index = core.utils.bitReverseIndex(i, column_log_size);
        value.* = QM31.fromBase(domain.at(natural_index).x);
    }
    const column = try prover.secure_column.SecureColumnByCoords.fromSecureSlice(allocator, values);
    var prover_channel = Channel{};
    var fri_prover = try prover.fri.FriProver(CpuBackend, Hasher, Profile).commit(
        allocator, &prover_channel, config, domain, column,
    );
    var decommitment = try fri_prover.decommit(allocator, &prover_channel);
    defer decommitment.deinit(allocator);

    const bound = core.fri.CirclePolyDegreeBound.init(column_log_size - config.log_blowup_factor);
    var verifier_channel = Channel{};
    var verifier = try Verifier.commit(
        allocator, &verifier_channel, config, decommitment.fri_proof.proof, bound,
    );
    defer verifier.deinit(allocator);
    var sampled = try verifier.sampleQueryPositionsWithRaw(allocator, &verifier_channel);
    defer sampled.deinit(allocator);
    try std.testing.expect(sampled.raw.len > sampled.unique.len);
    try std.testing.expectEqualSlices(usize, decommitment.query_positions, sampled.unique);

    const answers = try allocator.alloc(QM31, sampled.unique.len);
    defer allocator.free(answers);
    for (answers, sampled.unique) |*answer, position| answer.* = values[position];
    var capture: core.fri.FriQueryCapture(Hasher) = undefined;
    try verifier.decommitWithQueryCapture(allocator, answers, sampled.raw, &capture);
    defer capture.deinit(allocator);
    try admission.validate(allocator, sampled.raw, capture);
    try std.testing.expectEqual(@as(usize, 2), capture.layers.len);
    try std.testing.expectEqual(fold_step, capture.layers[0].fold_step);
    try std.testing.expectEqual(@as(u32, 1), capture.layers[1].fold_step);
    for (capture.layers, 0..) |layer, layer_index| {
        const leaf_log: u32 = if (layer_index == 0) 2 else 0;
        for (0..layer.query_count) |slot| {
            try std.testing.expect(try replay(allocator, layer, slot, leaf_log));
        }
    }

    const original_value = capture.layers[0].values[0];
    capture.layers[0].values[0] = original_value.add(QM31.one());
    try std.testing.expect(!(try replay(allocator, capture.layers[0], 0, 2)));
    try std.testing.expectError(error.InvalidFriMerkleCapture,
        admission.validate(allocator, sampled.raw, capture));
    capture.layers[0].values[0] = original_value;

    const original_sibling = capture.layers[0].siblings[0];
    capture.layers[0].siblings[0] = [_]u8{0} ** 32;
    try std.testing.expect(!(try replay(allocator, capture.layers[0], 0, 2)));
    try std.testing.expectError(error.InvalidFriMerkleCapture,
        admission.validate(allocator, sampled.raw, capture));
    capture.layers[0].siblings[0] = original_sibling;

    const original_position = capture.layers[0].positions[0];
    capture.layers[0].positions[0] = original_position ^ (@as(usize, 1) << @intCast(capture.layers[0].fold_step));
    try std.testing.expect(!(try replay(allocator, capture.layers[0], 0, 2)));
    try std.testing.expectError(error.InvalidFriMerkleCapture,
        admission.validate(allocator, sampled.raw, capture));
    capture.layers[0].positions[0] = original_position;

    const original_commitment = capture.layers[1].commitment;
    capture.layers[1].commitment = [_]u8{0} ** 32;
    try std.testing.expectError(error.InvalidFriMerkleCapture,
        admission.validate(allocator, sampled.raw, capture));
    capture.layers[1].commitment = original_commitment;

    const original_siblings = capture.layers[1].siblings;
    capture.layers[1].siblings = original_siblings[0 .. original_siblings.len - 1];
    try std.testing.expectError(error.InvalidFriMerkleCapture,
        admission.validate(allocator, sampled.raw, capture));
    capture.layers[1].siblings = original_siblings;
}

test "FRI Merkle binding: fold step 2 packed and partial unpacked capture" {
    try runAdmissionCase(4, 2, 16);
}

test "FRI Merkle binding: fold step 4 packed and partial unpacked capture" {
    try runAdmissionCase(6, 4, 70);
}
