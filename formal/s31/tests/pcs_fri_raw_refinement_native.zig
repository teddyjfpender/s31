//! Differential audit of native FRI captures for varied layer schedules.
//! This checks raw-slot transitions independently of the verifier's folding
//! helpers. It does not prove Merkle binding or Zig-to-Lean semantics.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
const Hasher = Profile.MerkleHasher;
const Channel = Profile.Channel;
const Verifier = core.fri.FriVerifier(Hasher, Profile);

comptime {
    if (Channel != core.channel.blake2s.Blake2sM31Channel)
        @compileError("FRI audit must use the S31 M31 transcript channel");
    if (Hasher != core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher)
        @compileError("FRI audit must use the S31 plain Merkle hasher");
}

fn pair(alpha: QM31, coordinate: M31, left: QM31, right: QM31) !QM31 {
    const inverse = try coordinate.inv();
    return left.add(right).add(alpha.mul(left.sub(right).mulM31(inverse)));
}

fn referenceLine(
    allocator: std.mem.Allocator,
    values: []const QM31,
    initial_domain: core.poly.line.LineDomain,
    alpha: QM31,
    steps: u32,
) !QM31 {
    if (steps == 0 or values.len != (@as(usize, 1) << @intCast(steps)))
        return error.BadLayerShape;
    const scratch = try allocator.dupe(QM31, values);
    defer allocator.free(scratch);
    var domain = initial_domain;
    var length = scratch.len;
    for (0..steps) |step| {
        const half = length / 2;
        const challenge = alpha.pow(@as(u64, 1) << @intCast(step));
        for (0..half) |i| {
            const point_index = core.utils.bitReverseIndex(
                i,
                @intCast(std.math.log2_int(usize, half)),
            );
            const x = domain.at(point_index);
            scratch[i] = try pair(challenge, x, scratch[2 * i], scratch[2 * i + 1]);
        }
        length = half;
        domain = domain.double();
    }
    return scratch[0];
}

fn referenceCircle(
    allocator: std.mem.Allocator,
    values: []const QM31,
    source_domain: core.poly.circle.domain.CircleDomain,
    subset_start: usize,
    alpha: QM31,
    steps: u32,
) !QM31 {
    if (steps == 0 or values.len != (@as(usize, 1) << @intCast(steps)))
        return error.BadLayerShape;
    const initial_index = core.utils.bitReverseIndex(subset_start, source_domain.logSize());
    const fold_initial = source_domain.indexAt(initial_index);
    const fold_domain = core.poly.circle.domain.CircleDomain.new(
        core.circle.Coset.new(fold_initial, steps - 1),
    );
    const half = values.len / 2;
    const first = try allocator.alloc(QM31, half);
    defer allocator.free(first);
    for (first, 0..) |*out, i| {
        const point_index = core.utils.bitReverseIndex(
            i,
            @intCast(std.math.log2_int(usize, half)),
        );
        const y = fold_domain.half_coset.at(point_index).y;
        out.* = try pair(alpha, y, values[2 * i], values[2 * i + 1]);
    }
    if (steps == 1) return first[0];
    return referenceLine(
        allocator,
        first,
        core.poly.line.LineDomain.fromCircleDomain(fold_domain),
        alpha.square(),
        steps - 1,
    );
}

fn referenceInner(
    allocator: std.mem.Allocator,
    values: []const QM31,
    source_domain: core.poly.line.LineDomain,
    subset_start: usize,
    alpha: QM31,
    steps: u32,
) !QM31 {
    if (steps == 0 or values.len != (@as(usize, 1) << @intCast(steps)))
        return error.BadLayerShape;
    const initial_index = core.utils.bitReverseIndex(subset_start, source_domain.logSize());
    const fold_initial = source_domain.coset().indexAt(initial_index);
    const fold_domain = try core.poly.line.LineDomain.init(
        core.circle.Coset.new(fold_initial, steps),
    );
    return referenceLine(allocator, values, fold_domain, alpha, steps);
}

fn findValue(positions: []const usize, values: []const QM31, position: usize) !QM31 {
    for (positions, values) |candidate, value| {
        if (candidate == position) return value;
    }
    return error.MissingQuery;
}

fn audit(
    allocator: std.mem.Allocator,
    verifier: *const Verifier,
    capture: core.fri.FriQueryCapture(Hasher),
    raw: []const usize,
    unique: []const usize,
    first_values: []const QM31,
) !void {
    if (unique.len != first_values.len or
        capture.layers.len != 1 + verifier.inner_layers.len or
        verifier.last_layer_poly.len() >
            (@as(usize, 1) << @intCast(verifier.config.log_last_layer_degree_bound)))
        return error.BadLayerShape;

    for (capture.layers, 0..) |layer, layer_index| {
        const step = if (layer_index == 0)
            verifier.config.fold_step
        else
            verifier.inner_layers[layer_index - 1].fold_step;
        const alpha = if (layer_index == 0)
            verifier.first_layer.folding_alpha
        else
            verifier.inner_layers[layer_index - 1].folding_alpha;
        const commitment = if (layer_index == 0)
            verifier.first_layer.proof.commitment
        else
            verifier.inner_layers[layer_index - 1].proof.commitment;
        if (step == 0 or step >= @bitSizeOf(usize)) return error.BadLayerShape;
        const width = @as(usize, 1) << @intCast(step);
        if (layer.query_count != raw.len or layer.positions.len != raw.len or
            layer.values.len != raw.len * width or layer.fold_step != step or
            layer.fold_width != width or !layer.folding_alpha.eql(alpha) or
            !std.meta.eql(layer.commitment, commitment))
            return error.BadLayerShape;

        // A merged group has one authenticated subset, even when several raw
        // draws refer to it. Check this at every layer before using its values.
        for (layer.positions, 0..) |position, i| {
            for (layer.positions[0..i], 0..) |prior, j| {
                if ((prior >> @intCast(step)) != (position >> @intCast(step))) continue;
                for (layer.queryValues(i), layer.queryValues(j)) |left, right| {
                    if (!left.eql(right)) return error.InconsistentGroup;
                }
            }
        }
    }

    for (raw, 0..) |initial_position, slot| {
        var position = initial_position;
        var current = try findValue(unique, first_values, position);
        for (capture.layers, 0..) |layer, layer_index| {
            if (layer.positions[slot] != position) return error.BadRawPosition;
            const step = layer.fold_step;
            const width: usize = @intCast(layer.fold_width);
            const subset = layer.queryValues(slot);
            if (!subset[position % width].eql(current)) return error.BadCurrentValue;
            const subset_start = (position >> @intCast(step)) << @intCast(step);
            current = if (layer_index == 0)
                try referenceCircle(
                    allocator,
                    subset,
                    verifier.first_layer.column_commitment_domain,
                    subset_start,
                    layer.folding_alpha,
                    step,
                )
            else
                try referenceInner(
                    allocator,
                    subset,
                    verifier.inner_layers[layer_index - 1].domain,
                    subset_start,
                    layer.folding_alpha,
                    step,
                );
            position >>= @intCast(step);
        }
        const x = verifier.last_layer_domain.at(core.utils.bitReverseIndex(
            position,
            verifier.last_layer_domain.logSize(),
        ));
        const expected = try verifier.last_layer_poly.evalAtPoint(
            allocator,
            QM31.fromBase(x),
        );
        if (!current.eql(expected)) return error.BadTerminalValue;
    }
}

fn runSchedule(allocator: std.mem.Allocator, log_size: u32, step: u32) !void {
    var config = try core.fri.FriConfig.init(0, 1, 8);
    config.fold_step = step;
    const domain = core.poly.circle.canonic.CanonicCoset.new(log_size).circleDomain();
    const values = try allocator.alloc(QM31, domain.size());
    defer allocator.free(values);
    for (values, 0..) |*value, i| {
        const natural = core.utils.bitReverseIndex(i, log_size);
        value.* = if (log_size == 2)
            QM31.zero()
        else
            QM31.fromBase(domain.at(natural).x);
    }
    const column = try prover.secure_column.SecureColumnByCoords.fromSecureSlice(
        allocator,
        values,
    );
    var prover_channel = Channel{};
    var fri_prover = try prover.fri.FriProver(CpuBackend, Hasher, Profile).commit(
        allocator,
        &prover_channel,
        config,
        domain,
        column,
    );
    var proof = try fri_prover.decommit(allocator, &prover_channel);
    defer proof.deinit(allocator);

    var verifier_channel = Channel{};
    var verifier = try Verifier.commit(
        allocator,
        &verifier_channel,
        config,
        proof.fri_proof.proof,
        core.fri.CirclePolyDegreeBound.init(log_size - config.log_blowup_factor),
    );
    defer verifier.deinit(allocator);
    var sampled = try verifier.sampleQueryPositionsWithRaw(allocator, &verifier_channel);
    defer sampled.deinit(allocator);
    try std.testing.expectEqualSlices(usize, proof.query_positions, sampled.unique);
    const answers = try allocator.alloc(QM31, sampled.unique.len);
    defer allocator.free(answers);
    for (answers, sampled.unique) |*answer, position| answer.* = values[position];

    var capture: core.fri.FriQueryCapture(Hasher) = undefined;
    try verifier.decommitWithQueryCapture(allocator, answers, sampled.raw, &capture);
    defer capture.deinit(allocator);
    try audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers);

    // These hostile edits leave the verifier's success result untouched.
    // The independent audit must reject the altered certificate.
    const first = &capture.layers[0];
    const saved_position = first.positions[0];
    first.positions[0] ^= 1;
    try std.testing.expectError(error.BadRawPosition,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    first.positions[0] = saved_position;

    const saved_value = first.values[0];
    first.values[0] = saved_value.add(QM31.one());
    if (audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers)) |_| {
        return error.AcceptedChangedSubset;
    } else |_| {}
    first.values[0] = saved_value;

    const saved_alpha = first.folding_alpha;
    first.folding_alpha = saved_alpha.add(QM31.one());
    try std.testing.expectError(error.BadLayerShape,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    first.folding_alpha = saved_alpha;

    if (capture.layers.len > 1) {
        const inner = &capture.layers[capture.layers.len - 1];
        const saved_inner_value = inner.values[0];
        inner.values[0] = saved_inner_value.add(QM31.one());
        if (audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers)) |_| {
            return error.AcceptedChangedInnerSubset;
        } else |_| {}
        inner.values[0] = saved_inner_value;
    }

    const saved_coefficient = verifier.last_layer_poly.coefficientsMut()[0];
    verifier.last_layer_poly.coefficientsMut()[0] = saved_coefficient.add(QM31.one());
    try std.testing.expectError(error.BadTerminalValue,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    verifier.last_layer_poly.coefficientsMut()[0] = saved_coefficient;
}

test "FRI raw-slot refinement audits varied native layer schedules" {
    const allocator = std.testing.allocator;
    for ([_]struct { log_size: u32, step: u32 }{
        .{ .log_size = 2, .step = 1 }, // no inner layer, repeated raw draws
        .{ .log_size = 3, .step = 1 }, // one inner layer
        .{ .log_size = 5, .step = 1 }, // three inner layers
        .{ .log_size = 5, .step = 2 }, // one wider inner layer
        .{ .log_size = 7, .step = 2 }, // two inner layers
        .{ .log_size = 8, .step = 3 }, // partial last inner fold
    }) |schedule| {
        try runSchedule(allocator, schedule.log_size, schedule.step);
    }
}
