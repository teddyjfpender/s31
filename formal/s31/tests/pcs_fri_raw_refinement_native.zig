//! Differential audit of native FRI captures for varied layer schedules.
//! This checks raw-slot transitions independently of the verifier's folding
//! helpers. It does not prove Merkle binding or Zig-to-Lean semantics.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const admission = @import("fri_capture_admission");

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
const Hasher = Profile.MerkleHasher;
const Channel = Profile.Channel;
const Verifier = core.fri.FriVerifier(Hasher, Profile);

fn emptyLayer(allocator: std.mem.Allocator, marker: u8) !core.fri.FriLayerProof(Hasher) {
    const witness = try allocator.alloc(QM31, 0);
    errdefer allocator.free(witness);
    const hashes = try allocator.alloc(Hasher.Hash, 0);
    return .{
        .fri_witness = witness,
        .decommitment = .{ .hash_witness = hashes },
        .commitment = [_]u8{marker} ** 32,
    };
}

// The proof shape is deliberately constructed independently of the prover:
// three distinct roots and two terminal coefficients make the transcript
// sequence observable. This only tests the pinned native commit path, not
// Fiat–Shamir independence or acceptance of an arbitrary Merkle opening.
test "FRI raw-slot refinement: native round roots, alphas and terminal have one transcript order" {
    const allocator = std.testing.allocator;
    var config = try core.fri.FriConfig.init(1, 1, 2);
    config.fold_step = 2;
    const inner = try allocator.alloc(core.fri.FriLayerProof(Hasher), 2);
    inner[0] = try emptyLayer(allocator, 2);
    inner[1] = try emptyLayer(allocator, 3);
    var proof = core.fri.FriProof(Hasher){
        .first_layer = try emptyLayer(allocator, 1),
        .inner_layers = inner,
        .last_layer_poly = core.poly.line.LinePoly.initOwned(try allocator.dupe(QM31, &.{
            QM31.fromU32Unchecked(11, 0, 0, 0),
            QM31.fromU32Unchecked(13, 0, 0, 0),
        })),
    };
    defer proof.deinit(allocator);

    var native_channel = Channel{};
    var verifier = try Verifier.commit(
        allocator, &native_channel, config, proof,
        core.fri.CirclePolyDegreeBound.init(6),
    );
    defer verifier.deinit(allocator);

    // A separate transcript replay gives an exact, byte-level order oracle.
    var expected_channel = Channel{};
    Profile.mixRoot(&expected_channel, proof.first_layer.commitment);
    const first_alpha = expected_channel.drawSecureFelt();
    try std.testing.expect(verifier.first_layer.folding_alpha.eql(first_alpha));
    try std.testing.expectEqual(@as(u32, 7), verifier.first_layer.column_commitment_domain.logSize());

    const expected_steps = [_]u32{ 2, 1 };
    const expected_logs = [_]u32{ 5, 3 };
    for (proof.inner_layers, verifier.inner_layers, 0..) |source, layer, i| {
        Profile.mixRoot(&expected_channel, source.commitment);
        const alpha = expected_channel.drawSecureFelt();
        try std.testing.expect(layer.folding_alpha.eql(alpha));
        try std.testing.expectEqual(expected_steps[i], layer.fold_step);
        try std.testing.expectEqual(expected_logs[i], layer.domain.logSize());
        try std.testing.expectEqualDeep(source.commitment, layer.proof.commitment);
    }
    try std.testing.expectEqual(@as(u32, 2), verifier.last_layer_domain.logSize());
    try std.testing.expectEqual(@as(usize, 2), verifier.last_layer_poly.len());
    for (proof.last_layer_poly.coefficients(), verifier.last_layer_poly.coefficients()) |source, copied| {
        try std.testing.expect(source.eql(copied));
    }
    const before_terminal_channel = expected_channel;
    expected_channel.mixFelts(proof.last_layer_poly.coefficients());
    try std.testing.expectEqualDeep(expected_channel.digestBytes(), native_channel.digestBytes());
    try std.testing.expectEqual(expected_channel.n_draws, native_channel.n_draws);

    // Both a root and a terminal-coefficient change must alter the transcript.
    var changed_root_channel = Channel{};
    Profile.mixRoot(&changed_root_channel, [_]u8{4} ** 32);
    _ = changed_root_channel.drawSecureFelt();
    for (proof.inner_layers) |source| {
        Profile.mixRoot(&changed_root_channel, source.commitment);
        _ = changed_root_channel.drawSecureFelt();
    }
    changed_root_channel.mixFelts(proof.last_layer_poly.coefficients());
    try std.testing.expect(!std.mem.eql(u8, &changed_root_channel.digestBytes(), &native_channel.digestBytes()));
    var changed_terminal_channel = before_terminal_channel;
    changed_terminal_channel.mixFelts(&.{
        QM31.fromU32Unchecked(11, 0, 0, 0),
        QM31.fromU32Unchecked(14, 0, 0, 0),
    });
    try std.testing.expect(!std.mem.eql(u8, &changed_terminal_channel.digestBytes(), &native_channel.digestBytes()));
}

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
    const raw_answers = try allocator.alloc(QM31, sampled.raw.len);
    defer allocator.free(raw_answers);
    for (raw_answers, sampled.raw) |*answer, position| answer.* = values[position];
    try admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
        capture, verifier.last_layer_poly.coefficients());

    const saved_raw_answer = raw_answers[0];
    raw_answers[0] = saved_raw_answer.add(QM31.one());
    try std.testing.expectError(error.InvalidFriCapture,
        admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
            capture, verifier.last_layer_poly.coefficients()));
    raw_answers[0] = saved_raw_answer;

    const saved_width = capture.layers[0].fold_width;
    capture.layers[0].fold_width += 1;
    try std.testing.expectError(error.InvalidFriCapture,
        admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
            capture, verifier.last_layer_poly.coefficients()));
    capture.layers[0].fold_width = saved_width;

    // These hostile edits leave the verifier's success result untouched.
    // The independent audit must reject the altered certificate.
    const first = &capture.layers[0];
    const saved_position = first.positions[0];
    first.positions[0] ^= 1;
    try std.testing.expectError(error.BadRawPosition,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    try std.testing.expectError(error.InvalidFriCapture,
        admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
            capture, verifier.last_layer_poly.coefficients()));
    first.positions[0] = saved_position;

    const saved_value = first.values[0];
    first.values[0] = saved_value.add(QM31.one());
    if (audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers)) |_| {
        return error.AcceptedChangedSubset;
    } else |_| {}
    try std.testing.expectError(error.InvalidFriCapture,
        admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
            capture, verifier.last_layer_poly.coefficients()));
    first.values[0] = saved_value;

    const saved_alpha = first.folding_alpha;
    first.folding_alpha = saved_alpha.add(QM31.one());
    try std.testing.expectError(error.BadLayerShape,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    // The admission checker deliberately has no independent transcript state.
    // Challenge custody is supplied by the successful verifier capture.
    first.folding_alpha = saved_alpha;

    if (capture.layers.len > 1) {
        const inner = &capture.layers[capture.layers.len - 1];
        const saved_inner_value = inner.values[0];
        inner.values[0] = saved_inner_value.add(QM31.one());
        if (audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers)) |_| {
            return error.AcceptedChangedInnerSubset;
        } else |_| {}
        try std.testing.expectError(error.InvalidFriCapture,
            admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
                capture, verifier.last_layer_poly.coefficients()));
        inner.values[0] = saved_inner_value;
    }

    const saved_coefficient = verifier.last_layer_poly.coefficientsMut()[0];
    verifier.last_layer_poly.coefficientsMut()[0] = saved_coefficient.add(QM31.one());
    try std.testing.expectError(error.BadTerminalValue,
        audit(allocator, &verifier, capture, sampled.raw, sampled.unique, answers));
    try std.testing.expectError(error.InvalidFriCapture,
        admission.validate(Hasher, allocator, config, sampled.raw, raw_answers,
            capture, verifier.last_layer_poly.coefficients()));
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

test "FRI raw-slot refinement independently evaluates terminal polynomial basis" {
    const allocator = std.testing.allocator;
    const base = struct {
        fn q(value: u32) QM31 {
            return QM31.fromU32Unchecked(value, 0, 0, 0);
        }
    }.q;
    const four = [_]QM31{ base(1), base(2), base(3), base(4) };
    const hand = try admission.evaluateTerminalPolynomial(
        allocator,
        &four,
        M31.fromCanonical(5),
    );
    // The lower pairs use 2*5^2-1=49, then the last pair uses 5.
    try std.testing.expect(hand.eql(base(1094)));
    try std.testing.expectError(error.InvalidFriCapture,
        admission.evaluateTerminalPolynomial(allocator, &.{}, M31.one()));
    try std.testing.expectError(error.InvalidFriCapture,
        admission.evaluateTerminalPolynomial(allocator, &.{ base(1), base(2), base(3) }, M31.one()));

    var prng = std.Random.DefaultPrng.init(0x7373_3131_f124_2026);
    const random = prng.random();
    for (0..7) |log_size| {
        const count = @as(usize, 1) << @intCast(log_size);
        const coefficients = try allocator.alloc(QM31, count);
        defer allocator.free(coefficients);
        for (coefficients) |*coefficient| {
            coefficient.* = QM31.fromU32Unchecked(
                random.intRangeLessThan(u32, 0, core.fields.m31.Modulus),
                random.intRangeLessThan(u32, 0, core.fields.m31.Modulus),
                random.intRangeLessThan(u32, 0, core.fields.m31.Modulus),
                random.intRangeLessThan(u32, 0, core.fields.m31.Modulus),
            );
        }
        var native = core.poly.line.LinePoly.initOwned(
            try allocator.dupe(QM31, coefficients),
        );
        defer native.deinit(allocator);
        for (0..8) |_| {
            const x = M31.fromCanonical(
                random.intRangeLessThan(u32, 0, core.fields.m31.Modulus),
            );
            const independently_evaluated = try admission.evaluateTerminalPolynomial(
                allocator, coefficients, x,
            );
            const verifier_evaluated = try native.evalAtPoint(allocator, QM31.fromBase(x));
            try std.testing.expect(independently_evaluated.eql(verifier_evaluated));
        }
    }
}

test "FRI raw-slot refinement every terminal basis coefficient uses the indexed doubling factors" {
    const allocator = std.testing.allocator;
    const selected = QM31.fromU32Unchecked(1, 2, 3, 4);
    const points = [_]M31{
        M31.zero(),
        M31.fromCanonical(5),
        M31.fromCanonical(core.fields.m31.Modulus - 1),
    };
    // A one-hot coefficient has a product basis value determined by the bits
    // of its native recursive index. This oracle neither calls the verifier's
    // pending-stack fold nor S31's adjacent-pair reduction.
    for (0..9) |log_size| {
        const count = @as(usize, 1) << @intCast(log_size);
        const coefficients = try allocator.alloc(QM31, count);
        defer allocator.free(coefficients);
        for (0..count) |basis_index| {
            @memset(coefficients, QM31.zero());
            coefficients[basis_index] = selected;
            var native = core.poly.line.LinePoly.initOwned(
                try allocator.dupe(QM31, coefficients),
            );
            defer native.deinit(allocator);
            for (points) |x| {
                var expected = selected;
                var doubled = QM31.fromBase(x);
                for (0..log_size) |level| {
                    const index_bit = log_size - 1 - level;
                    if (((basis_index >> @intCast(index_bit)) & 1) == 1)
                        expected = expected.mul(doubled);
                    doubled = core.circle.CirclePoint(QM31).doubleX(doubled);
                }
                const verifier_value = try native.evalAtPoint(allocator, QM31.fromBase(x));
                const capture_value = try admission.evaluateTerminalPolynomial(
                    allocator, coefficients, x,
                );
                try std.testing.expect(verifier_value.eql(expected));
                try std.testing.expect(capture_value.eql(expected));
            }
        }
    }
}
