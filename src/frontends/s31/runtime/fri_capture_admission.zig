//! S31 capture admission after the native PCS verifier succeeds.
//!
//! This independently replays each raw FRI query through captured subsets and
//! the algebraic pair fold before recursive witness conversion. It checks
//! operational consistency of the published capture, not Merkle binding or
//! FRI proximity. The terminal evaluator is the same native LinePoly routine.
const std = @import("std");
const core = @import("stwo_core");

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const CircleDomain = core.poly.circle.domain.CircleDomain;
const LineDomain = core.poly.line.LineDomain;

fn pair(alpha: QM31, coordinate: M31, left: QM31, right: QM31) !QM31 {
    const inverse = try coordinate.inv();
    return left.add(right).add(alpha.mul(left.sub(right).mulM31(inverse)));
}

fn foldLine(
    allocator: std.mem.Allocator,
    values: []const QM31,
    initial_domain: LineDomain,
    alpha: QM31,
    steps: u32,
) !QM31 {
    if (steps == 0 or steps >= @bitSizeOf(usize) or
        values.len != (@as(usize, 1) << @intCast(steps)))
        return error.InvalidFriCapture;
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
            scratch[i] = try pair(
                challenge,
                domain.at(point_index),
                scratch[2 * i],
                scratch[2 * i + 1],
            );
        }
        length = half;
        domain = domain.double();
    }
    return scratch[0];
}

fn foldCircle(
    allocator: std.mem.Allocator,
    values: []const QM31,
    source_domain: CircleDomain,
    subset_start: usize,
    alpha: QM31,
    steps: u32,
) !QM31 {
    if (steps == 0 or steps >= @bitSizeOf(usize) or
        values.len != (@as(usize, 1) << @intCast(steps)))
        return error.InvalidFriCapture;
    const initial_index = core.utils.bitReverseIndex(subset_start, source_domain.logSize());
    const fold_initial = source_domain.indexAt(initial_index);
    const fold_domain = CircleDomain.new(core.circle.Coset.new(fold_initial, steps - 1));
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
    return foldLine(
        allocator,
        first,
        LineDomain.fromCircleDomain(fold_domain),
        alpha.square(),
        steps - 1,
    );
}

/// Check an already verified FRI capture in exact raw transcript order.
/// Success ensures the published arrays form an operational FRI path for every
/// raw slot. It does not authenticate them against a committed oracle by itself.
pub fn validate(
    comptime H: type,
    allocator: std.mem.Allocator,
    config: core.fri.FriConfig,
    raw: []const usize,
    deep_answers: []const QM31,
    captured: core.fri.FriQueryCapture(H),
    coefficients: []const QM31,
) !void {
    if (captured.layers.len == 0 or raw.len != deep_answers.len or
        raw.len != config.n_queries or
        config.fold_step == 0 or config.log_blowup_factor == 0 or
        coefficients.len == 0 or !std.math.isPowerOfTwo(coefficients.len) or
        config.log_last_layer_degree_bound >= @bitSizeOf(usize))
        return error.InvalidFriCapture;
    if (coefficients.len > (@as(usize, 1) << @intCast(config.log_last_layer_degree_bound)))
        return error.InvalidFriCapture;

    const first = captured.layers[0];
    const source_log = std.math.add(u32, first.path_depth, first.fold_step) catch
        return error.InvalidFriCapture;
    if (first.fold_step != config.fold_step or
        source_log > core.circle.M31_CIRCLE_LOG_ORDER or
        source_log < config.log_blowup_factor + first.fold_step or
        source_log - config.log_blowup_factor - first.fold_step <
            config.log_last_layer_degree_bound)
        return error.InvalidFriCapture;
    var remaining = source_log - config.log_blowup_factor -
        first.fold_step - config.log_last_layer_degree_bound;
    if (captured.layers.len != 1 + core.fri.nFoldSteps(remaining, config.fold_step))
        return error.InvalidFriCapture;

    const circle_domain = core.poly.circle.canonic.CanonicCoset.new(source_log).circleDomain();
    const initial_line_domain = try LineDomain.init(
        core.circle.Coset.halfOdds(source_log - first.fold_step),
    );
    var layer_log = source_log;
    for (captured.layers, 0..) |layer, layer_index| {
        const expected_step = if (layer_index == 0)
            config.fold_step
        else
            core.fri.foldStepAt(config.fold_step, remaining);
        if (layer_index != 0) remaining -= expected_step;
        if (expected_step == 0 or expected_step >= @bitSizeOf(usize) or
            expected_step > layer_log)
            return error.InvalidFriCapture;
        const width = @as(usize, 1) << @intCast(expected_step);
        const expected_values = std.math.mul(usize, raw.len, width) catch
            return error.InvalidFriCapture;
        const next_log = layer_log - expected_step;
        if (layer.fold_step != expected_step or layer.fold_width != width or
            layer.path_depth != next_log or layer.query_count != raw.len or
            layer.positions.len != raw.len or layer.values.len != expected_values)
            return error.InvalidFriCapture;
        layer_log = next_log;

        // Merged and duplicate raw slots must present one identical subset.
        for (layer.positions, 0..) |position, i| {
            if (position >= (@as(usize, 1) << @intCast(layer_log + expected_step)))
                return error.InvalidFriCapture;
            for (layer.positions[0..i], 0..) |prior, j| {
                if ((prior >> @intCast(expected_step)) !=
                    (position >> @intCast(expected_step))) continue;
                for (layer.queryValues(i), layer.queryValues(j)) |left, right| {
                    if (!left.eql(right)) return error.InvalidFriCapture;
                }
            }
        }
    }
    if (remaining != 0 or layer_log !=
        config.log_last_layer_degree_bound + config.log_blowup_factor)
        return error.InvalidFriCapture;

    var polynomial = core.poly.line.LinePoly.initOwned(
        try allocator.dupe(QM31, coefficients),
    );
    defer polynomial.deinit(allocator);
    for (raw, deep_answers, 0..) |initial_position, first_value, slot| {
        var position = initial_position;
        var current = first_value;
        var line_domain = initial_line_domain;
        for (captured.layers, 0..) |layer, layer_index| {
            if (position != layer.positions[slot]) return error.InvalidFriCapture;
            const width: usize = @intCast(layer.fold_width);
            const subset = layer.queryValues(slot);
            if (!current.eql(subset[position % width])) return error.InvalidFriCapture;
            const step = layer.fold_step;
            const subset_start = (position >> @intCast(step)) << @intCast(step);
            current = if (layer_index == 0)
                try foldCircle(allocator, subset, circle_domain, subset_start,
                    layer.folding_alpha, step)
            else
                try foldLineAtSubset(allocator, subset, line_domain, subset_start,
                    layer.folding_alpha, step);
            position >>= @intCast(step);
            if (layer_index != 0) {
                for (0..step) |_| line_domain = line_domain.double();
            }
        }
        if (position >= line_domain.size()) return error.InvalidFriCapture;
        const x = line_domain.at(core.utils.bitReverseIndex(
            position, line_domain.logSize(),
        ));
        const expected = try polynomial.evalAtPoint(allocator, QM31.fromBase(x));
        if (!current.eql(expected)) return error.InvalidFriCapture;
    }
}

fn foldLineAtSubset(
    allocator: std.mem.Allocator,
    values: []const QM31,
    source_domain: LineDomain,
    subset_start: usize,
    alpha: QM31,
    steps: u32,
) !QM31 {
    const initial_index = core.utils.bitReverseIndex(subset_start, source_domain.logSize());
    const fold_initial = source_domain.coset().indexAt(initial_index);
    const domain = try LineDomain.init(core.circle.Coset.new(fold_initial, steps));
    return foldLine(allocator, values, domain, alpha, steps);
}
