//! Source-only admission for the bounded tagged square/add-chip profile.
//!
//! This plan alone cannot authorize a proof. The mixed verifier reconstructs
//! scalar endpoint addresses, live AIR handles and the component manifest
//! from its embedded source before accepting native proof bytes.
const std = @import("std");
const relation = @import("relation.zig");
const canonical = @import("canonical.zig");
const P = @import("stwo_core").fields.m31.Modulus;

pub const max_calls: usize = 8;
pub const max_source_bytes: usize = 1 << 20;
pub const max_ir_nodes: usize = 1 << 16;
pub const max_total_rounds: u32 = 1 << 18;

pub const Call = struct {
    call_id: u32,
    source_node_id: u32,
    input_node_id: u32,
    rounds: u32,
    constant: u32,
};

const empty_call: Call = .{
    .call_id = 0,
    .source_node_id = 0,
    .input_node_id = 0,
    .rounds = 0,
    .constant = 0,
};

pub const Plan = struct {
    canonical_ir_sha256: [32]u8,
    calls: [max_calls]Call = [_]Call{empty_call} ** max_calls,
    call_count: usize = 0,
    public_output_ids: [8]u32 = [_]u32{0} ** 8,
    public_output_count: usize = 0,
    total_rounds: u32 = 0,

    pub fn callSlice(self: *const Plan) []const Call {
        return self.calls[0..self.call_count];
    }
};

/// The byte cap precedes JSON parsing. This returns no witness and no circuit
/// addresses. A released verifier still needs an authenticated source root.
pub fn extractSource(allocator: std.mem.Allocator, bytes: []const u8) !Plan {
    if (bytes.len > max_source_bytes) return error.ManyCallSourceTooLarge;
    var parsed = try relation.parseProgram(allocator, bytes);
    defer parsed.deinit();
    return extract(allocator, parsed.value);
}

/// Restrict source syntax before canonicalization, then require one distinct
/// canonical repeat per source repeat. Canonical IR may fold or merge nodes;
/// silently assigning two call IDs to one surviving repeat is forbidden.
pub fn extract(allocator: std.mem.Allocator, program: relation.Program) !Plan {
    if ((program.version != 1 and program.version != 2) or program.proof_mode != .transparent or
        (program.version == 1 and program.public_abi != null) or
        (program.version == 2 and program.public_abi == null) or
        program.assertions.len != 0 or
        program.inputs.len == 0 or program.public_outputs.len == 0 or
        program.public_outputs.len > 8)
        return error.UnsupportedManyCallSource;
    // The v2 mixed statement has exactly eight public M31 words. Admit a
    // single public four-lane input and one derived four-lane output until
    // the native proof/record binding has been exercised for wider shapes.
    if (program.version == 2 and (program.inputs.len != 1 or
        program.inputs[0].visibility != .public or
        program.public_outputs.len != 1))
        return error.UnsupportedManyCallSource;
    var scalar_selectors: usize = 0;
    for (program.inputs) |input| {
        if ((program.version == 1 and input.visibility != .private) or
            input.kind != .m31 or
            (input.length != 4 and (program.version != 1 or input.length != 1)))
            return error.UnsupportedManyCallSource;
        if (input.length == 1) scalar_selectors += 1;
    }
    // Keep the scalar selector ABI small while its source-to-chip coverage is
    // limited to one conditional feeder. A dead selector is rejected below.
    if (scalar_selectors > 1) return error.UnsupportedManyCallSource;

    var source_repeat_names: [max_calls][]const u8 = undefined;
    var source_repeat_count: usize = 0;
    for (program.nodes) |node| switch (node.op) {
        .repeat => {
            if (source_repeat_count == max_calls) return error.TooManyChipCalls;
            source_repeat_names[source_repeat_count] = node.name;
            source_repeat_count += 1;
        },
        .add, .mul, .add_const, .mul_const, .sum_lanes, .select => {},
        else => return error.UnsupportedManyCallNode,
    };
    if (source_repeat_count == 0) return error.NoChipCalls;

    var ir = try canonical.build(allocator, program);
    defer ir.deinit();
    if (ir.nodes.len > max_ir_nodes) return error.ManyCallCircuitTooLarge;
    const live = try allocator.alloc(bool, ir.nodes.len);
    defer allocator.free(live);
    @memset(live, false);
    const from_call = try allocator.alloc(bool, ir.nodes.len);
    defer allocator.free(from_call);
    @memset(from_call, false);

    var plan: Plan = .{ .canonical_ir_sha256 = ir.sha256 };
    for (ir.nodes, 0..) |node, index| {
        if (node.tag == .select) {
            const selector = node.selector orelse return error.UnsupportedChipSelector;
            if (node.kind != .m31 or node.length != 4 or selector >= index or
                ir.nodes[selector].tag != .input or ir.nodes[selector].kind != .m31 or
                ir.nodes[selector].length != 1 or ir.nodes[selector].visibility.? != .private)
                return error.UnsupportedChipSelector;
        }
        if (node.tag == .repeat) {
            if (plan.call_count == source_repeat_count) return error.NoncanonicalChipCalls;
            const body = node.body orelse return error.UnsupportedChipBody;
            const rounds = node.rounds orelse return error.UnsupportedChipRounds;
            if (node.kind != .m31 or node.length != 4 or
                rounds < 16 or rounds > 32768 or !std.math.isPowerOfTwo(rounds))
                return error.UnsupportedChipRounds;
            if (body.len != 2 or body[0].op != .square or body[0].constant != null or
                body[1].op != .add_const or body[1].constant == null or
                body[1].constant.? >= P)
                return error.UnsupportedChipBody;
            const input_id = node.lhs orelse return error.UnsupportedChipInput;
            if (input_id >= index or ir.nodes[input_id].kind != .m31 or ir.nodes[input_id].length != 4)
                return error.UnsupportedChipInput;
            // Only these circuit nodes may feed a chip. The bounded compiler
            // extracts their packed M31 coordinates into constrained scalar
            // Gate producers before recording endpoints. Select uses a
            // Boolean selector constrained by the direct circuit compiler.
            switch (ir.nodes[input_id].tag) {
                .input, .repeat, .add, .mul, .add_const, .mul_const, .select => {},
                else => return error.UnsupportedChipInput,
            }
            const source_id = sourceId(&ir, source_repeat_names[plan.call_count]) orelse
                return error.NoncanonicalChipCalls;
            if (source_id != index) return error.NoncanonicalChipCalls;
            plan.total_rounds = std.math.add(u32, plan.total_rounds, rounds) catch return error.TooManyChipRounds;
            if (plan.total_rounds > max_total_rounds) return error.TooManyChipRounds;
            plan.calls[plan.call_count] = .{
                .call_id = @intCast(plan.call_count),
                .source_node_id = @intCast(index),
                .input_node_id = input_id,
                .rounds = rounds,
                .constant = body[1].constant.?,
            };
            plan.call_count += 1;
        }
        from_call[index] = node.tag == .repeat or
            (if (node.lhs) |id| from_call[id] else false) or
            (if (node.rhs) |id| from_call[id] else false);
    }
    if (plan.call_count != source_repeat_count) return error.NoncanonicalChipCalls;

    for (ir.public_outputs) |output| {
        if (output.id >= ir.nodes.len) return error.InvalidManyCallOutput;
        const tag = ir.nodes[output.id].tag;
        if (tag == .input or tag == .repeat or !from_call[output.id])
            return error.InvalidManyCallOutput;
        plan.public_output_ids[plan.public_output_count] = output.id;
        plan.public_output_count += 1;
        live[output.id] = true;
    }
    if (program.version == 2 and
        (ir.public_outputs.len != 1 or ir.nodes[ir.public_outputs[0].id].length != 4))
        return error.UnsupportedManyCallSource;
    for (0..ir.nodes.len) |reverse| {
        const id = ir.nodes.len - 1 - reverse;
        if (!live[id]) continue;
        const node = ir.nodes[id];
        if (node.lhs) |lhs| live[lhs] = true;
        if (node.rhs) |rhs| live[rhs] = true;
        if (node.selector) |selector| live[selector] = true;
    }
    for (plan.callSlice()) |call|
        if (!live[call.source_node_id]) return error.DeadChipCall;
    for (ir.nodes, 0..) |node, id| {
        if (node.tag == .input and !live[id]) return error.DeadChipInput;
        if (node.tag != .input or node.length != 1) continue;
        const input_id: u32 = @intCast(id);
        var used_as_selector = false;
        for (ir.nodes, 0..) |consumer, consumer_id| {
            if (!live[consumer_id]) continue;
            if (consumer.lhs == input_id or consumer.rhs == input_id)
                return error.UnsupportedChipSelector;
            if (consumer.selector == input_id) {
                if (consumer.tag != .select) return error.UnsupportedChipSelector;
                used_as_selector = true;
            }
        }
        if (!used_as_selector) return error.UnsupportedChipSelector;
    }
    return plan;
}

fn sourceId(ir: *const canonical.IR, name: []const u8) ?u32 {
    for (ir.source_map) |entry|
        if (std.mem.eql(u8, entry.name, name)) return entry.id;
    return null;
}

fn chainProgram(allocator: std.mem.Allocator, n: usize, steps: []relation.Step) !relation.Program {
    const inputs = try allocator.alloc(relation.Input, 1);
    inputs[0] = .{ .name = "x", .kind = .m31, .length = 4, .visibility = .private };
    const nodes = try allocator.alloc(relation.Node, n + 1);
    var previous: []const u8 = "x";
    for (nodes[0..n], 0..) |*node, i| {
        const name = try std.fmt.allocPrint(allocator, "r{d}", .{i});
        node.* = .{ .name = name, .op = .repeat, .lhs = previous, .rounds = 16, .body = steps };
        previous = name;
    }
    nodes[n] = .{ .name = "total", .op = .sum_lanes, .lhs = previous };
    const outputs = try allocator.alloc([]const u8, 1);
    outputs[0] = "total";
    return .{
        .version = 1,
        .name = "bounded_chain",
        .inputs = inputs,
        .nodes = nodes,
        .assertions = &.{},
        .public_outputs = outputs,
    };
}

test "one, eight, and nine dependent calls have canonical admission bounds" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    const one = try extract(a, try chainProgram(a, 1, &steps));
    try std.testing.expectEqual(@as(usize, 1), one.call_count);
    try std.testing.expectEqual(@as(u32, 0), one.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 16), one.total_rounds);
    const eight = try extract(a, try chainProgram(a, 8, &steps));
    try std.testing.expectEqual(@as(usize, 8), eight.call_count);
    try std.testing.expectEqual(@as(u32, 7), eight.calls[7].call_id);
    for (eight.callSlice()[1..], 1..) |call, i|
        try std.testing.expectEqual(eight.calls[i - 1].source_node_id, call.input_node_id);
    try std.testing.expectError(error.TooManyChipCalls, extract(a, try chainProgram(a, 9, &steps)));
}

test "normalized three-call source preserves independent and dependent call IDs" {
    const source =
        \\{"version":1,"name":"three_calls","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"},{"name":"y","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"a","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":3}]},{"name":"b","op":"repeat","lhs":"y","rounds":32,"body":[{"op":"square"},{"op":"add_const","constant":5}]},{"name":"c","op":"repeat","lhs":"a","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":7}]},{"name":"joined","op":"add","lhs":"b","rhs":"c"},{"name":"total","op":"sum_lanes","lhs":"joined"}],"assertions":[],"public_outputs":["total"]}
    ;
    const plan = try extractSource(std.testing.allocator, source);
    try std.testing.expectEqual(@as(usize, 3), plan.call_count);
    try std.testing.expectEqual(@as(u32, 64), plan.total_rounds);
    try std.testing.expectEqual(@as(u32, 0), plan.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 1), plan.calls[1].call_id);
    try std.testing.expectEqual(@as(u32, 2), plan.calls[2].call_id);
    try std.testing.expectEqual(plan.calls[0].source_node_id, plan.calls[2].input_node_id);
    try std.testing.expect(plan.calls[0].input_node_id != plan.calls[1].input_node_id);
    try std.testing.expectEqual(@as(usize, 1), plan.public_output_count);
}

test "dead, merged, and publicly exposed repeat endpoints are rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    var two = try chainProgram(a, 2, &steps);
    two.nodes[1].lhs = "x";
    try std.testing.expectError(error.NoncanonicalChipCalls, extract(a, two));
    var different_steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 17 } };
    two.nodes[1].body = &different_steps;
    try std.testing.expectError(error.DeadChipCall, extract(a, two));
    two.public_outputs[0] = "r0";
    try std.testing.expectError(error.InvalidManyCallOutput, extract(a, two));
}

test "unsupported chip bodies, rounds, and public inputs fail closed" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    var one = try chainProgram(a, 1, &steps);
    one.nodes[0].rounds = 8;
    try std.testing.expectError(error.UnsupportedChipRounds, extract(a, one));
    one.nodes[0].rounds = 16;
    var reversed_steps = [_]relation.Step{ .{ .op = .add_const, .constant = 13 }, .{ .op = .square } };
    one.nodes[0].body = &reversed_steps;
    try std.testing.expectError(error.UnsupportedChipBody, extract(a, one));
    one.nodes[0].body = &steps;
    one.inputs[0].visibility = .public;
    try std.testing.expectError(error.UnsupportedManyCallSource, extract(a, one));
}

test "repeat after four-lane arithmetic has a canonical chip input" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    var two = try chainProgram(a, 2, &steps);
    const widened = try a.alloc(relation.Node, 4);
    widened[0] = two.nodes[0];
    widened[1] = .{ .name = "shifted", .op = .add_const, .lhs = "r0", .constant = 3 };
    widened[2] = two.nodes[1];
    widened[2].lhs = "shifted";
    widened[3] = two.nodes[2];
    two.nodes = widened;
    const plan = try extract(a, two);
    try std.testing.expectEqual(@as(usize, 2), plan.call_count);
    var ir = try canonical.build(a, two);
    defer ir.deinit();
    try std.testing.expectEqual(canonical.Tag.add_const, ir.nodes[plan.calls[1].input_node_id].tag);
}

test "arithmetic-fed calls may share one live circuit result" {
    const a = std.testing.allocator;
    var parsed = try relation.parseProgram(a, @embedFile("../examples/boundary/private_arithmetic_chip_fork.s31.json"));
    defer parsed.deinit();
    const plan = try extract(a, parsed.value);
    try std.testing.expectEqual(@as(usize, 3), plan.call_count);
    try std.testing.expectEqual(plan.calls[1].input_node_id, plan.calls[2].input_node_id);
    try std.testing.expect(plan.calls[1].source_node_id != plan.calls[2].source_node_id);
}

test "a private scalar bit selects a live four-lane chip feeder" {
    const source =
        \\{"version":1,"name":"selected_feeder","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"},{"name":"y","kind":"m31","length":4,"visibility":"private"},{"name":"bit","kind":"m31","length":1,"visibility":"private"}],"nodes":[{"name":"a","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},{"name":"left","op":"add","lhs":"a","rhs":"x"},{"name":"right","op":"mul","lhs":"a","rhs":"y"},{"name":"chosen","op":"select","selector":"bit","lhs":"left","rhs":"right"},{"name":"b","op":"repeat","lhs":"chosen","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":17}]},{"name":"sum","op":"add","lhs":"b","rhs":"a"},{"name":"product","op":"mul","lhs":"b","rhs":"y"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    var parsed = try relation.parseProgram(std.testing.allocator, source);
    defer parsed.deinit();
    const plan = try extract(std.testing.allocator, parsed.value);
    try std.testing.expectEqual(@as(usize, 2), plan.call_count);
    var ir = try canonical.build(std.testing.allocator, parsed.value);
    defer ir.deinit();
    const selected = ir.nodes[plan.calls[1].input_node_id];
    try std.testing.expectEqual(canonical.Tag.select, selected.tag);
    try std.testing.expectEqual(canonical.Tag.input, ir.nodes[selected.selector.?].tag);
    try std.testing.expectEqual(@as(u32, 1), ir.nodes[selected.selector.?].length);

    // A private scalar is admitted only as a live Boolean selector.
    parsed.value.nodes[3].selector = "x";
    try std.testing.expectError(error.InvalidNode, extract(std.testing.allocator, parsed.value));
    parsed.value.nodes[3].selector = "bit";
    const original_inputs = parsed.value.inputs;
    var with_dead = [_]relation.Input{ original_inputs[0], original_inputs[1], original_inputs[2], .{ .name = "dead", .kind = .m31, .length = 4, .visibility = .private } };
    parsed.value.inputs = &with_dead;
    try std.testing.expectError(error.DeadChipInput, extract(std.testing.allocator, parsed.value));
    parsed.value.inputs = original_inputs;
}

test "a live private scalar used as arithmetic is not a selector" {
    const source =
        \\{"version":1,"name":"scalar_nonselector","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"},{"name":"bit","kind":"m31","length":1,"visibility":"private"}],"nodes":[{"name":"a","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},{"name":"scalar","op":"sum_lanes","lhs":"a"},{"name":"claimed","op":"add","lhs":"scalar","rhs":"bit"}],"assertions":[],"public_outputs":["claimed"]}
    ;
    try std.testing.expectError(error.UnsupportedChipSelector, extractSource(std.testing.allocator, source));
}

test "source byte cap rejects before JSON parsing" {
    const too_large = try std.testing.allocator.alloc(u8, max_source_bytes + 1);
    defer std.testing.allocator.free(too_large);
    @memset(too_large, 'x');
    try std.testing.expectError(error.ManyCallSourceTooLarge, extractSource(std.testing.allocator, too_large));
}

test "record ABI v2 mixed admission has one public input and one derived result" {
    const a = std.testing.allocator;
    var parsed = try relation.parseProgram(a, @embedFile("../examples/boundary/record_mixed1.s31.json"));
    defer parsed.deinit();
    const plan = try extract(a, parsed.value);
    try std.testing.expectEqual(@as(usize, 1), plan.call_count);
    try std.testing.expectEqual(@as(usize, 1), plan.public_output_count);

    parsed.value.inputs[0].visibility = .private;
    try std.testing.expectError(error.UnsupportedManyCallSource, extract(a, parsed.value));
    parsed.value.inputs[0].visibility = .public;

    const original_inputs = parsed.value.inputs;
    var extra_inputs = [_]relation.Input{ original_inputs[0], original_inputs[0] };
    parsed.value.inputs = &extra_inputs;
    try std.testing.expectError(error.UnsupportedManyCallSource, extract(a, parsed.value));
    parsed.value.inputs = original_inputs;

    const original_outputs = parsed.value.public_outputs;
    var extra_outputs = [_][]const u8{ original_outputs[0], original_outputs[0] };
    parsed.value.public_outputs = &extra_outputs;
    try std.testing.expectError(error.UnsupportedManyCallSource, extract(a, parsed.value));
    parsed.value.public_outputs = original_outputs;

    const original_abi = parsed.value.public_abi;
    parsed.value.public_abi = null;
    try std.testing.expectError(error.UnsupportedManyCallSource, extract(a, parsed.value));
    parsed.value.public_abi = original_abi;
}
