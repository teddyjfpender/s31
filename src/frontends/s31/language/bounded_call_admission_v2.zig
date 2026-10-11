//! Source-only V2 admission for heterogeneous bounded tagged-chip calls.
//!
//! This file is deliberately not exported from `mod.zig` or connected to any
//! proof path. It identifies live, canonical square/add and
//! square/add/mix4 repeats. A later compiler must derive and compare their
//! actual circuit endpoint addresses in both value and topology modes.
//! Neither this plan nor its canonical IR digest authorizes proof bytes.
const std = @import("std");
const relation = @import("relation.zig");
const canonical = @import("canonical.zig");
const P = @import("stwo_core").fields.m31.Modulus;

pub const max_calls: usize = 8;
pub const max_source_bytes: usize = 1 << 20;
pub const max_ir_nodes: usize = 1 << 16;
pub const max_total_rounds: u32 = 1 << 18;
pub const max_public_output_words: u32 = 9;

/// Distinct AIR constructors and lookup relation IDs are required for these
/// two transitions. This tag is source metadata only until a native profile
/// authenticates a typed component roster.
pub const Kind = enum(u8) { square_add = 1, square_add_mix4 = 2 };

pub const Call = struct {
    kind: Kind,
    call_id: u32,
    source_node_id: u32,
    input_node_id: u32,
    rounds: u32,
    constant: u32,
};

const empty_call: Call = .{
    .kind = .square_add,
    .call_id = 0,
    .source_node_id = 0,
    .input_node_id = 0,
    .rounds = 0,
    .constant = 0,
};

pub const Plan = struct {
    schema_version: u32 = 2,
    canonical_ir_sha256: [32]u8,
    calls: [max_calls]Call = [_]Call{empty_call} ** max_calls,
    call_count: usize = 0,
    public_output_ids: [8]u32 = [_]u32{0} ** 8,
    public_output_count: usize = 0,
    public_output_word_count: u32 = 0,
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
    if (program.version != 1 or program.proof_mode != .transparent or
        program.public_abi != null or program.assertions.len != 0 or
        program.inputs.len == 0 or program.inputs.len > max_calls or
        program.public_outputs.len == 0 or
        program.public_outputs.len > 8)
        return error.UnsupportedManyCallSource;
    for (program.inputs) |input| {
        if (input.visibility != .private or input.kind != .m31 or input.length != 4)
            return error.UnsupportedManyCallSource;
    }

    var source_repeat_names: [max_calls][]const u8 = undefined;
    var source_repeat_count: usize = 0;
    for (program.nodes) |node| switch (node.op) {
        .repeat => {
            if (source_repeat_count == max_calls) return error.TooManyChipCalls;
            source_repeat_names[source_repeat_count] = node.name;
            source_repeat_count += 1;
        },
        .add, .mul, .add_const, .mul_const, .sum_lanes => {},
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
        if (node.tag == .repeat) {
            if (plan.call_count == source_repeat_count) return error.NoncanonicalChipCalls;
            const body = node.body orelse return error.UnsupportedChipBody;
            const rounds = node.rounds orelse return error.UnsupportedChipRounds;
            if (node.kind != .m31 or node.length != 4 or
                rounds < 16 or rounds > 32768 or !std.math.isPowerOfTwo(rounds))
                return error.UnsupportedChipRounds;
            if ((body.len != 2 and body.len != 3) or
                body[0].op != .square or body[0].constant != null or
                body[1].op != .add_const or body[1].constant == null or
                body[1].constant.? >= P)
                return error.UnsupportedChipBody;
            const kind: Kind = if (body.len == 2) .square_add else blk: {
                if (body[2].op != .mix4 or body[2].constant != null)
                    return error.UnsupportedChipBody;
                break :blk .square_add_mix4;
            };
            const input_id = node.lhs orelse return error.UnsupportedChipInput;
            if (input_id >= index or ir.nodes[input_id].kind != .m31 or ir.nodes[input_id].length != 4)
                return error.UnsupportedChipInput;
            // The current direct compiler records scalar endpoint addresses
            // only for private inputs and earlier chip outputs. Arithmetic
            // nodes have packed lanes but no `raw` scalar address array.
            // Admit those inputs only after a constrained unpacking path is
            // implemented and the value/topology maps are checked again.
            if (ir.nodes[input_id].tag != .input and ir.nodes[input_id].tag != .repeat)
                return error.UnsupportedChipInput;
            const source_id = sourceId(&ir, source_repeat_names[plan.call_count]) orelse
                return error.NoncanonicalChipCalls;
            if (source_id != index) return error.NoncanonicalChipCalls;
            plan.total_rounds = std.math.add(u32, plan.total_rounds, rounds) catch return error.TooManyChipRounds;
            if (plan.total_rounds > max_total_rounds) return error.TooManyChipRounds;
            plan.calls[plan.call_count] = .{
                .kind = kind,
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
        const result = ir.nodes[output.id];
        const tag = result.tag;
        if (tag == .input or tag == .repeat or !from_call[output.id])
            return error.InvalidManyCallOutput;
        plan.public_output_word_count = std.math.add(u32, plan.public_output_word_count, result.length) catch
            return error.TooManyPublicOutputWords;
        if (plan.public_output_word_count > max_public_output_words)
            return error.TooManyPublicOutputWords;
        plan.public_output_ids[plan.public_output_count] = output.id;
        plan.public_output_count += 1;
        live[output.id] = true;
    }
    for (0..ir.nodes.len) |reverse| {
        const id = ir.nodes.len - 1 - reverse;
        if (!live[id]) continue;
        const node = ir.nodes[id];
        if (node.lhs) |lhs| live[lhs] = true;
        if (node.rhs) |rhs| live[rhs] = true;
    }
    for (plan.callSlice()) |call|
        if (!live[call.source_node_id]) return error.DeadChipCall;
    // An unused private input would make source ABI shape depend on a value
    // that contributes to no public result. Reject it at this strict source
    // admission boundary instead of silently carrying a dead endpoint.
    for (ir.nodes, 0..) |node, id|
        if (node.tag == .input and !live[id]) return error.DeadChipInput;
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
    try std.testing.expectEqual(@as(u32, 2), one.schema_version);
    try std.testing.expectEqual(Kind.square_add, one.calls[0].kind);
    try std.testing.expectEqual(@as(u32, 0), one.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 16), one.total_rounds);
    const eight = try extract(a, try chainProgram(a, 8, &steps));
    try std.testing.expectEqual(@as(usize, 8), eight.call_count);
    try std.testing.expectEqual(@as(u32, 1), eight.public_output_word_count);
    try std.testing.expectEqual(@as(u32, 7), eight.calls[7].call_id);
    for (eight.callSlice()[1..], 1..) |call, i|
        try std.testing.expectEqual(eight.calls[i - 1].source_node_id, call.input_node_id);
    try std.testing.expectError(error.TooManyChipCalls, extract(a, try chainProgram(a, 9, &steps)));
}

test "heterogeneous repeat chain has distinct canonical kind and source IDs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var plain = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    var coupled = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 7 }, .{ .op = .mix4 } };
    const program = try chainProgram(a, 3, &plain);
    program.nodes[1].body = &coupled;
    const plan = try extract(a, program);
    try std.testing.expectEqual(@as(usize, 3), plan.call_count);
    try std.testing.expectEqual(Kind.square_add, plan.calls[0].kind);
    try std.testing.expectEqual(Kind.square_add_mix4, plan.calls[1].kind);
    try std.testing.expectEqual(Kind.square_add, plan.calls[2].kind);
    try std.testing.expectEqual(@as(u32, 7), plan.calls[1].constant);
    try std.testing.expectEqual(plan.calls[0].source_node_id, plan.calls[1].input_node_id);
    try std.testing.expectEqual(plan.calls[1].source_node_id, plan.calls[2].input_node_id);
    try std.testing.expect(plan.calls[0].source_node_id < plan.calls[1].source_node_id);
    try std.testing.expect(plan.calls[1].source_node_id < plan.calls[2].source_node_id);
    const v1 = @import("bounded_call_admission.zig");
    try std.testing.expectError(error.UnsupportedChipBody, v1.extract(a, program));
}

test "literal normalized mix4 source derives one coupled call" {
    const source =
        \\{"version":1,"name":"coupled_once","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"mixed","op":"repeat","lhs":"x","rounds":32,"body":[{"op":"square"},{"op":"add_const","constant":7},{"op":"mix4"}]},{"name":"claimed","op":"sum_lanes","lhs":"mixed"}],"assertions":[],"public_outputs":["claimed"]}
    ;
    const plan = try extractSource(std.testing.allocator, source);
    try std.testing.expectEqual(@as(usize, 1), plan.call_count);
    try std.testing.expectEqual(Kind.square_add_mix4, plan.calls[0].kind);
    try std.testing.expectEqual(@as(u32, 0), plan.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 0), plan.calls[0].input_node_id);
    try std.testing.expectEqual(@as(u32, 1), plan.calls[0].source_node_id);
    try std.testing.expectEqual(@as(u32, 32), plan.calls[0].rounds);
    try std.testing.expectEqual(@as(u32, 7), plan.calls[0].constant);
    try std.testing.expectEqual(@as(u32, 1), plan.public_output_word_count);
}

test "v2 all-square metadata agrees with existing v1 source plan" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var plain = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 23 } };
    const program = try chainProgram(a, 2, &plain);
    const current = try @import("bounded_call_admission.zig").extract(a, program);
    const next = try extract(a, program);
    try std.testing.expectEqualSlices(u8, &current.canonical_ir_sha256, &next.canonical_ir_sha256);
    try std.testing.expectEqual(current.call_count, next.call_count);
    for (current.callSlice(), next.callSlice()) |old, new| {
        try std.testing.expectEqual(Kind.square_add, new.kind);
        try std.testing.expectEqual(old.call_id, new.call_id);
        try std.testing.expectEqual(old.source_node_id, new.source_node_id);
        try std.testing.expectEqual(old.input_node_id, new.input_node_id);
        try std.testing.expectEqual(old.rounds, new.rounds);
        try std.testing.expectEqual(old.constant, new.constant);
    }
}

test "mix4 is admitted only as exact final step after square and constant" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var plain = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 3 } };
    const program = try chainProgram(a, 1, &plain);
    var early_mix = [_]relation.Step{ .{ .op = .mix4 }, .{ .op = .square }, .{ .op = .add_const, .constant = 3 } };
    program.nodes[0].body = &early_mix;
    try std.testing.expectError(error.UnsupportedChipBody, extract(a, program));
    var extra_mix = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 3 }, .{ .op = .mix4 }, .{ .op = .mix4 } };
    program.nodes[0].body = &extra_mix;
    try std.testing.expectError(error.UnsupportedChipBody, extract(a, program));
    var wrong_add = [_]relation.Step{ .{ .op = .square }, .{ .op = .mul_const, .constant = 3 }, .{ .op = .mix4 } };
    program.nodes[0].body = &wrong_add;
    try std.testing.expectError(error.UnsupportedChipBody, extract(a, program));
}

test "dead private input and more than nine public words are rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var plain = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 3 } };
    var program = try chainProgram(a, 1, &plain);
    const two_inputs = try a.alloc(relation.Input, 2);
    two_inputs[0] = program.inputs[0];
    two_inputs[1] = .{ .name = "unused", .kind = .m31, .length = 4, .visibility = .private };
    program.inputs = two_inputs;
    try std.testing.expectError(error.DeadChipInput, extract(a, program));
    program.inputs = two_inputs[0..1];
    const nodes = try a.alloc(relation.Node, 4);
    nodes[0] = program.nodes[0];
    nodes[1] = .{ .name = "a", .op = .add_const, .lhs = "r0", .constant = 1 };
    nodes[2] = .{ .name = "b", .op = .add_const, .lhs = "r0", .constant = 2 };
    nodes[3] = .{ .name = "c", .op = .add_const, .lhs = "r0", .constant = 3 };
    program.nodes = nodes;
    const outputs = try a.alloc([]const u8, 3);
    outputs[0] = "a";
    outputs[1] = "b";
    outputs[2] = "c";
    program.public_outputs = outputs;
    try std.testing.expectError(error.TooManyPublicOutputWords, extract(a, program));
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

test "repeat after arithmetic is rejected until scalar endpoints are materialized" {
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
    try std.testing.expectError(error.UnsupportedChipInput, extract(a, two));
}

test "source byte cap rejects before JSON parsing" {
    const too_large = try std.testing.allocator.alloc(u8, max_source_bytes + 1);
    defer std.testing.allocator.free(too_large);
    @memset(too_large, 'x');
    try std.testing.expectError(error.ManyCallSourceTooLarge, extractSource(std.testing.allocator, too_large));
}
