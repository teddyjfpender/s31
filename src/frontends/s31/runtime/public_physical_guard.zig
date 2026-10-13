//! Eligibility for the diagnostic, uncommitted public direct-Gate base export.

const std = @import("std");
const relation = @import("stwo_s31_prototype").relation;

pub fn eligible(allocator: std.mem.Allocator, source: relation.Program) !bool {
    if (source.version != 1 or source.proof_mode != .transparent or
        source.inputs.len != 1 or source.nodes.len == 0 or source.nodes.len > 16 or
        source.assertions.len != 0 or source.public_outputs.len != 1)
        return false;
    const input = source.inputs[0];
    if (input.visibility != .public or input.kind != .m31 or input.length != 4)
        return false;
    var selected_is_node = false;
    for (source.nodes) |node| {
        if (node.op != .add and node.op != .sub and node.op != .mul) return false;
        if (std.mem.eql(u8, node.name, source.public_outputs[0])) selected_is_node = true;
    }
    if (!selected_is_node) return false;
    const result = (try source.shapeOf(allocator, source.public_outputs[0])) orelse return false;
    return result.kind == .m31 and result.length == 4;
}

pub fn checkAssignment(assignment: relation.Assignment) !void {
    if (assignment.private_inputs) |private| {
        if (private != .object or private.object.count() != 0)
            return error.PrivatePhysicalRowsUnavailable;
    }
}

test "public physical export guard rejects wrong source profiles" {
    const allocator = std.testing.allocator;
    var input = [_]relation.Input{.{
        .name = "x",
        .kind = .m31,
        .length = 4,
        .visibility = .public,
    }};
    var nodes = [_]relation.Node{.{
        .name = "p1",
        .op = .mul,
        .lhs = "x",
        .rhs = "x",
    }};
    var outputs = [_][]const u8{"p1"};
    var program: relation.Program = .{
        .version = 1,
        .name = "public_square",
        .inputs = &input,
        .nodes = &nodes,
        .assertions = &.{},
        .public_outputs = &outputs,
    };
    try program.validate(allocator);
    try std.testing.expect(try eligible(allocator, program));

    program.version = 2;
    try std.testing.expect(!try eligible(allocator, program));
    program.version = 1;
    program.proof_mode = .blinded;
    try std.testing.expect(!try eligible(allocator, program));
    program.proof_mode = .transparent;
    program.nodes = &.{};
    try std.testing.expect(!try eligible(allocator, program));
    program.nodes = &nodes;
    var two_inputs = [_]relation.Input{ input[0], input[0] };
    program.inputs = &two_inputs;
    try std.testing.expect(!try eligible(allocator, program));
    program.inputs = &input;
    var two_outputs = [_][]const u8{ "p1", "p1" };
    program.public_outputs = &two_outputs;
    try std.testing.expect(!try eligible(allocator, program));
    program.public_outputs = &outputs;

    input[0].visibility = .private;
    try std.testing.expect(!try eligible(allocator, program));
    input[0].visibility = .public;
    input[0].kind = .u16;
    try std.testing.expect(!try eligible(allocator, program));
    input[0].kind = .m31;
    input[0].length = 2;
    try std.testing.expect(!try eligible(allocator, program));
    input[0].length = 4;

    outputs[0] = "x";
    try std.testing.expect(!try eligible(allocator, program));
    outputs[0] = "p1";
    var assertions = [_]relation.Assertion{.{ .lhs = "p1", .rhs = "x" }};
    program.assertions = &assertions;
    try std.testing.expect(!try eligible(allocator, program));
    program.assertions = &.{};
    nodes[0].op = .constant;
    try std.testing.expect(!try eligible(allocator, program));
    nodes[0].op = .repeat;
    try std.testing.expect(!try eligible(allocator, program));
    nodes[0].op = .sum_lanes;
    try std.testing.expect(!try eligible(allocator, program));
    nodes[0].op = .sub;
    try std.testing.expect(try eligible(allocator, program));
    input[0].visibility = .private;
    try std.testing.expect(!try eligible(allocator, program));
    input[0].visibility = .public;
    nodes[0].op = .mul;

    var too_many = [_]relation.Node{nodes[0]} ** 17;
    program.nodes = &too_many;
    try std.testing.expect(!try eligible(allocator, program));
}

test "public physical export guard rejects nonempty private assignments" {
    const allocator = std.testing.allocator;
    var empty = try relation.parseAssignment(allocator,
        \\{"public_inputs":{"x":[0,1,2,7]},"private_inputs":{},"public_outputs":{"p1":[0,1,4,49]}}
    );
    defer empty.deinit();
    try checkAssignment(empty.value);
    var private = try relation.parseAssignment(allocator,
        \\{"public_inputs":{"x":[0,1,2,7]},"private_inputs":{"secret":[1]},"public_outputs":{"p1":[0,1,4,49]}}
    );
    defer private.deinit();
    try std.testing.expectError(error.PrivatePhysicalRowsUnavailable, checkAssignment(private.value));
}
