//! Independent, fail-closed check of the pure-field normalized relation to
//! canonical IR boundary. This checks the native graph consumed by the circuit
//! compiler; it does not establish circuit/AIR or PCS soundness.
const std = @import("std");
const core = @import("stwo_core");
const relation = @import("relation.zig");
const canonical = @import("canonical.zig");
const M31 = core.fields.m31.M31;

pub const schema = "s31-optimizer-correspondence-pure-field-v2";
pub const Receipt = struct {
    schema: []const u8 = schema,
    program_sha256: [64]u8,
    canonical_ir_sha256: [64]u8,
    source_nodes: usize,
    canonical_nodes: usize,
    aliases: usize,
};

const Key = struct {
    tag: canonical.Tag,
    length: u32,
    lhs: ?u32 = null,
    rhs: ?u32 = null,
    selector: ?u32 = null,
    constant: ?u32 = null,
};

// The legacy v1 IR encoding has neither selector nor index fields. Keep an
// independent encoder here so the certificate checks the digest as well as
// the graph supplied by canonical.build.
const EncodedNode = struct {
    tag: canonical.Tag,
    kind: relation.Kind,
    length: u32,
    lhs: ?u32 = null,
    rhs: ?u32 = null,
    constant: ?u32 = null,
    rounds: ?u32 = null,
    body: ?[]const relation.Step = null,
    input_name: ?[]const u8 = null,
    visibility: ?relation.Visibility = null,
};
const EncodedSelectorNode = struct {
    tag: canonical.Tag,
    kind: relation.Kind,
    length: u32,
    lhs: ?u32 = null,
    rhs: ?u32 = null,
    selector: ?u32 = null,
    constant: ?u32 = null,
    rounds: ?u32 = null,
    body: ?[]const relation.Step = null,
    input_name: ?[]const u8 = null,
    visibility: ?relation.Visibility = null,
};

fn supported(program: relation.Program) bool {
    if (program.version != 1 or program.proof_mode != .transparent) return false;
    for (program.inputs) |input| if (input.kind != .m31) return false;
    for (program.nodes) |node| switch (node.op) {
        .constant, .cast_m31, .add, .sub, .mul, .add_const, .mul_const,
        .inv, .is_zero, .select => {},
        else => return false,
    };
    return true;
}

fn key(node: canonical.Node) Key {
    return .{ .tag = node.tag, .length = node.length, .lhs = node.lhs,
        .rhs = node.rhs, .selector = node.selector, .constant = node.constant };
}

fn constant(length: u32, value: u32) canonical.Node {
    return .{ .tag = .constant, .kind = .m31, .length = length, .constant = value };
}

fn sameNode(expected: canonical.Node, actual: canonical.Node) bool {
    // The fragment has no indexed array or repeat body. Check every field,
    // including the selector and all otherwise-null metadata.
    return std.meta.eql(expected, actual);
}

fn field(value: u32) M31 {
    return M31.fromCanonical(value);
}

fn require(ok: bool) !void {
    if (!ok) return error.OptimizerCorrespondenceMismatch;
}

/// `null` explicitly means that this version does not cover the relation.
/// A non-null receipt means every source name, canonical node, assertion and
/// public output was reconstructed exactly. Replaying a distinct rewrite
/// specification catches native optimizer changes before gate construction.
pub fn check(allocator: std.mem.Allocator, source_bytes: []const u8, ir: *const canonical.IR) !?Receipt {
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    return checkProgram(allocator, parsed.value, ir, source_bytes);
}

fn checkProgram(allocator: std.mem.Allocator, program: relation.Program, ir: *const canonical.IR, source_bytes: []const u8) !?Receipt {
    if (!supported(program)) return null;
    try program.validate(allocator);
    try require(ir.source_map.len == program.inputs.len + program.nodes.len);
    var expected: std.ArrayListUnmanaged(canonical.Node) = .empty;
    defer expected.deinit(allocator);
    var names: std.StringHashMapUnmanaged(u32) = .empty;
    defer names.deinit(allocator);
    var expressions: std.AutoHashMapUnmanaged(Key, u32) = .empty;
    defer expressions.deinit(allocator);
    var aliases: usize = 0;

    for (program.inputs, 0..) |input, source_id| {
        const id: u32 = @intCast(expected.items.len);
        const node: canonical.Node = .{ .tag = .input, .kind = .m31,
            .length = input.length, .input_name = input.name,
            .visibility = input.visibility };
        try expected.append(allocator, node);
        try require(ir.nodes.len > id and sameNode(node, ir.nodes[id]));
        try require(std.mem.eql(u8, ir.source_map[source_id].name, input.name) and
            ir.source_map[source_id].id == id);
        try names.put(allocator, input.name, id);
    }

    for (program.nodes, 0..) |raw, node_index| {
        const lhs: ?u32 = if (raw.lhs) |name| names.get(name) orelse return error.OptimizerCorrespondenceMismatch else null;
        const rhs: ?u32 = if (raw.rhs) |name| names.get(name) orelse return error.OptimizerCorrespondenceMismatch else null;
        const selector: ?u32 = if (raw.selector) |name| names.get(name) orelse return error.OptimizerCorrespondenceMismatch else null;
        const length: u32 = if (raw.op == .constant) raw.length.? else if (raw.op == .is_zero) 1 else expected.items[lhs.?].length;
        const tag: canonical.Tag = switch (raw.op) {
            .constant => .constant,
            .cast_m31 => .cast_m31,
            .add => .add,
            .sub => .sub,
            .mul => .mul,
            .add_const => .add_const,
            .mul_const => .mul_const,
            .inv => .inv,
            .is_zero => .is_zero,
            .select => .select,
            else => unreachable,
        };
        var candidate: canonical.Node = .{ .tag = tag,
            .kind = .m31, .length = length, .lhs = lhs, .rhs = rhs,
            .selector = selector, .constant = raw.constant };
        if ((raw.op == .add or raw.op == .mul) and candidate.lhs.? > candidate.rhs.?)
            std.mem.swap(u32, &candidate.lhs.?, &candidate.rhs.?);
        const left = if (lhs) |id| expected.items[id] else null;
        const right = if (rhs) |id| expected.items[id] else null;
        var alias: ?u32 = null;
        switch (raw.op) {
            .cast_m31 => alias = lhs,
            .add, .sub, .mul => if (left.?.tag == .constant and right.?.tag == .constant) {
                const a = field(left.?.constant.?);
                const b = field(right.?.constant.?);
                candidate = constant(length, switch (raw.op) {
                    .add => a.add(b).toU32(),
                    .sub => a.sub(b).toU32(),
                    .mul => a.mul(b).toU32(),
                    else => unreachable,
                });
            },
            .add_const => {
                if (raw.constant.? == 0) alias = lhs else if (left.?.tag == .constant)
                    candidate = constant(length, field(left.?.constant.?).add(field(raw.constant.?)).toU32());
            },
            .mul_const => {
                if (raw.constant.? == 1) alias = lhs else if (raw.constant.? == 0)
                    candidate = constant(length, 0)
                else if (left.?.tag == .constant)
                    candidate = constant(length, field(left.?.constant.?).mul(field(raw.constant.?)).toU32());
            },
            .is_zero => {
                if (left.?.tag == .constant)
                    candidate = constant(1, @intFromBool(left.?.constant.? == 0));
            },
            .inv, .select => {},
            .constant => {},
            else => unreachable,
        }
        const id: u32 = if (alias) |prior| blk: {
            aliases += 1;
            break :blk prior;
        } else if (expressions.get(key(candidate))) |prior| blk: {
            aliases += 1;
            break :blk prior;
        } else blk: {
            const fresh: u32 = @intCast(expected.items.len);
            try expected.append(allocator, candidate);
            try require(ir.nodes.len > fresh and sameNode(candidate, ir.nodes[fresh]));
            try expressions.put(allocator, key(candidate), fresh);
            break :blk fresh;
        };
        const source_id = program.inputs.len + node_index;
        try require(std.mem.eql(u8, ir.source_map[source_id].name, raw.name) and
            ir.source_map[source_id].id == id);
        try names.put(allocator, raw.name, id);
    }
    try require(ir.nodes.len == expected.items.len and
        ir.assertions.len == program.assertions.len and
        ir.public_outputs.len == program.public_outputs.len);
    for (program.assertions, ir.assertions) |source, actual| {
        try require(actual.lhs == (names.get(source.lhs) orelse return error.OptimizerCorrespondenceMismatch) and
            actual.rhs == (names.get(source.rhs) orelse return error.OptimizerCorrespondenceMismatch));
    }
    for (program.public_outputs, ir.public_outputs) |name, actual| {
        try require(std.mem.eql(u8, actual.name, name) and
            actual.id == (names.get(name) orelse return error.OptimizerCorrespondenceMismatch));
    }
    var uses_selector = false;
    for (expected.items) |node| if (node.tag == .select) {
        uses_selector = true;
        break;
    };
    const canonical_bytes = if (uses_selector) blk: {
        const nodes = try allocator.alloc(EncodedSelectorNode, expected.items.len);
        defer allocator.free(nodes);
        for (expected.items, nodes) |node, *encoded| encoded.* = .{
            .tag = node.tag, .kind = node.kind, .length = node.length,
            .lhs = node.lhs, .rhs = node.rhs, .selector = node.selector,
            .constant = node.constant, .input_name = node.input_name,
            .visibility = node.visibility,
        };
        break :blk try std.json.Stringify.valueAlloc(allocator, .{
            .version = @as(u32, 1), .nodes = nodes,
            .assertions = ir.assertions, .public_outputs = ir.public_outputs,
        }, .{});
    } else blk: {
        const nodes = try allocator.alloc(EncodedNode, expected.items.len);
        defer allocator.free(nodes);
        for (expected.items, nodes) |node, *encoded| encoded.* = .{
            .tag = node.tag, .kind = node.kind, .length = node.length,
            .lhs = node.lhs, .rhs = node.rhs, .constant = node.constant,
            .input_name = node.input_name, .visibility = node.visibility,
        };
        break :blk try std.json.Stringify.valueAlloc(allocator, .{
            .version = @as(u32, 1), .nodes = nodes,
            .assertions = ir.assertions, .public_outputs = ir.public_outputs,
        }, .{});
    };
    defer allocator.free(canonical_bytes);
    var canonical_digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(canonical_bytes, &canonical_digest, .{});
    try require(std.mem.eql(u8, &canonical_digest, &ir.sha256));
    var source_digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(source_bytes, &source_digest, .{});
    return .{ .program_sha256 = std.fmt.bytesToHex(source_digest, .lower),
        .canonical_ir_sha256 = std.fmt.bytesToHex(canonical_digest, .lower),
        .source_nodes = program.nodes.len, .canonical_nodes = ir.nodes.len,
        .aliases = aliases };
}

test "production canonical graph passes with folds CSE aliases and ordered subtraction" {
    const source =
        \\{"version":1,"name":"optimizer_audit","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"},{"name":"y","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"seven","op":"constant","constant":7,"length":4},{"name":"ten","op":"add_const","lhs":"seven","constant":3},{"name":"sum","op":"add","lhs":"x","rhs":"y"},{"name":"same","op":"add","lhs":"y","rhs":"x"},{"name":"diff","op":"sub","lhs":"sum","rhs":"ten"},{"name":"again","op":"mul_const","lhs":"diff","constant":1},{"name":"zero","op":"mul_const","lhs":"again","constant":0}],"assertions":[{"lhs":"sum","rhs":"same"}],"public_outputs":["diff","zero"]}
    ;
    var parsed = try relation.parseProgram(std.testing.allocator, source);
    defer parsed.deinit();
    var ir = try canonical.build(std.testing.allocator, parsed.value);
    defer ir.deinit();
    const receipt = (try check(std.testing.allocator, source, &ir)).?;
    try std.testing.expectEqualStrings(schema, receipt.schema);
    try std.testing.expectEqual(@as(usize, 7), receipt.source_nodes);
    try std.testing.expectEqual(@as(usize, 2), receipt.aliases);

    const original_constant = ir.nodes[3].constant;
    ir.nodes[3].constant = 11;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.nodes[3].constant = original_constant;

    const original_alias = ir.source_map[5].id;
    ir.source_map[5].id = ir.source_map[3].id;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.source_map[5].id = original_alias;

    const original_lhs = ir.nodes[5].lhs;
    const original_rhs = ir.nodes[5].rhs;
    ir.nodes[5].lhs = original_rhs;
    ir.nodes[5].rhs = original_lhs;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.nodes[5].lhs = original_lhs;
    ir.nodes[5].rhs = original_rhs;

    ir.sha256[0] ^= 1;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
}

test "control graph checks scalar zero test, select selector, inverse and CSE" {
    const source =
        \\{"version":1,"name":"optimizer_control","inputs":[{"name":"x","kind":"m31","length":1,"visibility":"public"},{"name":"a","kind":"m31","length":4,"visibility":"private"},{"name":"b","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"z","op":"is_zero","lhs":"x"},{"name":"z_copy","op":"is_zero","lhs":"x"},{"name":"picked","op":"select","lhs":"a","rhs":"b","selector":"z"},{"name":"picked_copy","op":"select","lhs":"a","rhs":"b","selector":"z_copy"},{"name":"inverse","op":"inv","lhs":"picked"},{"name":"c0","op":"constant","constant":0,"length":1},{"name":"one","op":"is_zero","lhs":"c0"}],"assertions":[{"lhs":"picked","rhs":"picked_copy"}],"public_outputs":["inverse","one"]}
    ;
    var parsed = try relation.parseProgram(std.testing.allocator, source);
    defer parsed.deinit();
    var ir = try canonical.build(std.testing.allocator, parsed.value);
    defer ir.deinit();
    const receipt = (try check(std.testing.allocator, source, &ir)).?;
    try std.testing.expectEqualStrings(schema, receipt.schema);
    try std.testing.expectEqual(@as(usize, 7), receipt.source_nodes);
    try std.testing.expectEqual(@as(usize, 2), receipt.aliases);
    try std.testing.expectEqual(@as(?u32, 3), ir.nodes[4].selector);
    try std.testing.expectEqual(@as(u32, 1), ir.nodes[7].constant.?);

    ir.nodes[4].selector = 0;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.nodes[4].selector = 3;
    ir.nodes[7].constant = 0;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.nodes[7].constant = 1;
    ir.source_map[6].id = 5;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
    ir.source_map[6].id = 4;
    ir.sha256[0] ^= 1;
    try std.testing.expectError(error.OptimizerCorrespondenceMismatch,
        check(std.testing.allocator, source, &ir));
}
