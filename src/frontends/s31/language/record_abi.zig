//! Public record ABI v2 validator and typed statement projection. This module
//! deliberately knows only relation shapes and first-order wire references;
//! record grouping emits no arithmetic operation.

const std = @import("std");
const Value = std.json.Value;
const P: i64 = (1 << 31) - 1;
const schema = "s31-public-record-boundary-v2";
const domain = "s31-public-record-boundary-v2\x00";

fn object(value: Value, keys: []const []const u8) !std.json.ObjectMap {
    if (value != .object or value.object.count() != keys.len) return error.InvalidRecordAbi;
    for (keys) |key| if (!value.object.contains(key)) return error.InvalidRecordAbi;
    return value.object;
}

fn field(value: Value, key: []const u8) !Value {
    if (value != .object) return error.InvalidRecordAbi;
    return value.object.get(key) orelse error.InvalidRecordAbi;
}

fn array(value: Value) ![]Value {
    if (value != .array) return error.InvalidRecordAbi;
    return value.array.items;
}

fn name(value: Value) ![]const u8 {
    if (value != .string or value.string.len == 0 or value.string.len > 128) return error.InvalidRecordAbi;
    const bytes = value.string;
    if (!std.ascii.isAlphabetic(bytes[0]) and bytes[0] != '_') return error.InvalidRecordAbi;
    for (bytes[1..]) |byte| if (!std.ascii.isAlphanumeric(byte) and byte != '_') return error.InvalidRecordAbi;
    return bytes;
}

fn string(value: Value) ![]const u8 {
    if (value != .string or value.string.len == 0 or value.string.len > 128)
        return error.InvalidRecordAbi;
    return value.string;
}

fn count(value: Value) !usize {
    if (value != .integer or value.integer < 0) return error.InvalidRecordAbi;
    return std.math.cast(usize, value.integer) orelse error.InvalidRecordAbi;
}

fn appendCanonical(allocator: std.mem.Allocator, output: *std.ArrayList(u8), value: Value) !void {
    switch (value) {
        .object => |map| {
            try output.append(allocator, '{');
            const keys = try allocator.alloc([]const u8, map.count());
            defer allocator.free(keys);
            var iterator = map.iterator();
            var at: usize = 0;
            while (iterator.next()) |entry| : (at += 1) keys[at] = entry.key_ptr.*;
            std.mem.sort([]const u8, keys, {}, struct {
                fn lessThan(_: void, left: []const u8, right: []const u8) bool {
                    return std.mem.lessThan(u8, left, right);
                }
            }.lessThan);
            for (keys, 0..) |key, index| {
                if (index != 0) try output.append(allocator, ',');
                const encoded_key = try std.json.Stringify.valueAlloc(allocator, key, .{});
                defer allocator.free(encoded_key);
                try output.appendSlice(allocator, encoded_key);
                try output.append(allocator, ':');
                try appendCanonical(allocator, output, map.get(key).?);
            }
            try output.append(allocator, '}');
        },
        .array => |items| {
            try output.append(allocator, '[');
            for (items.items, 0..) |item, index| {
                if (index != 0) try output.append(allocator, ',');
                try appendCanonical(allocator, output, item);
            }
            try output.append(allocator, ']');
        },
        .string => |bytes| {
            const encoded = try std.json.Stringify.valueAlloc(allocator, bytes, .{});
            defer allocator.free(encoded);
            try output.appendSlice(allocator, encoded);
        },
        .integer => |number| {
            const encoded = try std.fmt.allocPrint(allocator, "{d}", .{number});
            defer allocator.free(encoded);
            try output.appendSlice(allocator, encoded);
        },
        .bool => |flag| try output.appendSlice(allocator, if (flag) "true" else "false"),
        .null => try output.appendSlice(allocator, "null"),
        else => return error.InvalidRecordAbi,
    }
}

pub fn canonicalJson(allocator: std.mem.Allocator, value: Value) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendCanonical(allocator, &output, value);
    return output.toOwnedSlice(allocator);
}

const Segment = union(enum) {
    root: []const u8,
    field: []const u8,
    tuple: usize,
};

fn matchingPath(value: Value, path: []const Segment) !void {
    const parts = try array(value);
    if (parts.len != path.len) return error.InvalidRecordAbi;
    for (parts, path) |part, expected| {
        switch (expected) {
            .root => |label| {
                _ = try object(part, &.{"root"});
                if (!std.mem.eql(u8, try name(try field(part, "root")), label)) return error.InvalidRecordAbi;
            },
            .field => |label| {
                _ = try object(part, &.{"field"});
                if (!std.mem.eql(u8, try name(try field(part, "field")), label)) return error.InvalidRecordAbi;
            },
            .tuple => |index| {
                _ = try object(part, &.{"tuple"});
                if (try count(try field(part, "tuple")) != index) return error.InvalidRecordAbi;
            },
        }
    }
}

const State = struct {
    allocator: std.mem.Allocator,
    input_at: usize = 0,
    total_leaves: usize = 0,
    outputs: std.ArrayList([]const u8) = .empty,
    path: std.ArrayList(Segment) = .empty,
    nominal: std.StringHashMapUnmanaged([]u8) = .empty,

    fn deinit(self: *State) void {
        self.outputs.deinit(self.allocator);
        self.path.deinit(self.allocator);
        var iterator = self.nominal.valueIterator();
        while (iterator.next()) |encoded| self.allocator.free(encoded.*);
        self.nominal.deinit(self.allocator);
    }

    fn leaf(self: *State, program: anytype, descriptor: Value,
            expected_length: usize, input_root: bool, visibility: []const u8) !void {
        _ = try object(descriptor, &.{ "kind", "length", "path", "wire" });
        if (!std.mem.eql(u8, try name(try field(descriptor, "kind")), "m31") or
            try count(try field(descriptor, "length")) != expected_length)
            return error.InvalidRecordAbi;
        try matchingPath(try field(descriptor, "path"), self.path.items);
        const wire = try name(try field(descriptor, "wire"));
        self.total_leaves += 1;
        if (self.total_leaves > 1024) return error.InvalidRecordAbi;
        if (input_root) {
            if (self.input_at >= program.inputs.len) return error.InvalidRecordAbi;
            const input = program.inputs[self.input_at];
            self.input_at += 1;
            if (!std.mem.eql(u8, input.name, wire) or input.kind != .m31 or
                input.length != expected_length or
                !std.mem.eql(u8, @tagName(input.visibility), visibility))
                return error.InvalidRecordAbi;
        } else {
            const shape = (try program.shapeOf(self.allocator, wire)) orelse return error.InvalidRecordAbi;
            if (shape.kind != .m31 or shape.length != expected_length) return error.InvalidRecordAbi;
            var seen = false;
            for (self.outputs.items) |prior| if (std.mem.eql(u8, prior, wire)) {
                seen = true;
                break;
            };
            if (!seen) try self.outputs.append(self.allocator, wire);
        }
    }

    fn typeTree(self: *State, program: anytype, tree: Value, leaves: []Value,
                at: *usize, input_root: bool, visibility: []const u8, depth: usize) !void {
        if (depth > 32 or tree != .object) return error.InvalidRecordAbi;
        if (tree.object.contains("kind")) {
            _ = try object(tree, &.{ "kind", "length" });
            if (!std.mem.eql(u8, try name(try field(tree, "kind")), "m31")) return error.InvalidRecordAbi;
            const length = try count(try field(tree, "length"));
            if (length == 0 or length > 8 or at.* >= leaves.len) return error.InvalidRecordAbi;
            try self.leaf(program, leaves[at.*], length, input_root, visibility);
            at.* += 1;
            return;
        }
        if (tree.object.contains("tuple")) {
            _ = try object(tree, &.{"tuple"});
            const elements = try array(try field(tree, "tuple"));
            if (elements.len == 0 or elements.len > 64) return error.InvalidRecordAbi;
            for (elements, 0..) |child, index| {
                try self.path.append(self.allocator, .{ .tuple = index });
                try self.typeTree(program, child, leaves, at, input_root, visibility, depth + 1);
                _ = self.path.pop();
            }
            return;
        }
        _ = try object(tree, &.{ "record", "fields" });
        const record_name = try name(try field(tree, "record"));
        const fields = try array(try field(tree, "fields"));
        if (fields.len == 0 or fields.len > 64) return error.InvalidRecordAbi;
        const canonical = try canonicalJson(self.allocator, tree);
        if (self.nominal.get(record_name)) |prior| {
            defer self.allocator.free(canonical);
            if (!std.mem.eql(u8, prior, canonical)) return error.InvalidRecordAbi;
        } else try self.nominal.put(self.allocator, record_name, canonical);
        for (fields, 0..) |child, index| {
            _ = try object(child, &.{ "name", "type" });
            const field_name = try name(try field(child, "name"));
            for (fields[0..index]) |prior| {
                if (std.mem.eql(u8, try name(try field(prior, "name")), field_name))
                    return error.InvalidRecordAbi;
            }
            try self.path.append(self.allocator, .{ .field = field_name });
            try self.typeTree(program, try field(child, "type"), leaves, at,
                              input_root, visibility, depth + 1);
            _ = self.path.pop();
        }
    }
};

fn root(state: *State, program: anytype, descriptor: Value,
        input_root: bool) ![]const u8 {
    if (input_root)
        _ = try object(descriptor, &.{ "name", "type", "leaves", "visibility" })
    else
        _ = try object(descriptor, &.{ "name", "type", "leaves" });
    const root_name = try name(try field(descriptor, "name"));
    const visibility = if (input_root) try name(try field(descriptor, "visibility")) else "public";
    if (input_root and !std.mem.eql(u8, visibility, "public") and !std.mem.eql(u8, visibility, "private"))
        return error.InvalidRecordAbi;
    const tree = try field(descriptor, "type");
    if (tree != .object or (input_root and !tree.object.contains("kind")) or
        (!input_root and !tree.object.contains("record"))) return error.InvalidRecordAbi;
    const leaves = try array(try field(descriptor, "leaves"));
    try state.path.append(state.allocator, .{ .root = root_name });
    defer _ = state.path.pop();
    var at: usize = 0;
    try state.typeTree(program, tree, leaves, &at, input_root, visibility, 0);
    if (at != leaves.len) return error.InvalidRecordAbi;
    return root_name;
}

pub fn validate(allocator: std.mem.Allocator, program: anytype) !void {
    const abi = program.public_abi orelse return error.InvalidRecordAbi;
    _ = try object(abi, &.{ "inputs", "result", "schema" });
    if (!std.mem.eql(u8, try string(try field(abi, "schema")), schema)) return error.InvalidRecordAbi;
    const inputs = try array(try field(abi, "inputs"));
    if (inputs.len != program.inputs.len) return error.InvalidRecordAbi;
    var state: State = .{ .allocator = allocator };
    defer state.deinit();
    var roots: std.StringHashMapUnmanaged(void) = .empty;
    defer roots.deinit(allocator);
    for (inputs) |descriptor| {
        const root_name = try root(&state, program, descriptor, true);
        if (roots.contains(root_name)) return error.InvalidRecordAbi;
        try roots.put(allocator, root_name, {});
    }
    if (state.input_at != program.inputs.len) return error.InvalidRecordAbi;
    const result_name = try root(&state, program, try field(abi, "result"), false);
    if (!std.mem.eql(u8, result_name, "result") or roots.contains(result_name)) return error.InvalidRecordAbi;
    if (state.outputs.items.len != program.public_outputs.len) return error.InvalidRecordAbi;
    for (state.outputs.items, program.public_outputs) |actual, expected| {
        if (!std.mem.eql(u8, actual, expected)) return error.InvalidRecordAbi;
    }
}

pub fn digest(allocator: std.mem.Allocator, program: anytype) ![32]u8 {
    try validate(allocator, program);
    const canonical = try canonicalJson(allocator, program.public_abi.?);
    defer allocator.free(canonical);
    var hasher = std.crypto.hash.sha2.Sha256.init(.{});
    hasher.update(domain);
    hasher.update(canonical);
    hasher.update("\n");
    var output: [32]u8 = undefined;
    hasher.final(&output);
    return output;
}

pub fn claimedWords(allocator: std.mem.Allocator, program: anytype,
                    encoded: []const u8) ![8]u32 {
    if (encoded.len == 0 or encoded.len > 1_000_000) return error.InvalidRecordStatement;
    try validate(allocator, program);
    var parsed = try std.json.parseFromSlice(Value, allocator, encoded,
        .{ .duplicate_field_behavior = .@"error" });
    defer parsed.deinit();
    const statement = parsed.value;
    _ = try object(statement, &.{ "abi_sha256", "leaves", "version" });
    if (try count(try field(statement, "version")) != 2) return error.InvalidRecordStatement;
    const expected_digest = try digest(allocator, program);
    const expected_hex = std.fmt.bytesToHex(expected_digest, .lower);
    const claimed_digest = try string(try field(statement, "abi_sha256"));
    if (!std.mem.eql(u8, claimed_digest, &expected_hex)) return error.InvalidRecordStatement;
    const canonical = try canonicalJson(allocator, statement);
    defer allocator.free(canonical);
    if (encoded.len != canonical.len + 1 or !std.mem.eql(u8, encoded[0..canonical.len], canonical) or
        encoded[canonical.len] != '\n') return error.InvalidRecordStatement;
    const claimed = try array(try field(statement, "leaves"));
    const abi = program.public_abi.?;
    const roots = try array(try field(abi, "inputs"));
    const output_root = try field(abi, "result");
    var expected_count: usize = (try array(try field(output_root, "leaves"))).len;
    for (roots) |input_root| if (std.mem.eql(u8, try name(try field(input_root, "visibility")), "public")) {
        expected_count += (try array(try field(input_root, "leaves"))).len;
    };
    if (claimed.len != expected_count) return error.InvalidRecordStatement;
    var wire_values: std.StringHashMapUnmanaged([]const u32) = .empty;
    defer {
        var iterator = wire_values.valueIterator();
        while (iterator.next()) |words| allocator.free(words.*);
        wire_values.deinit(allocator);
    }
    var cursor: usize = 0;
    for (roots) |input_root| {
        if (!std.mem.eql(u8, try name(try field(input_root, "visibility")), "public")) continue;
        for (try array(try field(input_root, "leaves"))) |descriptor| {
            try checkClaim(allocator, descriptor, claimed[cursor], &wire_values);
            cursor += 1;
        }
    }
    for (try array(try field(output_root, "leaves"))) |descriptor| {
        try checkClaim(allocator, descriptor, claimed[cursor], &wire_values);
        cursor += 1;
    }
    var output = [_]u32{0} ** 8;
    var at: usize = 0;
    for (program.inputs) |input| {
        if (input.visibility != .public) continue;
        const values = wire_values.get(input.name) orelse return error.InvalidRecordStatement;
        for (values) |word| {
            if (at >= 8) return error.InvalidRecordStatement;
            output[at] = word;
            at += 1;
        }
    }
    for (program.public_outputs) |wire| {
        const values = wire_values.get(wire) orelse return error.InvalidRecordStatement;
        for (values) |word| {
            if (at >= 8) return error.InvalidRecordStatement;
            output[at] = word;
            at += 1;
        }
    }
    if (at == 0) return error.InvalidRecordStatement;
    return output;
}

fn checkClaim(allocator: std.mem.Allocator, descriptor: Value, actual: Value,
              wire_values: *std.StringHashMapUnmanaged([]const u32)) !void {
    _ = try object(actual, &.{ "path", "words" });
    const expected_path = try canonicalJson(allocator, try field(descriptor, "path"));
    defer allocator.free(expected_path);
    const actual_path = try canonicalJson(allocator, try field(actual, "path"));
    defer allocator.free(actual_path);
    if (!std.mem.eql(u8, expected_path, actual_path)) return error.InvalidRecordStatement;
    const length = try count(try field(descriptor, "length"));
    const words = try array(try field(actual, "words"));
    if (words.len != length) return error.InvalidRecordStatement;
    const value = try allocator.alloc(u32, length);
    errdefer allocator.free(value);
    for (words, value) |word, *slot| {
        if (word != .integer or word.integer < 0 or word.integer >= P) return error.InvalidRecordStatement;
        slot.* = @intCast(word.integer);
    }
    const wire = try name(try field(descriptor, "wire"));
    if (wire_values.get(wire)) |prior| {
        if (!std.mem.eql(u32, prior, value)) return error.InvalidRecordStatement;
        allocator.free(value);
    } else try wire_values.put(allocator, wire, value);
}
