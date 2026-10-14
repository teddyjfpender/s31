//! Audit-only XDM04 certificate for the exact experimental CAS05 draft.
//!
//! `verifyAndCapture` first calls the native verifier, then independently
//! parses its wire, rebuilds the sparse node map, and checks a complete mixed
//! leaf/inserted/upper opening for every returned row. `auditCommitment`
//! independently rehashes every node in a native prover commitment. Both
//! functions are uniform in admitted profile sizes, subject to allocation.
//! This module is not installed in CAS05 verification and is not a Zig-to-Lean
//! semantics proof or a BLAKE2s collision-resistance result.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");

const M31 = core.fields.m31.M31;
const modulus = core.fields.m31.Modulus;
const xdm = core.pcs.transposed_merkle_sparse;
const tree = core.pcs.transposed_merkle_cascade;
const topology = core.pcs.transposed_merkle;
const Commitment = prover.pcs.transposed_cascade_experimental.Commitment;
const Hash = tree.Hash;
const Children = struct { left: Hash, right: Hash };

fn sameHash(a: Hash, b: Hash) bool {
    return std.meta.eql(a, b);
}

fn key(level: usize, index: usize) u64 {
    return (@as(u64, @intCast(level)) << 32) | @as(u64, @intCast(index));
}

fn pathPosition(level: usize, index: usize) usize {
    var at_level = level;
    var at_index = index;
    var place: usize = 1;
    var position: usize = 0;
    while (at_level > 0) : (at_level -= 1) {
        const side = if (at_level == 1) at_index & 1 else (at_index >> 1) & 1;
        position += place * side;
        place *= 2;
        at_index = topology.parent(@intCast(at_level), at_index);
    }
    return position;
}

const Cursor = struct {
    bytes: []const u8,
    at: usize = 0,

    fn take(self: *Cursor, n: usize) ![]const u8 {
        if (self.at > self.bytes.len or n > self.bytes.len - self.at)
            return error.InvalidXdm04Certificate;
        const out = self.bytes[self.at..][0..n];
        self.at += n;
        return out;
    }
    fn readU16(self: *Cursor) !u16 {
        return std.mem.readInt(u16, (try self.take(2))[0..2], .little);
    }
    fn readU32(self: *Cursor) !u32 {
        return std.mem.readInt(u32, (try self.take(4))[0..4], .little);
    }
    fn felt(self: *Cursor) !M31 {
        const word = try self.readU32();
        if (word >= modulus) return error.InvalidXdm04Certificate;
        return M31.fromCanonical(word);
    }
    fn hash(self: *Cursor) !Hash {
        var out: Hash = undefined;
        @memcpy(&out, try self.take(out.len));
        return out;
    }
};

fn putNode(nodes: *std.AutoHashMap(u64, Hash), level: usize, index: usize, value: Hash) !void {
    const address = key(level, index);
    if (nodes.get(address)) |old| {
        if (!sameHash(old, value)) return error.InvalidXdm04Certificate;
    } else try nodes.put(address, value);
}

fn childHash(nodes: *std.AutoHashMap(u64, Hash), cursor: *Cursor,
    level: usize, index: usize, used: *usize, count: usize) !Hash {
    if (nodes.get(key(level, index))) |known| return known;
    if (used.* >= count) return error.InvalidXdm04Certificate;
    const value = try cursor.hash();
    used.* += 1;
    try nodes.put(key(level, index), value);
    return value;
}

fn parseHeader(cursor: *Cursor, expected: xdm.Profile, root: Hash) !void {
    if (!std.mem.eql(u8, try cursor.take(xdm.MAGIC.len), xdm.MAGIC))
        return error.InvalidXdm04Certificate;
    if (try cursor.readU16() != xdm.VERSION or try cursor.readU16() != 0 or
        try cursor.readU32() != cursor.bytes.len or
        try cursor.readU32() != expected.largest_log_size or
        try cursor.readU16() != expected.height_count or try cursor.readU16() != 0 or
        try cursor.readU32() != expected.query_count)
        return error.InvalidXdm04Certificate;
    for (expected.columns[0..expected.height_count]) |count|
        if (try cursor.readU16() != count) return error.InvalidXdm04Certificate;
    if (!sameHash(try cursor.hash(), root)) return error.InvalidXdm04Certificate;
}

pub const Step = struct {
    sibling: Hash,
    inserted_row: ?[]const M31,
};

pub const Opening = struct {
    /// Borrowed from the capture's native verifier output.
    row: []const M31,
    children: ?Children,
    steps: []Step,
    native_level: usize,
    native_index: usize,
    path_position: usize,
    root: Hash,

    pub fn deinit(self: *Opening, allocator: std.mem.Allocator) void {
        allocator.free(self.steps);
        self.* = undefined;
    }

    pub fn replay(self: Opening) Hash {
        var current = if (self.children) |children|
            tree.hashInserted(children.left, children.right, self.row)
        else
            tree.hashLeaf(self.row);
        var position = self.path_position;
        for (self.steps) |step| {
            const left = if (position & 1 == 0) current else step.sibling;
            const right = if (position & 1 == 0) step.sibling else current;
            current = if (step.inserted_row) |inserted|
                tree.hashInserted(left, right, inserted)
            else
                tree.hashUpper(left, right);
            position >>= 1;
        }
        return current;
    }

    pub fn check(self: Opening) bool {
        return self.native_level < @bitSizeOf(usize) and
            self.native_index < (@as(usize, 1) << @intCast(self.native_level)) and
            self.steps.len == self.native_level and
            self.path_position == pathPosition(self.native_level, self.native_index) and
            sameHash(self.replay(), self.root);
    }
};

pub const Capture = struct {
    allocator: std.mem.Allocator,
    profile: xdm.Profile,
    expected_root: Hash,
    raw_queries: []usize,
    opened: xdm.VerifiedOpenings,
    nodes: std.AutoHashMap(u64, Hash),
    first_rows: std.AutoHashMap(u64, usize),

    pub fn deinit(self: *Capture) void {
        self.first_rows.deinit();
        self.nodes.deinit();
        self.opened.deinit();
        self.allocator.free(self.raw_queries);
        self.* = undefined;
    }

    fn row(self: *const Capture, height: usize, index: usize) ![]const M31 {
        const offset = self.first_rows.get(key(height, index)) orelse
            return error.InvalidXdm04Certificate;
        const cols = self.profile.columns[height];
        if (offset > self.opened.values[height].len or
            cols > self.opened.values[height].len - offset)
            return error.InvalidXdm04Certificate;
        return self.opened.values[height][offset..][0..cols];
    }

    fn queriedRow(self: *const Capture, height: usize, query: usize, j: usize) ![]const M31 {
        const cols = self.profile.columns[height];
        const offset = (query * 2 + j) * cols;
        if (offset > self.opened.values[height].len or
            cols > self.opened.values[height].len - offset)
            return error.InvalidXdm04Certificate;
        return self.opened.values[height][offset..][0..cols];
    }

    pub fn openingAt(self: *const Capture, height: usize, query: usize, j: usize) !Opening {
        if (height >= self.profile.height_count or query >= self.raw_queries.len or j >= 2)
            return error.InvalidXdm04Certificate;
        const k: usize = self.profile.largest_log_size;
        const level = k - height;
        const index = xdm.pairBase(self.raw_queries[query], height) + j;
        const row_values = try self.queriedRow(height, query, j);
        const first_row = try self.row(height, index);
        for (row_values, first_row) |value, earlier|
            if (!value.eql(earlier)) return error.InvalidXdm04Certificate;
        const children: ?Children = if (height == 0) null else blk: {
            const pair = topology.children(@intCast(level), index);
            break :blk .{
                .left = self.nodes.get(key(level + 1, pair[0])) orelse
                    return error.InvalidXdm04Certificate,
                .right = self.nodes.get(key(level + 1, pair[1])) orelse
                    return error.InvalidXdm04Certificate,
            };
        };
        const steps = try self.allocator.alloc(Step, level);
        errdefer self.allocator.free(steps);
        var at_level = level;
        var at_index = index;
        for (steps) |*step| {
            const sibling_index = topology.sibling(@intCast(at_level), at_index);
            const sibling = self.nodes.get(key(at_level, sibling_index)) orelse
                return error.InvalidXdm04Certificate;
            const parent_index = topology.parent(@intCast(at_level), at_index);
            const parent_height = k - (at_level - 1);
            step.* = .{
                .sibling = sibling,
                .inserted_row = if (parent_height > 0 and parent_height < self.profile.height_count)
                    try self.row(parent_height, parent_index)
                else null,
            };
            at_level -= 1;
            at_index = parent_index;
        }
        return .{
            .row = row_values,
            .children = children,
            .steps = steps,
            .native_level = level,
            .native_index = index,
            .path_position = pathPosition(level, index),
            .root = self.expected_root,
        };
    }

    pub fn auditAt(self: *const Capture, height: usize, query: usize, j: usize) !void {
        var opening = try self.openingAt(height, query, j);
        defer opening.deinit(self.allocator);
        if (!opening.check()) return error.InvalidXdm04Certificate;
        var current = if (opening.children) |children|
            tree.hashInserted(children.left, children.right, opening.row)
        else
            tree.hashLeaf(opening.row);
        var at_level = opening.native_level;
        var at_index = opening.native_index;
        var position = opening.path_position;
        if (!sameHash(current, self.nodes.get(key(at_level, at_index)) orelse
            return error.InvalidXdm04Certificate)) return error.InvalidXdm04Certificate;
        for (opening.steps) |step| {
            const left = if (position & 1 == 0) current else step.sibling;
            const right = if (position & 1 == 0) step.sibling else current;
            current = if (step.inserted_row) |inserted|
                tree.hashInserted(left, right, inserted)
            else
                tree.hashUpper(left, right);
            at_index = topology.parent(@intCast(at_level), at_index);
            at_level -= 1;
            position >>= 1;
            if (!sameHash(current, self.nodes.get(key(at_level, at_index)) orelse
                return error.InvalidXdm04Certificate)) return error.InvalidXdm04Certificate;
        }
    }

    pub fn auditAll(self: *const Capture) !void {
        for (self.raw_queries, 0..) |_, query| {
            for (0..self.profile.height_count) |height| {
                for (0..2) |j| try self.auditAt(height, query, j);
            }
        }
    }
};

/// A successful return is stronger than direct native verifier success: it
/// includes a second parse, sparse replay, and every-row mixed-path audit.
pub fn verifyAndCapture(allocator: std.mem.Allocator, encoded: []const u8,
    expected: xdm.Profile, expected_root: Hash, raw_queries: []const usize) !Capture {
    try expected.validate();
    var opened = try xdm.verifyAndCollect(allocator, encoded, expected, expected_root, raw_queries);
    errdefer opened.deinit();
    var nodes = std.AutoHashMap(u64, Hash).init(allocator);
    errdefer nodes.deinit();
    var first_rows = std.AutoHashMap(u64, usize).init(allocator);
    errdefer first_rows.deinit();
    const raw_copy = try allocator.dupe(usize, raw_queries);
    errdefer allocator.free(raw_copy);
    var cursor = Cursor{ .bytes = encoded };
    try parseHeader(&cursor, expected, expected_root);
    const k: usize = expected.largest_log_size;
    for (raw_queries, 0..) |raw, query| {
        if (raw >= (@as(usize, 1) << @intCast(k)) or try cursor.readU32() != raw)
            return error.InvalidXdm04Certificate;
        for (0..expected.height_count) |height| {
            const cols = expected.columns[height];
            const base = xdm.pairBase(raw, height);
            for (0..2) |j| {
                const offset = (query * 2 + j) * cols;
                for (0..cols) |col| {
                    const word = try cursor.felt();
                    if (!word.eql(opened.at(height, query, j, col)))
                        return error.InvalidXdm04Certificate;
                }
                const address = key(height, base + j);
                if (first_rows.get(address)) |prior| {
                    for (0..cols) |col| if (!opened.values[height][prior + col].eql(
                        opened.values[height][offset + col]))
                        return error.InvalidXdm04Certificate;
                } else try first_rows.put(address, offset);
            }
        }
    }
    const witness_count: usize = try cursor.readU32();
    const maximum = expected.query_count *
        (4 * (expected.height_count - 1) + 2 * @as(usize, expected.largest_log_size));
    if (witness_count > maximum or witness_count > (encoded.len - cursor.at) / @sizeOf(Hash) or
        encoded.len - cursor.at != witness_count * @sizeOf(Hash))
        return error.InvalidXdm04Certificate;
    var used: usize = 0;
    for (raw_queries, 0..) |raw, query| {
        const base = xdm.pairBase(raw, 0);
        for (0..2) |j| {
            const cols = expected.columns[0];
            const offset = (query * 2 + j) * cols;
            try putNode(&nodes, k, base + j, tree.hashLeaf(opened.values[0][offset..][0..cols]));
        }
    }
    for (1..expected.height_count) |height| {
        const level = k - height;
        for (raw_queries, 0..) |raw, query| {
            const base = xdm.pairBase(raw, height);
            for (0..2) |j| {
                const index = base + j;
                const pair = topology.children(@intCast(level), index);
                const left = try childHash(&nodes, &cursor, level + 1, pair[0], &used, witness_count);
                const right = try childHash(&nodes, &cursor, level + 1, pair[1], &used, witness_count);
                const cols = expected.columns[height];
                const offset = (query * 2 + j) * cols;
                try putNode(&nodes, level, index,
                    tree.hashInserted(left, right, opened.values[height][offset..][0..cols]));
            }
        }
    }
    const bottom = k - expected.height_count + 1;
    var active = std.ArrayList(usize).empty;
    defer active.deinit(allocator);
    for (raw_queries) |raw| {
        const base = xdm.pairBase(raw, expected.height_count - 1);
        try active.append(allocator, base);
        try active.append(allocator, base + 1);
    }
    var level = bottom;
    while (level > 0) : (level -= 1) {
        std.sort.heap(usize, active.items, {}, std.sort.asc(usize));
        var next = std.ArrayList(usize).empty;
        errdefer next.deinit(allocator);
        for (active.items, 0..) |index, position| {
            if (position > 0 and index == active.items[position - 1]) continue;
            if (!nodes.contains(key(level, index))) return error.InvalidXdm04Certificate;
            const sibling = topology.sibling(@intCast(level), index);
            _ = try childHash(&nodes, &cursor, level, sibling, &used, witness_count);
            const parent = topology.parent(@intCast(level), index);
            const pair = topology.children(@intCast(level - 1), parent);
            const left = nodes.get(key(level, pair[0])) orelse return error.InvalidXdm04Certificate;
            const right = nodes.get(key(level, pair[1])) orelse return error.InvalidXdm04Certificate;
            try putNode(&nodes, level - 1, parent, tree.hashUpper(left, right));
            try next.append(allocator, parent);
        }
        active.deinit(allocator);
        active = next;
    }
    if (used != witness_count or cursor.at != encoded.len or
        !sameHash(nodes.get(key(0, 0)) orelse return error.InvalidXdm04Certificate,
            expected_root)) return error.InvalidXdm04Certificate;
    var capture = Capture{
        .allocator = allocator,
        .profile = expected,
        .expected_root = expected_root,
        .raw_queries = raw_copy,
        .opened = opened,
        .nodes = nodes,
        .first_rows = first_rows,
    };
    try capture.auditAll();
    return capture;
}

/// Rehash all nodes from the *borrowed* source columns of a native commitment.
/// The root alone is insufficient evidence of this construction; every layer
/// and ordered row is checked. A caller can then use `verifyAndCapture` for
/// source openings against this same root.
pub fn auditCommitment(commitment: Commitment) !void {
    const source = commitment.source_columns;
    const k: usize = commitment.profile.largest_log_size;
    if (source.len < 2 or source.len != commitment.profile.height_count or
        commitment.layers.len != k + 1 or k < source.len + 2 or
        k >= @bitSizeOf(usize)) return error.InvalidXdm04Certificate;
    for (commitment.layers, 0..) |layer, level| {
        if (layer.len != (@as(usize, 1) << @intCast(level)))
            return error.InvalidXdm04Certificate;
    }
    var row: [tree.MAX_COLUMNS]M31 = undefined;
    for (source, 0..) |columns, height| {
        if (columns.len == 0 or columns.len > tree.MAX_COLUMNS or
            columns.len != commitment.profile.columns[height])
            return error.InvalidXdm04Certificate;
        for (columns) |column| {
            if (column.len != (@as(usize, 1) << @intCast(k - height)))
                return error.InvalidXdm04Certificate;
            for (column) |word| if (word.v >= modulus)
                return error.InvalidXdm04Certificate;
        }
    }
    for (commitment.layers[k], 0..) |actual, index| {
        for (source[0], 0..) |column, col| row[col] = column[index];
        if (!sameHash(actual, tree.hashLeaf(row[0..source[0].len])))
            return error.InvalidXdm04Certificate;
    }
    var level = k;
    while (level > 0) {
        level -= 1;
        const height = k - level;
        for (commitment.layers[level], 0..) |actual, index| {
            const pair = topology.children(@intCast(level), index);
            const left = commitment.layers[level + 1][pair[0]];
            const right = commitment.layers[level + 1][pair[1]];
            const expected = if (height < source.len) blk: {
                for (source[height], 0..) |column, col| row[col] = column[index];
                break :blk tree.hashInserted(left, right, row[0..source[height].len]);
            } else tree.hashUpper(left, right);
            if (!sameHash(actual, expected)) return error.InvalidXdm04Certificate;
        }
    }
}
