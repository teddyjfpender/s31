//! Emit a native accepted XDM04 wire and every audit certificate for an
//! independent standard-library hashlib/topology replay.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const audit = @import("pcs_xdm04_mixed_certificate");

const M31 = core.fields.m31.M31;
const Hash = core.pcs.transposed_merkle_cascade.Hash;
const Commitment = prover.pcs.transposed_cascade_experimental.Commitment;
const topology = core.pcs.transposed_merkle;

const Step = struct { sibling: []const u8, inserted_row: ?[]const u32 };
const Opening = struct {
    height: usize,
    query: usize,
    j: usize,
    native_level: usize,
    native_index: usize,
    path_position: usize,
    row: []const u32,
    start: []const u8,
    steps: []const Step,
};
const TopologyEntry = struct {
    level: usize,
    index: usize,
    parent: usize,
    sibling: usize,
    children: [2]usize,
    path_position: usize,
};

fn nativePathPosition(level: usize, index: usize) usize {
    var at_level = level;
    var at_index = index;
    var place: usize = 1;
    var position: usize = 0;
    while (at_level > 0) : (at_level -= 1) {
        position += place * (if (at_level == 1) at_index & 1 else (at_index >> 1) & 1);
        place *= 2;
        at_index = topology.parent(@intCast(at_level), at_index);
    }
    return position;
}

fn hex(allocator: std.mem.Allocator, bytes: []const u8) ![]const u8 {
    const digits = "0123456789abcdef";
    const out = try allocator.alloc(u8, 2 * bytes.len);
    for (bytes, 0..) |byte, i| {
        out[2 * i] = digits[byte >> 4];
        out[2 * i + 1] = digits[byte & 15];
    }
    return out;
}

fn words(allocator: std.mem.Allocator, values: []const M31) ![]const u32 {
    const out = try allocator.alloc(u32, values.len);
    for (values, out) |value, *word| word.* = value.toU32();
    return out;
}

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const k: u32 = 5;
    const height_count = 3;
    const raw = [_]usize{ 5, 12, 5 };
    var source_values: [height_count][2][]M31 = undefined;
    var source_words: [height_count][2][]const u32 = undefined;
    var source: [height_count][]const []const M31 = undefined;
    var source_json: [height_count][]const []const u32 = undefined;
    var columns: [height_count]u16 = undefined;
    for (0..height_count) |height| {
        const width: usize = if (height == 1) 1 else 2;
        columns[height] = @intCast(width);
        for (0..width) |col| {
            const count = @as(usize, 1) << @intCast(k - @as(u32, @intCast(height)));
            source_values[height][col] = try allocator.alloc(M31, count);
            for (source_values[height][col], 0..) |*value, index|
                value.* = M31.fromCanonical(@intCast(1000 + 100 * height + 20 * col + index));
            source_words[height][col] = try words(allocator, source_values[height][col]);
        }
        source[height] = source_values[height][0..width];
        source_json[height] = source_words[height][0..width];
    }
    var commitment = try Commitment.commitSparse(allocator, source[0..], raw.len);
    defer commitment.deinit();
    try audit.auditCommitment(commitment);
    const wire = try commitment.encodeSparseOpenings(allocator, &raw);
    var profile = core.pcs.transposed_merkle_sparse.Profile{
        .largest_log_size = k,
        .height_count = height_count,
        .columns = [_]u16{0} ** 8,
        .query_count = raw.len,
    };
    @memcpy(profile.columns[0..height_count], &columns);
    var captured = try audit.verifyAndCapture(allocator, wire, profile, commitment.root(), &raw);
    defer captured.deinit();
    const openings = try allocator.alloc(Opening, raw.len * height_count * 2);
    var next: usize = 0;
    for (raw, 0..) |_, query| for (0..height_count) |height| for (0..2) |j| {
        var opening = try captured.openingAt(height, query, j);
        defer opening.deinit(allocator);
        const steps = try allocator.alloc(Step, opening.steps.len);
        for (opening.steps, steps) |step, *output| {
            output.* = .{
                .sibling = try hex(allocator, &step.sibling),
                .inserted_row = if (step.inserted_row) |row| try words(allocator, row) else null,
            };
        }
        const start: Hash = if (opening.children) |children|
            core.pcs.transposed_merkle_cascade.hashInserted(children.left, children.right, opening.row)
        else core.pcs.transposed_merkle_cascade.hashLeaf(opening.row);
        openings[next] = .{
            .height = height,
            .query = query,
            .j = j,
            .native_level = opening.native_level,
            .native_index = opening.native_index,
            .path_position = opening.path_position,
            .row = try words(allocator, opening.row),
            .start = try hex(allocator, &start),
            .steps = steps,
        };
        next += 1;
    };
    const root = commitment.root();
    const entries = try allocator.alloc(TopologyEntry, (@as(usize, 1) << @intCast(k + 1)) - 2);
    var next_entry: usize = 0;
    for (1..k + 1) |level| for (0..(@as(usize, 1) << @intCast(level))) |index| {
        const up = topology.parent(@intCast(level), index);
        entries[next_entry] = .{
            .level = level,
            .index = index,
            .parent = up,
            .sibling = topology.sibling(@intCast(level), index),
            .children = topology.children(@intCast(level - 1), up),
            .path_position = nativePathPosition(level, index),
        };
        next_entry += 1;
    };
    const fixture = .{
        .largest_log_size = k,
        .height_count = height_count,
        .columns = columns,
        .raw_queries = raw,
        .source_columns = source_json,
        .root = try hex(allocator, &root),
        .wire = try hex(allocator, wire),
        .openings = openings,
        .topology = entries,
    };
    const json = try std.json.Stringify.valueAlloc(allocator, fixture, .{});
    try std.fs.File.stdout().writeAll(json);
}
