//! Independently build four complete trees, then audit a PCS-shaped capture.
const std = @import("std");
const core = @import("stwo_core");
const admission = @import("pcs_lifted_capture_admission");

const M31 = core.fields.m31.M31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Capture = core.verifier.ProofCapture(H);
const Path = core.vcs_lifted.verifier.MerklePathCapture(H);

const Fixture = struct {
    raw: [4]usize = .{ 7, 3, 1, 7 },
    roots: [4]H.Hash = undefined,
    log_buffers: [4][2]u32 = undefined,
    logs: [4][]u32 = undefined,
    positions: [4][4]usize = undefined,
    siblings: [4][12]H.Hash = undefined,
    paths: [4]Path = undefined,
    nodes: [4][16]H.Hash = undefined,
    values: [24]M31 = undefined,
    capture: Capture = undefined,
    value_count: usize = 0,
};

fn project(position: usize, source: u32, target: u32) usize {
    return ((position >> @intCast(source - target + 1)) << 1) | (position & 1);
}

fn columnValue(tree: usize, column: usize, index: usize) M31 {
    return M31.fromCanonical(@intCast(100 * tree + 20 * column + index + 1));
}

fn at(f: *const Fixture, tree: usize, column: usize, leaf: usize, height: u32, malicious: bool) M31 {
    const index = project(leaf, height, f.logs[tree][column]);
    const value = columnValue(tree, column, index);
    // A malicious tree can authenticate two different values for one
    // projected index. Its Merkle paths are still completely valid.
    if (malicious and tree == 1 and column == 1 and leaf == 3)
        return value.add(M31.one());
    return value;
}

fn makeFixture(f: *Fixture, malicious: bool) void {
    f.raw = .{ 7, 3, 1, 7 };
    f.log_buffers = .{
        .{ 2, 0 }, // preprocessed tree at height 2
        .{ 3, 2 }, // unsorted column logs at height 3
        .{ 2, 3 },
        .{ 3, 0 },
    };
    const widths = [_]usize{ 1, 2, 2, 1 };
    for (0..4) |tree| f.logs[tree] = f.log_buffers[tree][0..widths[tree]];

    for (0..4) |tree| {
        const height: u32 = if (tree == 0) 2 else 3;
        const leaf_count: usize = @as(usize, 1) << @intCast(height);
        for (0..leaf_count) |leaf| {
            var row: [2]M31 = undefined;
            for (0..widths[tree]) |slot| {
                const column: usize = if (tree == 1) 1 - slot else slot;
                row[slot] = at(f, tree, column, leaf, height, malicious);
            }
            var hasher = H.defaultWithInitialState();
            hasher.updateLeaf(row[0..widths[tree]]);
            f.nodes[tree][leaf_count + leaf] = hasher.finalize();
        }
        var node = leaf_count - 1;
        while (node > 0) : (node -= 1)
            f.nodes[tree][node] = H.hashChildren(.{
                .left = f.nodes[tree][2 * node],
                .right = f.nodes[tree][2 * node + 1],
            });
        f.roots[tree] = f.nodes[tree][1];

        for (f.raw, 0..) |raw, slot| {
            const leaf = project(raw, 3, height);
            f.positions[tree][slot] = leaf;
            var index = leaf_count + leaf;
            for (0..height) |level| {
                f.siblings[tree][slot * height + level] = f.nodes[tree][index ^ 1];
                index /= 2;
            }
        }
        f.paths[tree] = .{
            .positions = f.positions[tree][0..],
            .path_depth = height,
            .siblings = f.siblings[tree][0 .. f.raw.len * height],
        };
    }

    f.value_count = 0;
    for (0..4) |tree| {
        const height: u32 = if (tree == 0) 2 else 3;
        for (0..widths[tree]) |column| {
            for (f.raw) |raw| {
                const leaf = project(raw, 3, height);
                f.values[f.value_count] = at(f, tree, column, leaf, height, malicious);
                f.value_count += 1;
            }
        }
    }
    f.capture.queries = .{ .raw = f.raw[0..], .unique = f.raw[0..0] };
    f.capture.commitments = f.roots[0..];
    f.capture.column_log_sizes = f.logs[0..];
    f.capture.trace_paths = f.paths[0..];
    f.capture.queried_values = f.values[0..f.value_count];
}

fn config() !core.pcs.config_v2.PcsConfigV2 {
    const fri = try core.pcs.config_v2.FriConfigV2.init(0, 0, 1, 4, 1);
    return .{
        .fri_config = fri,
        .trace_lifting_log_size = 3,
        .preprocessed_lifting_log_size = 2,
    };
}

test "PCS lifted capture: four roots, heterogeneous logs, projected rows and duplicate raw queries" {
    var fixture: Fixture = undefined;
    makeFixture(&fixture, false);
    try admission.validate(std.testing.allocator, try config(), &fixture.roots, &fixture.capture);
}

test "PCS lifted capture: a valid malicious Merkle tree with inconsistent projected values is rejected" {
    var fixture: Fixture = undefined;
    makeFixture(&fixture, true);
    // The constructor hashed every malicious leaf and made complete paths to
    // the corresponding root. Rejection is specifically cross-leaf lifting.
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(std.testing.allocator, try config(), &fixture.roots, &fixture.capture));
}

test "PCS lifted capture: corrupted roots, values, paths, positions and shape reject" {
    const allocator = std.testing.allocator;
    var fixture: Fixture = undefined;
    makeFixture(&fixture, false);
    const pcs = try config();
    fixture.capture.commitments[1][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(allocator, pcs, &fixture.roots, &fixture.capture));
    fixture.capture.commitments[1][0] ^= 1;
    fixture.values[0] = fixture.values[0].add(M31.one());
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(allocator, pcs, &fixture.roots, &fixture.capture));
    makeFixture(&fixture, false);
    fixture.siblings[2][0][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(allocator, pcs, &fixture.roots, &fixture.capture));
    makeFixture(&fixture, false);
    fixture.positions[0][0] ^= 2;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(allocator, pcs, &fixture.roots, &fixture.capture));
    makeFixture(&fixture, false);
    fixture.capture.queried_values = fixture.values[0 .. fixture.value_count - 1];
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        admission.validate(allocator, pcs, &fixture.roots, &fixture.capture));
}
