//! Recommit a public direct-Gate base trace for diagnostic comparison with a
//! proof's main-tree root. This does not authenticate arbitrary proof openings.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const prover = @import("stwo_prover_engine");

const M31 = core.fields.m31.M31;
const ColumnEvaluation = prover.pcs.ColumnEvaluation;
const Engine = cpu.Internal.Engine;
const Channel = cpu.Internal.Channel;

/// Recompute tree 1 from precisely the supplied `writeBase` columns. Tree 0
/// is installed first because the revision's lifting height depends on the
/// tree index. The caller must separately check the source, assignment, and
/// parsed proof before interpreting equality with a proof commitment.
pub fn root(
    allocator: std.mem.Allocator,
    pp: *const circuit.common.direct_arithmetic.Circuit,
    base_columns: []const ColumnEvaluation,
    pcs: core.pcs.config_v2.PcsConfigV2,
) ![32]u8 {
    if (base_columns.len != circuit.witness.direct_arithmetic.main_width)
        return error.InvalidDirectTraceShape;
    var fixed = try cpu.direct_arithmetic.PreprocessedCommitment.build(allocator, pp, pcs);
    defer fixed.deinit(allocator);
    var scheme = try Engine.initRevision(allocator, pcs);
    defer Engine.deinit(&scheme, allocator);
    scheme.setStorePolynomialsCoefficients();
    var channel = Channel{};
    {
        var lease = fixed.tree.retainShared();
        errdefer lease.deinit(allocator);
        try scheme.appendCommittedTree(allocator, lease, &channel);
    }
    const copied = try cloneColumns(allocator, base_columns);
    try Engine.commit(&scheme, allocator, copied, null, &channel);
    try Engine.flushPendingCommit(&scheme, allocator, &channel);
    if (scheme.trees.items.len != 2) return error.InvalidDirectCommitmentShape;
    return scheme.trees.items[1].commitment.root();
}

fn cloneColumns(allocator: std.mem.Allocator, source: []const ColumnEvaluation) ![]ColumnEvaluation {
    const owned = try allocator.alloc(ColumnEvaluation, source.len);
    var ready: usize = 0;
    errdefer {
        for (owned[0..ready]) |entry| allocator.free(entry.values);
        allocator.free(owned);
    }
    for (source, owned) |entry, *slot| {
        slot.* = .{ .log_size = entry.log_size, .values = try allocator.dupe(M31, entry.values) };
        ready += 1;
    }
    return owned;
}
