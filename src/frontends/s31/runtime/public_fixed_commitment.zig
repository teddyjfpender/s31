//! Recommit an explicit public direct-Gate fixed-column export. This is a
//! diagnostic equality check against a sealed key, not a proof-opening check.

const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const circuit = @import("stwo_circuit_frontend");

const M31 = core.fields.m31.M31;
const ColumnEvaluation = prover.pcs.ColumnEvaluation;
const width = circuit.common.direct_arithmetic.N_COLUMNS;

/// Uses the exact preprocessed PCS preparation and Merkle implementation, but
/// takes the eight 512-word columns as independent input rather than rebuilding
/// them from a circuit. Column order and every canonical word affect the root.
pub fn rootFromWords(
    allocator: std.mem.Allocator,
    words: [width][]const u32,
) ![32]u8 {
    var evaluations: [width]ColumnEvaluation = undefined;
    var allocated: usize = 0;
    defer for (evaluations[0..allocated]) |evaluation| allocator.free(evaluation.values);
    for (words, &evaluations) |column, *evaluation| {
        if (column.len != 512) return error.InvalidDirectTraceShape;
        const values = try allocator.alloc(M31, 512);
        evaluation.* = .{ .log_size = 9, .values = values };
        allocated += 1;
        for (column, values) |word, *value| {
            if (word >= 2147483647) return error.NonCanonicalM31Word;
            value.* = M31.fromCanonical(word);
        }
    }
    var twiddles = prover.poly.twiddle_source.TwiddleSource.initOwned(allocator);
    defer twiddles.deinit(allocator);
    var prepared = try prover.pcs.column_preparation.prepareColumnsForCommitBorrowedForBackend(
        prover.pcs.HostMerkleBackend,
        allocator,
        &evaluations,
        1,
        .never,
        &twiddles,
    );
    var tree = prover.pcs.CommitmentTreeProver(
        core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel.MerkleHasher,
    ).initPrepared(allocator, &prepared, null) catch |err| {
        prepared.deinit(allocator);
        return err;
    };
    defer tree.deinit(allocator);
    return tree.root();
}
