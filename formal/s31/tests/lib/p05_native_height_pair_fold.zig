//! Experimental P05 source-height first fold. The verifier-side input is the
//! four-root admitted row capture plus verifier-owned scheme/AIR/proof inputs.
//! Only complete authenticated native source pairs are folded. This is not a
//! multi-domain FRI verifier or an oracle degree test.
const std = @import("std");
const core = @import("stwo_core");
const own = @import("s31_own_adapter");
const roster = @import("s31_p05_roster");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Capture = core.verifier.ProofCapture(H);
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;

const Row = struct { position: usize, value: QM31 };

fn rowLess(_: void, lhs: Row, rhs: Row) bool {
    return lhs.position < rhs.position;
}

pub const PairFold = struct {
    /// Native source-domain pair, in bit-reversed codeword order.
    source_pair_start: usize,
    original_pair: [2]QM31,
    own_quotient_pair: [2]QM31,
    original_fold: QM31,
    own_quotient_fold: QM31,
    /// Candidate linear combination; its challenge schedule is not mapped
    /// to the published degree-corrected multi-domain theorem.
    combined_fold: QM31,
};

pub const WordFold = struct {
    tree_index: usize,
    column_index: usize,
    source_log_size: u32,
    sample_index: usize,
    kind: own.SampleKind,
    pairs: []PairFold,
};

pub const NativeHeightFolds = struct {
    words: []WordFold,

    pub fn deinit(self: *NativeHeightFolds, allocator: std.mem.Allocator) void {
        for (self.words) |word| allocator.free(word.pairs);
        allocator.free(self.words);
        self.* = undefined;
    }
};

/// Recompute every own quotient at its source-height circle point, then apply
/// pinned native circle-to-line folding to both original and own quotient.
/// `fold_alpha` and `pair_beta` are externally supplied test challenges here;
/// a real profile must draw and bind them after the four existing root epochs.
/// Missing pair siblings fail closed because the old capture does not contain
/// a separate authenticated native-height FRI decommitment witness.
pub fn reconstruct(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    proof_roots: []const H.Hash,
    capture: *const Capture,
    scheme: anytype,
    handles: []const core.air.components.Component,
    accepted_values: core.pcs.TreeVec([][]QM31),
    include_all_preprocessed_columns: bool,
    fold_alpha: QM31,
    pair_beta: QM31,
) !NativeHeightFolds {
    const claims = try roster.derive(
        H,
        allocator,
        pcs,
        scheme,
        handles,
        accepted_values,
        capture,
        include_all_preprocessed_columns,
    );
    defer allocator.free(claims);
    var admitted = try own.reconstruct(allocator, pcs, proof_roots, capture, claims);
    defer admitted.deinit(allocator);
    return foldAdmittedRowsForControl(allocator, pcs, &admitted, fold_alpha, pair_beta);
}

/// Low-level algebra control for an already admitted sampled-row witness. The
/// only verifier-facing entrypoint is `reconstruct`, which derives its claims
/// from the accepted scheme, AIR masks, and proof values.
pub fn foldAdmittedRowsForControl(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    admitted: *const own.OwnQuotientWords,
    fold_alpha: QM31,
    pair_beta: QM31,
) !NativeHeightFolds {
    const out = try allocator.alloc(WordFold, admitted.words.len);
    var initialized: usize = 0;
    errdefer {
        for (out[0..initialized]) |word| allocator.free(word.pairs);
        allocator.free(out);
    }
    var fold_workspace = try core.fri.FoldCircleWorkspace.init(allocator, 1);
    defer fold_workspace.deinit(allocator);

    for (admitted.words) |word| {
        if (word.source_log_size > pcs.trace_lifting_log_size)
            return error.InvalidP05NativeSourceHeight;
        // The pinned prover evaluates a shorter committed column at the
        // lifted point repeatedly doubled down to that column's domain.
        // Its native-height quotient must use this normalized OOD point,
        // not the raw lifted sample point used by legacy friAnswers.
        const native_point = word.point.repeatedDouble(
            pcs.trace_lifting_log_size - word.source_log_size,
        );
        if (word.projected_positions.len != word.original_values.len or
            word.projected_positions.len == 0)
            return error.InvalidP05NativePairShape;
        const rows = try allocator.alloc(Row, word.projected_positions.len);
        defer allocator.free(rows);
        for (word.projected_positions, word.original_values, rows) |position, value, *row| {
            row.* = .{ .position = position, .value = value };
        }
        std.sort.heap(Row, rows, {}, rowLess);
        var unique_count: usize = 0;
        for (rows) |row| {
            if (unique_count != 0 and rows[unique_count - 1].position == row.position) {
                if (!rows[unique_count - 1].value.eql(row.value))
                    return error.InconsistentP05SourceRow;
                continue;
            }
            rows[unique_count] = row;
            unique_count += 1;
        }
        if (unique_count % 2 != 0) return error.MissingP05NativePair;
        const pairs = try allocator.alloc(PairFold, unique_count / 2);
        errdefer allocator.free(pairs);
        const source_domain = core.poly.circle.canonic.CanonicCoset
            .new(word.source_log_size).circleDomain();
        for (pairs, 0..) |*pair, group_index| {
            const left = rows[2 * group_index];
            const right = rows[2 * group_index + 1];
            if ((left.position & 1) != 0 or right.position != left.position + 1)
                return error.MissingP05NativePair;
            const initial = core.utils.bitReverseIndex(left.position, word.source_log_size);
            const pair_domain = core.poly.circle.domain.CircleDomain.new(
                core.circle.Coset.new(source_domain.indexAt(initial), 0),
            );
            const original_pair = [2]QM31{ left.value, right.value };
            var quotient_pair: [2]QM31 = undefined;
            for (original_pair, &quotient_pair, 0..) |value, *quotient, side| {
                const components = value.toM31Array();
                if (!components[1].isZero() or !components[2].isZero() or
                    !components[3].isZero())
                    return error.InvalidP05NativeSourceValue;
                const position = left.position + side;
                const row = source_domain.at(core.utils.bitReverseIndex(
                    position,
                    word.source_log_size,
                ));
                quotient.* = try own.ownQuotientAt(native_point, word.claim, components[0], row);
            }
            var folded_original = [1]QM31{QM31.zero()};
            var folded_quotient = [1]QM31{QM31.zero()};
            try core.fri.foldCircleIntoLineWithWorkspace(
                allocator,
                &folded_original,
                &original_pair,
                pair_domain,
                fold_alpha,
                &fold_workspace,
            );
            try core.fri.foldCircleIntoLineWithWorkspace(
                allocator,
                &folded_quotient,
                &quotient_pair,
                pair_domain,
                fold_alpha,
                &fold_workspace,
            );
            pair.* = .{
                .source_pair_start = left.position,
                .original_pair = original_pair,
                .own_quotient_pair = quotient_pair,
                .original_fold = folded_original[0],
                .own_quotient_fold = folded_quotient[0],
                .combined_fold = folded_original[0].add(folded_quotient[0].mul(pair_beta)),
            };
        }
        out[initialized] = .{
            .tree_index = word.tree_index,
            .column_index = word.column_index,
            .source_log_size = word.source_log_size,
            .sample_index = word.sample_index,
            .kind = word.kind,
            .pairs = pairs,
        };
        initialized += 1;
    }
    return .{ .words = out };
}
