//! Experimental P05 sampled-row relation. Each authenticated source column is
//! paired separately with every native two-point OOD quotient it owns.
//! This does not assert a whole-oracle degree bound or admit a proof profile.
const std = @import("std");
const core = @import("stwo_core");
const lifted = @import("s31_lifted_capture");
const roster = @import("s31_p05_roster");

const M31 = core.fields.m31.M31;
const CM31 = core.fields.cm31.CM31;
const QM31 = core.fields.qm31.QM31;
const CirclePointM31 = core.circle.CirclePointM31;
const CirclePointQM31 = core.circle.CirclePointQM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Capture = core.verifier.ProofCapture(H);
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;

/// Caller-supplied ordered OOD claim. Here it is an external test oracle,
/// checked against capture but not authenticated by this adapter. A future v2
/// verifier must derive it from its accepted AIR/OOD relation and public key.
pub const ExpectedClaim = roster.Claim;

pub const SampleKind = enum { explicit, periodic };

pub const OwnQuotientWord = struct {
    tree_index: usize,
    column_index: usize,
    source_log_size: u32,
    sample_index: usize,
    kind: SampleKind,
    /// OOD pair owned by this exact source-column sample. Periodicity uses
    /// the shifted second point with the same claimed value.
    point: CirclePointQM31,
    claim: QM31,
    /// Exact projected source position for every raw lifted query.
    projected_positions: []usize,
    /// Authenticated source value and its own two-point quotient at the
    /// *lifted native PCS row point*. These words have no degree certificate.
    original_values: []QM31,
    quotient_values: []QM31,

    fn deinit(self: *OwnQuotientWord, allocator: std.mem.Allocator) void {
        allocator.free(self.projected_positions);
        allocator.free(self.original_values);
        allocator.free(self.quotient_values);
        self.* = undefined;
    }
};

pub const OwnQuotientWords = struct {
    words: []OwnQuotientWord,

    pub fn deinit(self: *OwnQuotientWords, allocator: std.mem.Allocator) void {
        for (self.words) |*word| word.deinit(allocator);
        allocator.free(self.words);
        self.* = undefined;
    }
};

/// Exact native numerator/denominator law for one *unweighted* source word.
/// `complexConjugateLineCoeffs` derives the conjugate OOD point and value;
/// `denominator` is the CM31 determinant used by native row evaluation.
pub fn ownQuotientAt(
    point: CirclePointQM31,
    claim: QM31,
    value: M31,
    row: CirclePointM31,
) !QM31 {
    const prx = point.x.c0;
    const pry = point.y.c0;
    const pix = point.x.c1;
    const piy = point.y.c1;
    const denominator = prx.sub(CM31.fromBase(row.x)).mul(piy)
        .sub(pry.sub(CM31.fromBase(row.y)).mul(pix));
    if (denominator.isZero()) return error.ZeroOwnQuotientDivisor;
    if (!point.x.square().add(point.y.square()).eql(QM31.one()))
        return error.InvalidOodCirclePoint;
    const line = try core.constraints.complexConjugateLineCoeffs(point, claim, QM31.one());
    const numerator = line.c.mulM31(value)
        .sub(line.a.mulM31(row.y).add(line.b));
    const quotient = numerator.mulCM31(try denominator.inv());
    if (!quotient.mulCM31(denominator).eql(numerator))
        return error.InvalidOwnQuotientEquation;
    return quotient;
}

fn appendWord(
    allocator: std.mem.Allocator,
    out: []OwnQuotientWord,
    initialized: *usize,
    pcs: PcsConfigV2,
    raw: []const usize,
    source_values: []const M31,
    tree: usize,
    column: usize,
    log: u32,
    sample: usize,
    kind: SampleKind,
    point: CirclePointQM31,
    claim: QM31,
) !void {
    const positions = try core.pcs.utils.prepareTreeQueryPositions(
        allocator,
        raw,
        pcs.trace_lifting_log_size,
        log,
    );
    errdefer allocator.free(positions);
    if (log >= @bitSizeOf(usize)) return error.InvalidSourceHeightProjection;
    const source_rows: usize = @as(usize, 1) << @intCast(log);
    for (positions) |position| {
        if (position >= source_rows) return error.InvalidSourceHeightProjection;
    }
    const originals = try allocator.alloc(QM31, raw.len);
    errdefer allocator.free(originals);
    const quotients = try allocator.alloc(QM31, raw.len);
    errdefer allocator.free(quotients);
    const domain = core.poly.circle.canonic.CanonicCoset.new(pcs.trace_lifting_log_size).circleDomain();
    for (raw, source_values, originals, quotients) |position, value, *original, *quotient| {
        const row = domain.at(core.utils.bitReverseIndex(position, pcs.trace_lifting_log_size));
        original.* = QM31.fromBase(value);
        quotient.* = try ownQuotientAt(point, claim, value, row);
    }
    out[initialized.*] = .{
        .tree_index = tree,
        .column_index = column,
        .source_log_size = log,
        .sample_index = sample,
        .kind = kind,
        .point = point,
        .claim = claim,
        .projected_positions = positions,
        .original_values = originals,
        .quotient_values = quotients,
    };
    initialized.* += 1;
}

/// Fail closed unless every captured mask sample matches an independent,
/// ordered `(tree,column,sample,height,point,value)` roster. A two-sample
/// column additionally gets native's periodicity sample *before* samples 0/1.
/// All four Merkle roots, paths, projections, and raw duplicates are checked
/// before any claim is used. The output is local row data, never proof admission.
pub fn reconstruct(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    proof_roots: []const H.Hash,
    capture: *const Capture,
    expected_claims: []const ExpectedClaim,
) !OwnQuotientWords {
    try lifted.validate(allocator, pcs, proof_roots, capture);
    if (capture.sampled_points.len != capture.column_log_sizes.len)
        return error.InvalidP05ClaimRoster;
    const raw = capture.queries.raw;
    var claim_count: usize = 0;
    var word_count: usize = 0;
    for (capture.column_log_sizes, capture.sampled_points) |logs, point_columns| {
        if (logs.len != point_columns.len) return error.InvalidP05ClaimRoster;
        for (point_columns) |points| {
            if (points.len < 1 or points.len > 2) return error.UnsupportedP05SampleShape;
            claim_count = std.math.add(usize, claim_count, points.len) catch
                return error.InvalidP05ClaimRoster;
            word_count = std.math.add(usize, word_count, points.len + @intFromBool(points.len == 2)) catch
                return error.InvalidP05ClaimRoster;
        }
    }
    if (claim_count != capture.sampled_values.len or claim_count != expected_claims.len)
        return error.InvalidP05ClaimRoster;
    const out = try allocator.alloc(OwnQuotientWord, word_count);
    var initialized: usize = 0;
    errdefer {
        for (out[0..initialized]) |*word| word.deinit(allocator);
        allocator.free(out);
    }
    var claim_at: usize = 0;
    var value_at: usize = 0;
    for (capture.column_log_sizes, capture.sampled_points, 0..) |logs, point_columns, tree| {
        for (logs, point_columns, 0..) |log, points, column| {
            const value_end = std.math.add(usize, value_at, raw.len) catch
                return error.InvalidP05ClaimRoster;
            if (value_end > capture.queried_values.len) return error.InvalidP05ClaimRoster;
            const source_values = capture.queried_values[value_at..value_end];
            value_at = value_end;
            const first_claim = claim_at;
            for (points, 0..) |point, sample| {
                const expected = expected_claims[claim_at];
                const value = capture.sampled_values[claim_at];
                if (expected.tree_index != tree or expected.column_index != column or
                    expected.sample_index != sample or expected.source_log_size != log or
                    !expected.point.eql(point) or !expected.value.eql(value))
                    return error.InvalidP05ClaimRoster;
                claim_at += 1;
            }
            if (points.len == 2) {
                const shift = core.poly.circle.canonic.CanonicCoset.new(pcs.trace_lifting_log_size)
                    .step().repeatedDouble(log);
                const periodic_point = points[1].add(.{
                    .x = QM31.fromBase(shift.x),
                    .y = QM31.fromBase(shift.y),
                });
                try appendWord(allocator, out, &initialized, pcs, raw, source_values, tree, column, log, 1, .periodic, periodic_point, capture.sampled_values[first_claim + 1]);
            }
            for (points, 0..) |point, sample| {
                try appendWord(allocator, out, &initialized, pcs, raw, source_values, tree, column, log, sample, .explicit, point, capture.sampled_values[first_claim + sample]);
            }
        }
    }
    if (value_at != capture.queried_values.len or claim_at != expected_claims.len or
        initialized != word_count)
        return error.InvalidP05ClaimRoster;
    return .{ .words = out };
}
