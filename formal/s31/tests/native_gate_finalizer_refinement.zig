//! Numeric differential for the exact native two-batch Gate LogUp finalizer.
//! The independent arithmetic below is over QM31 values; it does not claim
//! that a proof opening authenticates these samples as committed columns.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const Eval = circuit.stark_verifier.constraint_eval;
const Term = circuit.stark_verifier.logup.LogupTerm(QM31);
const Column = Eval.InteractionAtOods(QM31);

const Numeric = struct {
    pub const Var = QM31;

    pub fn zero(_: *const Numeric) Var { return QM31.zero(); }
    pub fn constant(_: *Numeric, value: QM31) !Var { return value; }
    pub fn add(_: *Numeric, left: Var, right: Var) !Var { return left.add(right); }
    pub fn sub(_: *Numeric, left: Var, right: Var) !Var { return left.sub(right); }
    pub fn mul(_: *Numeric, left: Var, right: Var) !Var { return left.mul(right); }
    pub fn inv(_: *Numeric, value: Var) !Var { return value.inv(); }
};

const Data = struct {
    n: QM31,
    pub fn nInstances(self: @This()) QM31 { return self.n; }
};

fn base(value: u32) QM31 { return QM31.fromBase(M31.fromCanonical(value)); }

fn columns(first: QM31, previous: QM31, last: QM31) [8]Column {
    const zero = QM31.zero();
    return .{
        .{ .at_oods = first }, .{ .at_oods = zero },
        .{ .at_oods = zero }, .{ .at_oods = zero },
        .{ .at_oods = last, .at_prev = previous },
        .{ .at_oods = zero, .at_prev = zero },
        .{ .at_oods = zero, .at_prev = zero },
        .{ .at_oods = zero, .at_prev = zero },
    };
}

fn native(allocator: std.mem.Allocator, rho: QM31, prior: QM31,
    terms: [3]Term, samples: []const Column, claim: QM31) !QM31 {
    var ctx: Numeric = .{};
    var preprocessed: Eval.ColumnMap(QM31) = .empty;
    var public_params: Eval.ColumnMap(QM31) = .empty;
    var acc = Eval.CompositionConstraintAccumulator(Numeric).init(
        allocator, &ctx, &preprocessed, &public_params, rho,
        .{ QM31.zero(), QM31.zero() },
    );
    defer acc.deinit();
    acc.accumulation = prior;
    for (terms) |term| try acc.terms.append(allocator, term);
    try acc.finalizeLogupInPairs(&ctx, samples, Data{ .n = base(8) }, claim);
    return acc.finalize();
}

fn independent(rho: QM31, prior: QM31, terms: [3]Term,
    first: QM31, previous: QM31, last: QM31, claim: QM31) !QM31 {
    const pair_den = terms[0].denominator.mul(terms[1].denominator);
    const pair_num = terms[1].numerator.mul(terms[0].denominator)
        .add(terms[0].numerator.mul(terms[1].denominator));
    const pair_residual = first.mul(pair_den).sub(pair_num);
    const shift = claim.mul(try base(8).inv());
    const single_residual = last.sub(previous).sub(first).add(shift)
        .mul(terms[2].denominator).sub(terms[2].numerator);
    return prior.mul(rho).mul(rho).add(pair_residual.mul(rho)).add(single_residual);
}

test "native Gate finalizer matches independent 11-residual tail under hostile samples" {
    const allocator = std.testing.allocator;
    const terms = [3]Term{
        .{ .numerator = base(1), .denominator = base(2) },
        .{ .numerator = base(3), .denominator = base(5) },
        .{ .numerator = base(2), .denominator = base(7) },
    };
    const first = (try base(1).div(base(2))).add(try base(3).div(base(5)));
    const previous = base(17);
    const claim = base(11);
    const last = previous.add(first).add(try base(2).div(base(7)))
        .sub(try claim.div(base(8)));
    const rhos = [_]QM31{ QM31.zero(), QM31.one(), base(3), QM31.fromU32Unchecked(4, 1, 2, 3) };
    for (rhos) |rho| {
        const prior = base(13);
        const variants = [_]struct { first: QM31, previous: QM31, last: QM31, claim: QM31 }{
            .{ .first = first, .previous = previous, .last = last, .claim = claim },
            .{ .first = first.add(QM31.one()), .previous = previous, .last = last, .claim = claim },
            .{ .first = first, .previous = previous.add(QM31.one()), .last = last, .claim = claim },
            .{ .first = first, .previous = previous, .last = last.add(QM31.one()), .claim = claim },
            .{ .first = first, .previous = previous, .last = last, .claim = claim.add(QM31.one()) },
        };
        for (variants) |variant| {
            const samples = columns(variant.first, variant.previous, variant.last);
            const observed = try native(allocator, rho, prior, terms, &samples, variant.claim);
            const expected = try independent(rho, prior, terms,
                variant.first, variant.previous, variant.last, variant.claim);
            try std.testing.expect(observed.eql(expected));
        }
    }

    // With a zero arithmetic prefix, these valid samples close at every rho.
    const valid = columns(first, previous, last);
    for (rhos) |rho| {
        try std.testing.expect((try native(allocator, rho, QM31.zero(), terms, &valid, claim)).isZero());
    }
    // A changed public claim and a wrong previous-row sample must be detected.
    try std.testing.expect(!(try native(allocator, QM31.one(), QM31.zero(), terms,
        &valid, claim.add(QM31.one()))).isZero());
    const wrong_previous = columns(first, previous.add(QM31.one()), last);
    try std.testing.expect(!(try native(allocator, QM31.one(), QM31.zero(), terms,
        &wrong_previous, claim)).isZero());

    // One bad coefficient can cancel a false pair residual with the false
    // singleton residual: changing first by 1 gives 10*rho - 7.
    const wrong_first = columns(first.add(QM31.one()), previous, last);
    const cancelling_rho = try base(7).div(base(10));
    try std.testing.expect((try native(allocator, cancelling_rho, QM31.zero(), terms,
        &wrong_first, claim)).isZero());
    try std.testing.expect(!(try native(allocator, QM31.one(), QM31.zero(), terms,
        &wrong_first, claim)).isZero());

    var malformed = valid;
    malformed[4].at_prev = null;
    try std.testing.expectError(error.MissingPreviousRowSample,
        native(allocator, QM31.one(), QM31.zero(), terms, &malformed, claim));
    malformed = valid;
    malformed[0].at_prev = QM31.zero();
    try std.testing.expectError(error.UnexpectedPreviousRowSample,
        native(allocator, QM31.one(), QM31.zero(), terms, &malformed, claim));
    try std.testing.expectError(error.InteractionColumnCountMismatch,
        native(allocator, QM31.one(), QM31.zero(), terms, valid[0..7], claim));
}
