//! Unsigned fixed-width quotient and remainder in circuit AIR profiles.
//!
//! The quotient-product-remainder equation is fused into base-256 columns.
//! Each column is an integer equality, since its two sides are strictly
//! smaller than the M31 modulus. The high product columns and terminal carry
//! are included, so multiplication cannot wrap at the operand width.

const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const std = @import("std");
const integer_bits = @import("integer_bits.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Var = circuit.builder.Var;
const Context = circuit.builder.Context;

pub const Division = struct { quotient: []Var, remainder: []Var };
pub const Witness = struct { quotient: u128, remainder: u128 };

const Bytes = struct { wires: []Var, values: []u32 };

fn hint(comptime V: type, value: u32) V {
    return circuit.builder.ivalue.fromQm31(V, QM31.fromBase(M31.fromCanonical(value)));
}

fn valueOf(comptime V: type, ctx: *Context(V), wire: Var) u32 {
    return if (comptime V == QM31) ctx.get(wire).toM31Array()[0].v else 0;
}

fn value128(comptime V: type, ctx: *Context(V), words: []const Var) u128 {
    var value: u128 = 0;
    for (words, 0..) |word, i|
        value |= @as(u128, valueOf(V, ctx, word)) << @as(u7, @intCast(16 * i));
    return value;
}

fn constrainByte(comptime V: type, ctx: *Context(V), word: Var) !void {
    const value = valueOf(V, ctx, word);
    const scaled = try ctx.guessU16(hint(V, (value * 256) & 0xffff));
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    try ctx.eq(try ctx.mul(word, base), scaled);
}

fn assertEqualArithmetic(comptime V: type, ctx: *Context(V), lhs: Var, rhs: Var) !void {
    const difference = try ctx.sub(lhs, rhs);
    const anchor = try ctx.newVar(circuit.builder.ivalue.fromQm31(V, QM31.zero()));
    try ctx.addInto(anchor, difference, anchor);
}

fn boundedByte(comptime V: type, ctx: *Context(V), value: u32) !Var {
    const word = try ctx.guessU16(hint(V, value));
    try constrainByte(V, ctx, word);
    return word;
}

fn boundedByteArithmetic(comptime V: type, ctx: *Context(V), value: u32) !Var {
    const word = try ctx.guess(hint(V, value));
    _ = try integer_bits.decomposeByteArithmetic(V, ctx, word);
    return word;
}

fn splitWordArithmetic(comptime V: type, ctx: *Context(V), word: Var) !Bytes {
    const value = valueOf(V, ctx, word);
    const values = try ctx.scratch().alloc(u32, 2);
    values[0] = value & 255;
    values[1] = (value >> 8) & 255;
    const wires = try ctx.scratch().alloc(Var, 2);
    wires[0] = try boundedByteArithmetic(V, ctx, values[0]);
    wires[1] = try boundedByteArithmetic(V, ctx, values[1]);
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    try assertEqualArithmetic(V, ctx, word, try ctx.add(wires[0], try ctx.mul(wires[1], base)));
    return .{ .wires = wires, .values = values };
}

fn splitWordsArithmetic(comptime V: type, ctx: *Context(V), words: []const Var) !Bytes {
    const wires = try ctx.scratch().alloc(Var, 2 * words.len);
    const values = try ctx.scratch().alloc(u32, 2 * words.len);
    for (words, 0..) |word, i| {
        const pair = try splitWordArithmetic(V, ctx, word);
        @memcpy(wires[2 * i ..][0..2], pair.wires);
        @memcpy(values[2 * i ..][0..2], pair.values);
    }
    return .{ .wires = wires, .values = values };
}

fn witnessWordsArithmetic(comptime V: type, ctx: *Context(V), value: u128, width: u32) ![]Var {
    const words = try ctx.scratch().alloc(Var, @intCast(width / 16));
    for (words, 0..) |*word, i| {
        const digit: u32 = @intCast((value >> @as(u7, @intCast(16 * i))) & 0xffff);
        word.* = try ctx.guess(hint(V, digit));
    }
    return words;
}

/// Each caller-supplied word is already constrained to u16. For a byte
/// scalar, `byte_bounded` says the preceding integer view proved the tighter
/// range; otherwise it is proved here. The high split byte is bounded by
/// the u16 input bound and the reconstruction equation.
fn splitWords(comptime V: type, ctx: *Context(V), words: []const Var, width: u32, byte_bounded: bool) !Bytes {
    const count: usize = @intCast(width / 8);
    const wires = try ctx.scratch().alloc(Var, count);
    const values = try ctx.scratch().alloc(u32, count);
    if (width == 8) {
        wires[0] = words[0];
        values[0] = valueOf(V, ctx, words[0]);
        if (!byte_bounded) try constrainByte(V, ctx, words[0]);
        return .{ .wires = wires, .values = values };
    }
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    for (words, 0..) |word, i| {
        const value = valueOf(V, ctx, word);
        values[2 * i] = value & 255;
        values[2 * i + 1] = (value >> 8) & 255;
        wires[2 * i] = try boundedByte(V, ctx, values[2 * i]);
        wires[2 * i + 1] = try ctx.guessU16(hint(V, values[2 * i + 1]));
        try ctx.eq(word, try ctx.add(wires[2 * i], try ctx.mul(wires[2 * i + 1], base)));
    }
    return .{ .wires = wires, .values = values };
}

fn witnessWords(comptime V: type, ctx: *Context(V), value: u128, width: u32) ![]Var {
    const length: usize = if (width == 8) 1 else @intCast(width / 16);
    const words = try ctx.scratch().alloc(Var, length);
    for (words, 0..) |*word, i| {
        const digit: u32 = @intCast((value >> @as(u7, @intCast(16 * i))) & 0xffff);
        word.* = try ctx.guessU16(hint(V, digit));
    }
    return words;
}

/// A byte product plus remainder is at most 65,280, so one M31 equality
/// proves the full integer equation without convolution carries. The strict
/// remainder equation is likewise below the field modulus. The bounded flags
/// may only be set when a preceding constraint already proved the two bytes.
fn divRemByteWithWitness(comptime V: type, ctx: *Context(V), numerator: []const Var, denominator: []const Var, numerator_byte_bounded: bool, denominator_byte_bounded: bool, witness: Witness) !Division {
    if (!numerator_byte_bounded) _ = try integer_bits.decomposeByteArithmetic(V, ctx, numerator[0]);
    if (!denominator_byte_bounded) _ = try integer_bits.decomposeByteArithmetic(V, ctx, denominator[0]);
    const quotient_value = std.math.cast(u32, witness.quotient) orelse return error.IntegerOutOfRange;
    const remainder_value = std.math.cast(u32, witness.remainder) orelse return error.IntegerOutOfRange;
    if (quotient_value >= core.fields.m31.Modulus or remainder_value >= core.fields.m31.Modulus) return error.IntegerOutOfRange;
    const quotient = try ctx.guess(hint(V, quotient_value));
    const remainder = try ctx.guess(hint(V, remainder_value));
    _ = try integer_bits.decomposeByteArithmetic(V, ctx, quotient);
    _ = try integer_bits.decomposeByteArithmetic(V, ctx, remainder);
    const d = valueOf(V, ctx, denominator[0]);
    const difference_value = (d +% 256 -% remainder_value -% 1) & 255;
    const difference = try ctx.guess(hint(V, difference_value));
    _ = try integer_bits.decomposeByteArithmetic(V, ctx, difference);
    try assertEqualArithmetic(V, ctx, try ctx.add(try ctx.mul(quotient, denominator[0]), remainder), numerator[0]);
    try assertEqualArithmetic(V, ctx, denominator[0], try ctx.add(try ctx.add(remainder, ctx.one()), difference));
    const q = try ctx.scratch().alloc(Var, 1);
    const r = try ctx.scratch().alloc(Var, 1);
    q[0] = quotient;
    r[0] = remainder;
    return .{ .quotient = q, .remainder = r };
}

/// All 16-bit limbs are split into proved bytes. The full high product and
/// terminal carry prevent width truncation. Each arithmetic column is below
/// the M31 modulus even at width 128, with at most 16 byte products and a
/// 16-bit carry. This path needs no Eq or fixed range-table component.
pub fn divRemArithmeticWithWitness(comptime V: type, ctx: *Context(V), numerator: []const Var, denominator: []const Var, width: u32, witness: Witness) !Division {
    if (width != 16 and width != 32 and width != 64 and width != 128) return error.InvalidIntegerSpec;
    const word_count: usize = @intCast(width / 16);
    if (numerator.len != word_count or denominator.len != word_count) return error.InvalidIntegerOperand;
    const quotient = try witnessWordsArithmetic(V, ctx, witness.quotient, width);
    const remainder = try witnessWordsArithmetic(V, ctx, witness.remainder, width);
    const n = try splitWordsArithmetic(V, ctx, numerator);
    const d = try splitWordsArithmetic(V, ctx, denominator);
    const q = try splitWordsArithmetic(V, ctx, quotient);
    const r = try splitWordsArithmetic(V, ctx, remainder);
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    const count: usize = @intCast(width / 8);

    var incoming = ctx.zero();
    var carry_value: u64 = 0;
    for (0..2 * count) |column| {
        var sum = incoming;
        var integer_sum: u64 = carry_value;
        const first = if (column < count) 0 else column - (count - 1);
        const end = @min(column + 1, count);
        for (first..end) |i| {
            const j = column - i;
            sum = try ctx.add(sum, try ctx.mul(q.wires[i], d.wires[j]));
            integer_sum += @as(u64, q.values[i]) * d.values[j];
        }
        if (column < count) {
            sum = try ctx.add(sum, r.wires[column]);
            integer_sum += r.values[column];
        }
        const digit = if (column < count) n.wires[column] else ctx.zero();
        const outgoing_value: u32 = @intCast(integer_sum / 256);
        const outgoing = try ctx.guess(hint(V, outgoing_value));
        _ = try integer_bits.decomposeWordArithmetic(V, ctx, outgoing, 16);
        try assertEqualArithmetic(V, ctx, sum, try ctx.add(digit, try ctx.mul(outgoing, base)));
        incoming = outgoing;
        carry_value = outgoing_value;
    }
    try assertEqualArithmetic(V, ctx, incoming, ctx.zero());

    // d-r-1>=0, byte by byte. Every equation is strictly below the modulus.
    var borrow = ctx.one();
    var borrow_value: u32 = 1;
    for (0..count) |i| {
        const next_value: u32 = @intFromBool(d.values[i] < r.values[i] + borrow_value);
        const diff_value = (d.values[i] + 256 - r.values[i] - borrow_value) & 255;
        const next = try ctx.guess(hint(V, next_value));
        try assertEqualArithmetic(V, ctx, try ctx.mul(next, next), next);
        const diff = try boundedByteArithmetic(V, ctx, diff_value);
        try assertEqualArithmetic(V, ctx,
            try ctx.add(d.wires[i], try ctx.mul(next, base)),
            try ctx.add(try ctx.add(r.wires[i], borrow), diff));
        borrow = next;
        borrow_value = next_value;
    }
    try assertEqualArithmetic(V, ctx, borrow, ctx.zero());

    return .{ .quotient = quotient, .remainder = remainder };
}

pub fn divRemArithmetic(comptime V: type, ctx: *Context(V), numerator: []const Var, denominator: []const Var, width: u32) !Division {
    if (width != 16 and width != 32 and width != 64 and width != 128) return error.InvalidIntegerSpec;
    const word_count: usize = @intCast(width / 16);
    if (numerator.len != word_count or denominator.len != word_count) return error.InvalidIntegerOperand;
    const n = value128(V, ctx, numerator);
    const d = value128(V, ctx, denominator);
    if (comptime V == QM31) if (d == 0) return error.ZeroDivisor;
    return divRemArithmeticWithWitness(V, ctx, numerator, denominator, width, .{
        .quotient = if (d == 0) 0 else n / d,
        .remainder = if (d == 0) 0 else n % d,
    });
}

pub fn divRem(comptime V: type, ctx: *Context(V), numerator: []const Var, denominator: []const Var, width: u32, numerator_byte_bounded: bool, denominator_byte_bounded: bool) !Division {
    if (width != 8 and width != 16 and width != 32 and width != 64 and width != 128)
        return error.InvalidIntegerSpec;
    const limb_count: usize = if (width == 8) 1 else @intCast(width / 16);
    if (numerator.len != limb_count or denominator.len != limb_count)
        return error.InvalidIntegerOperand;
    const n = value128(V, ctx, numerator);
    const d = value128(V, ctx, denominator);
    if (comptime V == QM31) if (width == 8 and (n >= 256 or d >= 256)) return error.IntegerOutOfRange;
    if (comptime V == QM31) if (d == 0) return error.ZeroDivisor;
    return divRemWithWitness(V, ctx, numerator, denominator, width, numerator_byte_bounded, denominator_byte_bounded, .{
        .quotient = if (d == 0) 0 else n / d,
        .remainder = if (d == 0) 0 else n % d,
    });
}

/// The witness entry point lets tests submit a wrong quotient or remainder.
/// The constraints below, rather than this witness, determine validity.
pub fn divRemWithWitness(comptime V: type, ctx: *Context(V), numerator: []const Var, denominator: []const Var, width: u32, numerator_byte_bounded: bool, denominator_byte_bounded: bool, witness: Witness) !Division {
    if (width != 8 and width != 16 and width != 32 and width != 64 and width != 128)
        return error.InvalidIntegerSpec;
    const limb_count: usize = if (width == 8) 1 else @intCast(width / 16);
    if (numerator.len != limb_count or denominator.len != limb_count)
        return error.InvalidIntegerOperand;
    if (width == 8) return divRemByteWithWitness(V, ctx, numerator, denominator, numerator_byte_bounded, denominator_byte_bounded, witness);
    if (width == 16) return divRemArithmeticWithWitness(V, ctx, numerator, denominator, width, witness);
    const count: usize = @intCast(width / 8);
    const n = try splitWords(V, ctx, numerator, width, numerator_byte_bounded);
    const d = try splitWords(V, ctx, denominator, width, denominator_byte_bounded);
    const q_words = try witnessWords(V, ctx, witness.quotient, width);
    const r_words = try witnessWords(V, ctx, witness.remainder, width);
    const q = try splitWords(V, ctx, q_words, width, false);
    const r = try splitWords(V, ctx, r_words, width, false);
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));

    // q*d+r=n over all 2W bits, with zero high result and terminal carry.
    // Each left side is at most 16*255^2+65535+255 < p; each right side is
    // at most 255+256*65535 < p. The field equality is an integer equality.
    var incoming = ctx.zero();
    var carry_value: u64 = 0;
    for (0..2 * count) |column| {
        var sum = incoming;
        var integer_sum: u64 = carry_value;
        const first = if (column < count) 0 else column - (count - 1);
        const end = @min(column + 1, count);
        for (first..end) |i| {
            const j = column - i;
            sum = try ctx.add(sum, try ctx.mul(q.wires[i], d.wires[j]));
            integer_sum += @as(u64, q.values[i]) * d.values[j];
        }
        if (column < count) {
            sum = try ctx.add(sum, r.wires[column]);
            integer_sum += r.values[column];
        }
        const digit = if (column < count) n.wires[column] else ctx.zero();
        const outgoing_value: u32 = @intCast(integer_sum / 256);
        const outgoing = try ctx.guessU16(hint(V, outgoing_value));
        try ctx.eq(sum, try ctx.add(digit, try ctx.mul(outgoing, base)));
        incoming = outgoing;
        carry_value = outgoing_value;
    }
    try ctx.eq(incoming, ctx.zero());

    // d-r-1 >= 0. Boolean borrow and bounded digits make this an exact
    // strict comparison. In particular, no witness exists when d=0.
    const limb_base_value: u32 = if (width == 8) 256 else 65536;
    const limb_base = try ctx.constant(QM31.fromBase(M31.fromCanonical(limb_base_value)));
    var borrow = ctx.one();
    var borrow_value: u32 = 1;
    for (denominator, r_words) |dw, rw| {
        const dv = valueOf(V, ctx, dw);
        const rv = valueOf(V, ctx, rw);
        const next_value: u32 = @intFromBool(dv < rv + borrow_value);
        const diff_value = (dv + limb_base_value - rv - borrow_value) & (limb_base_value - 1);
        const next = try ctx.guess(hint(V, next_value));
        try ctx.eq(try ctx.mul(next, next), next);
        const diff = try ctx.guessU16(hint(V, diff_value));
        if (width == 8) try constrainByte(V, ctx, diff);
        try ctx.eq(try ctx.add(dw, try ctx.mul(next, limb_base)), try ctx.add(try ctx.add(rw, borrow), diff));
        borrow = next;
        borrow_value = next_value;
    }
    try ctx.eq(borrow, ctx.zero());
    return .{ .quotient = q_words, .remainder = r_words };
}

fn testWords(ctx: *Context(QM31), value: u128, width: u32) ![]Var {
    return witnessWords(QM31, ctx, value, width);
}

test "unsigned division constrains all widths and rejects false witnesses" {
    const cases = [_]struct { width: u32, n: u128, d: u128 }{
        .{ .width = 8, .n = 201, .d = 14 },
        .{ .width = 16, .n = 65535, .d = 1 },
        .{ .width = 32, .n = 123456, .d = 300 },
        .{ .width = 64, .n = 0x123456789abcdef0, .d = 0x10001 },
        .{ .width = 128, .n = std.math.maxInt(u128), .d = 0x10000000000000001 },
    };
    for (cases) |case| {
        var ctx = try Context(QM31).init(std.testing.allocator, 1);
        defer ctx.deinit();
        const n = try testWords(&ctx, case.n, case.width);
        const d = try testWords(&ctx, case.d, case.width);
        const result = try divRem(QM31, &ctx, n, d, case.width, false, false);
        try std.testing.expectEqual(case.n / case.d, value128(QM31, &ctx, result.quotient));
        try std.testing.expectEqual(case.n % case.d, value128(QM31, &ctx, result.remainder));
        try ctx.setOutputs(&.{result.quotient[0]});
        try ctx.finalize(false);
        try std.testing.expect(try ctx.isCircuitValid());
    }
    const bad = [_]Witness{
        .{ .quotient = 4, .remainder = 0 }, // 17/5 is 3 remainder 2.
        .{ .quotient = 2, .remainder = 7 }, // Equality holds, but r >= d.
        .{ .quotient = 3, .remainder = 258 }, // A byte cannot hide a high bit.
    };
    for (bad) |witness| {
        var ctx = try Context(QM31).init(std.testing.allocator, 1);
        defer ctx.deinit();
        const n = try testWords(&ctx, 17, 8);
        const d = try testWords(&ctx, 5, 8);
        const result = try divRemWithWitness(QM31, &ctx, n, d, 8, false, false, witness);
        try ctx.setOutputs(&.{result.quotient[0]});
        try ctx.finalize(false);
        try std.testing.expect(!(try ctx.isCircuitValid()));
    }
    {
        var ctx = try Context(QM31).init(std.testing.allocator, 1);
        defer ctx.deinit();
        const max = std.math.maxInt(u128);
        const n = try testWords(&ctx, max, 128);
        const d = try testWords(&ctx, max, 128);
        const result = try divRemWithWitness(QM31, &ctx, n, d, 128, false, false, .{ .quotient = 2, .remainder = 1 });
        try ctx.setOutputs(&.{result.quotient[0]});
        try ctx.finalize(false);
        try std.testing.expect(!(try ctx.isCircuitValid()));
    }
    {
        var ctx = try Context(QM31).init(std.testing.allocator, 1);
        defer ctx.deinit();
        const n = try testWords(&ctx, 0, 8);
        const d = try testWords(&ctx, 0, 8);
        try std.testing.expectError(error.ZeroDivisor, divRem(QM31, &ctx, n, d, 8, false, false));
        const result = try divRemWithWitness(QM31, &ctx, n, d, 8, false, false, .{ .quotient = 0, .remainder = 0 });
        try ctx.setOutputs(&.{result.quotient[0]});
        try ctx.finalize(false);
        try std.testing.expect(!(try ctx.isCircuitValid()));
    }
}

test "proved byte division needs no u16 lookup rows" {
    var ctx = try Context(QM31).init(std.testing.allocator, 2);
    defer ctx.deinit();
    const numerator = try ctx.guess(hint(QM31, 201));
    const denominator = try ctx.guess(hint(QM31, 14));
    _ = try integer_bits.decomposeByteArithmetic(QM31, &ctx, numerator);
    _ = try integer_bits.decomposeByteArithmetic(QM31, &ctx, denominator);
    const division = try divRemWithWitness(QM31, &ctx, &.{numerator}, &.{denominator}, 8, true, true, .{ .quotient = 14, .remainder = 5 });
    try ctx.setOutputs(&.{ division.quotient[0], division.remainder[0] });
    try ctx.finalize(false);
    try std.testing.expect(try ctx.isCircuitValid());
    try std.testing.expectEqual(@as(usize, 0), ctx.circuit.m31_to_u32.items.len);
    try std.testing.expectEqual(@as(usize, 0), ctx.circuit.eq.items.len);
}

test "byte division rejects an unbounded input even when equations agree" {
    var ctx = try Context(QM31).init(std.testing.allocator, 2);
    defer ctx.deinit();
    const numerator = try ctx.guess(hint(QM31, 256));
    const denominator = try ctx.guess(hint(QM31, 14));
    // 256 = 18*14+4 and 4<14; only the byte bound rules this out.
    const division = try divRemWithWitness(QM31, &ctx, &.{numerator}, &.{denominator}, 8, false, false, .{ .quotient = 18, .remainder = 4 });
    try ctx.setOutputs(&.{ division.quotient[0], division.remainder[0] });
    try ctx.finalize(false);
    try std.testing.expect(!(try ctx.isCircuitValid()));
}

test "arithmetic-only 16-bit division proves carries and strict remainder" {
    const cases = [_]struct { numerator: u32, denominator: u32, quotient: u128, remainder: u128, valid: bool }{
        .{ .numerator = 60000, .denominator = 257, .quotient = 233, .remainder = 119, .valid = true },
        // Equality alone holds, but 376 is not a canonical remainder.
        .{ .numerator = 60000, .denominator = 257, .quotient = 232, .remainder = 376, .valid = false },
        // 65536 = 255*257+1; only the proved 16-bit bound rules it out.
        .{ .numerator = 65536, .denominator = 257, .quotient = 255, .remainder = 1, .valid = false },
        .{ .numerator = 60000, .denominator = 0, .quotient = 0, .remainder = 60000, .valid = false },
    };
    for (cases) |case| {
        var ctx = try Context(QM31).init(std.testing.allocator, 2);
        defer ctx.deinit();
        const numerator = try ctx.guess(hint(QM31, case.numerator));
        const denominator = try ctx.guess(hint(QM31, case.denominator));
        const result = try divRemWithWitness(QM31, &ctx, &.{numerator}, &.{denominator}, 16, false, false,
            .{ .quotient = case.quotient, .remainder = case.remainder });
        try ctx.setOutputs(&.{ result.quotient[0], result.remainder[0] });
        try ctx.finalize(false);
        try std.testing.expectEqual(case.valid, try ctx.isCircuitValid());
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.m31_to_u32.items.len);
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.eq.items.len);
    }
}

test "arithmetic-only 32-bit division proves high product and word bounds" {
    const cases = [_]struct { n: [2]u32, d: [2]u32, q: u128, r: u128, valid: bool }{
        .{ .n = .{ 57920, 1 }, .d = .{ 300, 0 }, .q = 411, .r = 156, .valid = true },
        .{ .n = .{ 57920, 1 }, .d = .{ 300, 0 }, .q = 410, .r = 456, .valid = false },
        // 65536 = 218*300+136, but a raw u16 limb may not equal 65536.
        .{ .n = .{ 65536, 0 }, .d = .{ 300, 0 }, .q = 218, .r = 136, .valid = false },
        // The low 32 product bits vanish, but the high columns expose 2^32.
        .{ .n = .{ 0, 0 }, .d = .{ 0, 1 }, .q = 65536, .r = 0, .valid = false },
    };
    for (cases) |case| {
        var ctx = try Context(QM31).init(std.testing.allocator, 2);
        defer ctx.deinit();
        var n: [2]Var = undefined;
        var d: [2]Var = undefined;
        for (&n, case.n) |*word, value| word.* = try ctx.guess(hint(QM31, value));
        for (&d, case.d) |*word, value| word.* = try ctx.guess(hint(QM31, value));
        const result = try divRemArithmeticWithWitness(QM31, &ctx, &n, &d, 32,
            .{ .quotient = case.q, .remainder = case.r });
        try ctx.setOutputs(&.{ result.quotient[0], result.remainder[0] });
        try ctx.finalize(false);
        const valid = try ctx.isCircuitValid();
        if (case.valid != valid) std.debug.print("direct32 mismatch n={any} d={any} q={d} r={d} expected={} actual={}\n", .{ case.n, case.d, case.q, case.r, case.valid, valid });
        try std.testing.expectEqual(case.valid, valid);
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.m31_to_u32.items.len);
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.eq.items.len);
    }
}
