//! Fixed-width multiplication for sparse-wide and direct circuit AIRs.
//!
//! The existing sparse-wide path takes constrained u16 limbs, splits them
//! into constrained bytes, and uses a base-256 convolution. Its full product
//! includes a final zero column and constrains the terminal carry to zero.
//! The arithmetic-only direct path instead consumes Boolean operand bits
//! already proved and bound to the input limbs by its caller. It uses 8-bit
//! digits through W=32, 13-bit digits for W=64/128, Boolean result/carry
//! bits, and arithmetic zero self-loops for every radix equation. Its full
//! product treats the last carry as the final high digit and explicitly
//! constrains all padding bits to zero. In both paths, every column equation
//! is between bounded nonnegative integers strictly below the M31 modulus,
//! so field equality cannot hide a false product through modular wrap.

const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const std = @import("std");
const integer_bits = @import("integer_bits.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Var = circuit.builder.Var;
const Context = circuit.builder.Context;

const Bytes = struct {
    wires: []Var,
    values: []u32,
};

pub const FullProduct = struct {
    low: []Var,
    high: []Var,
};

/// Arithmetic-only direct-gate product. `low_bits` are the proved little-endian
/// bits of `low`, ready for the caller's bit cache. The operand bit slices must
/// already be Boolean and bound to the supplied operand limbs.
pub const ArithmeticProduct = struct {
    low: []Var,
    high: []Var,
    low_bits: []Var,
};

fn hint(comptime V: type, value: u32) V {
    return circuit.builder.ivalue.fromQm31(V, QM31.fromBase(M31.fromCanonical(value)));
}

fn valueOf(comptime V: type, ctx: *Context(V), wire: Var) u32 {
    return if (comptime V == QM31) ctx.get(wire).toM31Array()[0].v else 0;
}

fn constrainByte(comptime V: type, ctx: *Context(V), word: Var) !void {
    // The guessed u16 is the low 16 bits of 256*word. Field equality then
    // rejects any word >= 256 because the unreduced product is < 2^24 < p.
    const value = valueOf(V, ctx, word);
    const scaled = try ctx.guessU16(hint(V, (value * 256) & 0xffff));
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    try ctx.eq(try ctx.mul(word, base), scaled);
}

fn boundedByte(comptime V: type, ctx: *Context(V), value: u32) !Var {
    const result = try ctx.guessU16(hint(V, value));
    try constrainByte(V, ctx, result);
    return result;
}

fn inputBytes(comptime V: type, ctx: *Context(V), words: []const Var, byte_bounded: bool, count: usize) !Bytes {
    const wires = try ctx.scratch().alloc(Var, count);
    const values = try ctx.scratch().alloc(u32, count);
    if (count == 1) {
        wires[0] = words[0];
        values[0] = valueOf(V, ctx, words[0]);
        if (!byte_bounded) try constrainByte(V, ctx, words[0]);
        return .{ .wires = wires, .values = values };
    }
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    for (words, 0..) |word, index| {
        const value = valueOf(V, ctx, word);
        const low = value & 0xff;
        const high = (value >> 8) & 0xff;
        wires[2 * index] = try boundedByte(V, ctx, low);
        // The u16 limb and low-byte bounds make high < 256 through the
        // reconstruction equation; an extra byte lookup would be redundant.
        wires[2 * index + 1] = try ctx.guessU16(hint(V, high));
        values[2 * index] = low;
        values[2 * index + 1] = high;
        try ctx.eq(word, try ctx.add(wires[2 * index], try ctx.mul(wires[2 * index + 1], base)));
    }
    return .{ .wires = wires, .values = values };
}

fn product(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_byte_bounded: bool, right_byte_bounded: bool, full: bool) !FullProduct {
    if (width != 8 and width != 16 and width != 32 and width != 64 and width != 128)
        return error.InvalidIntegerSpec;
    const count: usize = @intCast(width / 8);
    const limb_count: usize = if (width == 8) 1 else count / 2;
    if (left.len != limb_count or right.len != limb_count)
        return error.InvalidIntegerOperand;

    const a = try inputBytes(V, ctx, left, left_byte_bounded, count);
    const b = try inputBytes(V, ctx, right, right_byte_bounded, count);
    const column_count = if (full) 2 * count else count;
    const output_bytes = try ctx.scratch().alloc(Var, column_count);
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(256)));
    var incoming = ctx.zero();
    var carry_value: u32 = 0;
    for (0..column_count) |column| {
        var sum_wire = incoming;
        var sum_value = carry_value;
        for (0..@min(count, column + 1)) |i| {
            const j = column - i;
            if (j >= count) continue;
            sum_wire = try ctx.add(sum_wire, try ctx.mul(a.wires[i], b.wires[j]));
            sum_value += a.values[i] * b.values[j];
        }
        const digit_value = sum_value & 0xff;
        const outgoing_value = sum_value >> 8;
        output_bytes[column] = try boundedByte(V, ctx, digit_value);
        const outgoing = try ctx.guessU16(hint(V, outgoing_value));
        try ctx.eq(sum_wire, try ctx.add(output_bytes[column], try ctx.mul(outgoing, base)));
        incoming = outgoing;
        carry_value = outgoing_value;
    }
    if (full) try ctx.eq(incoming, ctx.zero());

    const low = try ctx.scratch().alloc(Var, limb_count);
    const high = try ctx.scratch().alloc(Var, if (full) limb_count else 0);
    if (width == 8) {
        low[0] = output_bytes[0];
        if (full) high[0] = output_bytes[1];
    } else for (low, 0..) |*word, i| {
        word.* = try ctx.add(output_bytes[2 * i], try ctx.mul(output_bytes[2 * i + 1], base));
        if (full) high[i] = try ctx.add(output_bytes[count + 2 * i], try ctx.mul(output_bytes[count + 2 * i + 1], base));
    }
    return .{ .low = low, .high = high };
}

/// Return little-endian u16 limbs of `(left * right) mod 2^width`. Signed and
/// unsigned fixed-width operands use the same bit-pattern operation.
pub fn wrapping(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_byte_bounded: bool, right_byte_bounded: bool) ![]Var {
    return (try product(V, ctx, left, right, width, left_byte_bounded, right_byte_bounded, false)).low;
}

/// Return the complete 2W-bit unsigned product. The terminal carry is fixed
/// to zero; callers must apply their signed or unsigned overflow predicate.
pub fn fullProduct(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_byte_bounded: bool, right_byte_bounded: bool) !FullProduct {
    return product(V, ctx, left, right, width, left_byte_bounded, right_byte_bounded, true);
}

fn digitWidth(width: u32) ?usize {
    return switch (width) {
        8, 16, 32 => 8,
        64, 128 => 13,
        else => null,
    };
}

fn carryBitCount(width: u32) usize {
    // These are the bit lengths of the all-maximum input recurrence. The
    // partial top digit is included for the 13-bit radix cases.
    return switch (width) {
        8 => 8,
        16 => 9,
        32 => 10,
        64 => 15,
        128 => 17,
        else => unreachable,
    };
}

fn packBits(comptime V: type, ctx: *Context(V), bits: []const Var) !Var {
    var word = ctx.zero();
    for (0..bits.len) |offset| {
        word = try ctx.add(try ctx.add(word, word), bits[bits.len - 1 - offset]);
    }
    return word;
}

/// Each bit's self-product is its sole producing gate and proves membership
/// in {0,1} in QM31. Packing preserves the embedded M31 value.
fn booleanBits(comptime V: type, ctx: *Context(V), value: u32, count: usize) ![]Var {
    const bits = try ctx.scratch().alloc(Var, count);
    for (bits, 0..) |*bit, index| {
        const bit_value = (value >> @as(u5, @intCast(index))) & 1;
        bit.* = try ctx.newVar(hint(V, bit_value));
        try ctx.mulInto(bit.*, bit.*, bit.*);
    }
    return bits;
}

fn assertZeroArithmetic(comptime V: type, ctx: *Context(V), value: Var) !void {
    const anchor = try ctx.newVar(circuit.builder.ivalue.fromQm31(V, QM31.zero()));
    try ctx.addInto(anchor, value, anchor);
}

const ArithmeticMode = enum { wrapping, full, checked_unsigned };

fn arithmeticProduct(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_bits: []const Var, right_bits: []const Var, mode: ArithmeticMode) !ArithmeticProduct {
    const digit_width = digitWidth(width) orelse return error.InvalidIntegerSpec;
    const width_usize: usize = @intCast(width);
    const limb_count: usize = if (width == 8) 1 else width_usize / 16;
    if (left.len != limb_count or right.len != limb_count or
        left_bits.len != width_usize or right_bits.len != width_usize)
        return error.InvalidIntegerOperand;

    const digit_count = (width_usize + digit_width - 1) / digit_width;
    const base_value: u32 = @as(u32, 1) << @as(u5, @intCast(digit_width));
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(base_value)));
    const a = try ctx.scratch().alloc(Var, digit_count);
    const b = try ctx.scratch().alloc(Var, digit_count);
    const av = try ctx.scratch().alloc(u32, digit_count);
    const bv = try ctx.scratch().alloc(u32, digit_count);
    for (0..digit_count) |i| {
        const start = i * digit_width;
        const end = @min(start + digit_width, width_usize);
        // The last source digit is packed from only its real W-bit suffix;
        // no unconstrained zero-extension bits enter the convolution.
        a[i] = try packBits(V, ctx, left_bits[start..end]);
        b[i] = try packBits(V, ctx, right_bits[start..end]);
        av[i] = valueOf(V, ctx, a[i]);
        bv[i] = valueOf(V, ctx, b[i]);
    }

    const full = mode == .full;
    const output_digit_count = if (full) 2 * digit_count else digit_count;
    const output_bits = try ctx.scratch().alloc(Var, output_digit_count * digit_width);
    const constrained_columns = if (full) output_digit_count - 1 else output_digit_count;
    var incoming = ctx.zero();
    var carry_value: u32 = 0;
    var final_carry_bits: ?[]Var = null;
    for (0..constrained_columns) |column| {
        var sum = incoming;
        var sum_value: u64 = carry_value;
        for (0..@min(digit_count, column + 1)) |i| {
            const j = column - i;
            if (j >= digit_count) continue;
            sum = try ctx.add(sum, try ctx.mul(a[i], b[j]));
            sum_value += @as(u64, av[i]) * bv[j];
        }
        const digit_value: u32 = @intCast(sum_value & (base_value - 1));
        const outgoing_value: u32 = @intCast(sum_value >> @as(u6, @intCast(digit_width)));
        const digit_bits = try booleanBits(V, ctx, digit_value, digit_width);
        const outgoing_bits = try booleanBits(V, ctx, outgoing_value, carryBitCount(width));
        const digit = try packBits(V, ctx, digit_bits);
        const outgoing = try packBits(V, ctx, outgoing_bits);
        const rhs = try ctx.add(digit, try ctx.mul(outgoing, base));
        try assertZeroArithmetic(V, ctx, try ctx.sub(sum, rhs));
        @memcpy(output_bits[column * digit_width ..][0..digit_width], digit_bits);
        incoming = outgoing;
        carry_value = outgoing_value;
        final_carry_bits = outgoing_bits;
    }

    if (full) {
        const last = final_carry_bits.?;
        // No source terms occur after column 2N-2. The final carry is the
        // last product digit; higher carry bits and product padding are zero.
        for (last[digit_width..]) |bit| try assertZeroArithmetic(V, ctx, bit);
        @memcpy(output_bits[(output_digit_count - 1) * digit_width ..][0..digit_width], last[0..digit_width]);
        for (output_bits[2 * width_usize ..]) |bit| try assertZeroArithmetic(V, ctx, bit);
    } else if (mode == .checked_unsigned) {
        // The low columns telescope to product_low + C_N*B^N. A checked
        // product has no carry beyond them and no bits past W in their last
        // digit. This catches overflow inside a partial d13 top digit.
        try assertZeroArithmetic(V, ctx, incoming);
        for (output_bits[width_usize..]) |bit| try assertZeroArithmetic(V, ctx, bit);

        // Every omitted high coefficient is a sum of nonnegative bounded
        // digit products. Its maximum is 10*8191^2 < p, so zero in M31
        // forces zero over the integers without high digit/carry witnesses.
        for (digit_count..2 * digit_count - 1) |column| {
            var high_sum = ctx.zero();
            for (0..digit_count) |i| {
                const j = column - i;
                if (j >= digit_count) continue;
                high_sum = try ctx.add(high_sum, try ctx.mul(a[i], b[j]));
            }
            try assertZeroArithmetic(V, ctx, high_sum);
        }
    }

    const low_bits = output_bits[0..width_usize];
    const low = try ctx.scratch().alloc(Var, limb_count);
    const high = try ctx.scratch().alloc(Var, if (full) limb_count else 0);
    const limb_width: usize = if (width == 8) 8 else 16;
    for (low, 0..) |*word, i| {
        word.* = try packBits(V, ctx, low_bits[i * limb_width ..][0..limb_width]);
        if (full) high[i] = try packBits(V, ctx, output_bits[width_usize + i * limb_width ..][0..limb_width]);
    }
    return .{ .low = low, .high = high, .low_bits = low_bits };
}

/// Arithmetic-only wrapping multiplication. The caller supplies concatenated
/// little-endian operand bits already constrained to {0,1} and to `left` and
/// `right`. Extra bits in the last output digit are intentionally discarded.
pub fn wrappingArithmetic(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_bits: []const Var, right_bits: []const Var) !ArithmeticProduct {
    return arithmeticProduct(V, ctx, left, right, width, left_bits, right_bits, .wrapping);
}

/// Arithmetic-only complete 2W-bit product for unsigned and signed checked
/// overflow constraints in the caller. All product padding bits are zero.
pub fn fullProductArithmetic(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_bits: []const Var, right_bits: []const Var) !ArithmeticProduct {
    return arithmeticProduct(V, ctx, left, right, width, left_bits, right_bits, .full);
}

/// Checked unsigned multiplication without high product digit witnesses.
/// The low carry, partial top-digit spill, and every high source convolution
/// coefficient must vanish. The returned `high` slice is empty.
pub fn checkedUnsignedArithmetic(comptime V: type, ctx: *Context(V), left: []const Var, right: []const Var, width: u32, left_bits: []const Var, right_bits: []const Var) !ArithmeticProduct {
    return arithmeticProduct(V, ctx, left, right, width, left_bits, right_bits, .checked_unsigned);
}

fn expectCorruptedWireRejected(ctx: *Context(QM31), wire: Var) !void {
    const original = ctx.value_table.items[wire.idx];
    ctx.value_table.items[wire.idx] = original.add(QM31.one());
    defer ctx.value_table.items[wire.idx] = original;
    try std.testing.expect(!try ctx.isCircuitValid());
}

test "direct multiplier rejects source digit carry and result witness mutations" {
    const allocator = std.testing.allocator;
    var ctx = try Context(QM31).init(allocator, 1);
    defer ctx.deinit();
    const left = try ctx.guess(hint(QM31, 255));
    const right = try ctx.guess(hint(QM31, 258));
    const left_bits = try integer_bits.decomposeWordArithmetic(QM31, &ctx, left, 16);
    const right_bits = try integer_bits.decomposeWordArithmetic(QM31, &ctx, right, 16);
    const before_mul = ctx.circuit.mul.items.len;
    const result = try wrappingArithmetic(QM31, &ctx, &.{left}, &.{right}, 16, left_bits, right_bits);
    try ctx.setOutputs(result.low);
    try ctx.finalize(false);
    try std.testing.expectEqual(@as(u32, 254), valueOf(QM31, &ctx, result.low[0]));
    try std.testing.expect(try ctx.isCircuitValid());
    try std.testing.expectEqual(@as(usize, 0), ctx.circuit.eq.items.len);
    try std.testing.expectEqual(@as(usize, 0), ctx.circuit.m31_to_u32.items.len);
    try std.testing.expectEqual(null, try ctx.circuit.firstYieldViolation(allocator));

    // The first eight new self-product gates create column zero's output
    // digit. The ninth is its first carry bit. Changing either bit breaks
    // its producing gate or one of the exact radix equations.
    var self_products: [9]Var = undefined;
    var found: usize = 0;
    for (ctx.circuit.mul.items[before_mul..]) |gate| {
        if (gate.in0 == gate.in1 and gate.in1 == gate.out) {
            if (found < self_products.len) self_products[found] = .{ .idx = gate.out };
            found += 1;
        }
    }
    try std.testing.expect(found >= self_products.len);
    try expectCorruptedWireRejected(&ctx, left_bits[0]);
    try expectCorruptedWireRejected(&ctx, self_products[0]);
    try expectCorruptedWireRejected(&ctx, self_products[8]);
    try expectCorruptedWireRejected(&ctx, result.low[0]);
    try std.testing.expect(try ctx.isCircuitValid());
}

test "direct 13-bit digits split exact full product at the 64-bit boundary" {
    const allocator = std.testing.allocator;
    var ctx = try Context(QM31).init(allocator, 8);
    defer ctx.deinit();
    const left = try ctx.scratch().alloc(Var, 4);
    const right = try ctx.scratch().alloc(Var, 4);
    const left_bits = try ctx.scratch().alloc(Var, 64);
    const right_bits = try ctx.scratch().alloc(Var, 64);
    for (0..4) |i| {
        left[i] = try ctx.guess(hint(QM31, 65535));
        right[i] = try ctx.guess(hint(QM31, if (i == 0) 2 else 0));
        const a_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, left[i], 16);
        const b_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, right[i], 16);
        @memcpy(left_bits[16 * i ..][0..16], a_part);
        @memcpy(right_bits[16 * i ..][0..16], b_part);
    }
    const result = try fullProductArithmetic(QM31, &ctx, left, right, 64, left_bits, right_bits);
    const outputs = try ctx.scratch().alloc(Var, 8);
    @memcpy(outputs[0..4], result.low);
    @memcpy(outputs[4..8], result.high);
    try ctx.setOutputs(outputs);
    try ctx.finalize(false);
    try std.testing.expect(try ctx.isCircuitValid());
    try std.testing.expectEqual(null, try ctx.circuit.firstYieldViolation(allocator));
    for (result.low, 0..) |word, i|
        try std.testing.expectEqual(@as(u32, if (i == 0) 65534 else 65535), valueOf(QM31, &ctx, word));
    for (result.high, 0..) |word, i|
        try std.testing.expectEqual(@as(u32, if (i == 0) 1 else 0), valueOf(QM31, &ctx, word));
    try expectCorruptedWireRejected(&ctx, result.low_bits[63]);
    try expectCorruptedWireRejected(&ctx, result.high[0]);
    try std.testing.expect(try ctx.isCircuitValid());
}

test "unsigned checked shortcut rejects carry spill and high convolution overflow" {
    const allocator = std.testing.allocator;
    inline for (.{
        .{ .width = 8, .left = 25, .right = 10, .valid = true },
        .{ .width = 8, .left = 25, .right = 11, .valid = false },
        .{ .width = 16, .left = 255, .right = 257, .valid = true },
        .{ .width = 16, .left = 255, .right = 258, .valid = false }, // low carry only
        .{ .width = 16, .left = 256, .right = 256, .valid = false }, // high coefficient only
        .{ .width = 64, .left = @as(u128, std.math.maxInt(u64)), .right = 1, .valid = true },
        .{ .width = 64, .left = @as(u128, 1) << 63, .right = 2, .valid = false }, // partial-digit spill only
    }) |case| {
        const limb_count: usize = if (case.width == 8) 1 else case.width / 16;
        const per_limb: usize = if (case.width == 8) 8 else 16;
        var ctx = try Context(QM31).init(allocator, limb_count);
        defer ctx.deinit();
        const left = try ctx.scratch().alloc(Var, limb_count);
        const right = try ctx.scratch().alloc(Var, limb_count);
        const left_bits = try ctx.scratch().alloc(Var, case.width);
        const right_bits = try ctx.scratch().alloc(Var, case.width);
        for (0..limb_count) |i| {
            const shift: u7 = @intCast(16 * i);
            left[i] = try ctx.guess(hint(QM31, @intCast((@as(u128, case.left) >> shift) & 0xffff)));
            right[i] = try ctx.guess(hint(QM31, @intCast((@as(u128, case.right) >> shift) & 0xffff)));
            const a_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, left[i], per_limb);
            const b_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, right[i], per_limb);
            @memcpy(left_bits[per_limb * i ..][0..per_limb], a_part);
            @memcpy(right_bits[per_limb * i ..][0..per_limb], b_part);
        }
        const result = try checkedUnsignedArithmetic(QM31, &ctx, left, right, case.width, left_bits, right_bits);
        try std.testing.expectEqual(@as(usize, 0), result.high.len);
        try ctx.setOutputs(result.low);
        try ctx.finalize(false);
        try std.testing.expectEqual(case.valid, try ctx.isCircuitValid());
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.eq.items.len);
        try std.testing.expectEqual(@as(usize, 0), ctx.circuit.m31_to_u32.items.len);
        try std.testing.expectEqual(null, try ctx.circuit.firstYieldViolation(allocator));
    }
}

test "unsigned checked wide products distinguish high coefficient and top-digit spill" {
    const allocator = std.testing.allocator;
    inline for (.{
        .{ .width = 64, .left = @as(u128, 1) << 52, .right = @as(u128, 1) << 13, .valid = false },
        .{ .width = 128, .left = @as(u128, 1) << 117, .right = @as(u128, 1) << 13, .valid = false },
        .{ .width = 128, .left = @as(u128, 1) << 127, .right = @as(u128, 2), .valid = false },
        .{ .width = 128, .left = std.math.maxInt(u128), .right = @as(u128, 1), .valid = true },
    }) |case| {
        const limb_count: usize = case.width / 16;
        var ctx = try Context(QM31).init(allocator, limb_count);
        defer ctx.deinit();
        const left = try ctx.scratch().alloc(Var, limb_count);
        const right = try ctx.scratch().alloc(Var, limb_count);
        const left_bits = try ctx.scratch().alloc(Var, case.width);
        const right_bits = try ctx.scratch().alloc(Var, case.width);
        for (0..limb_count) |i| {
            const shift: u7 = @intCast(16 * i);
            left[i] = try ctx.guess(hint(QM31, @intCast((@as(u128, case.left) >> shift) & 0xffff)));
            right[i] = try ctx.guess(hint(QM31, @intCast((@as(u128, case.right) >> shift) & 0xffff)));
            const a_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, left[i], 16);
            const b_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, right[i], 16);
            @memcpy(left_bits[16 * i ..][0..16], a_part);
            @memcpy(right_bits[16 * i ..][0..16], b_part);
        }
        const result = try checkedUnsignedArithmetic(QM31, &ctx, left, right, case.width, left_bits, right_bits);
        try ctx.setOutputs(result.low);
        try ctx.finalize(false);
        try std.testing.expectEqual(case.valid, try ctx.isCircuitValid());
        try std.testing.expectEqual(null, try ctx.circuit.firstYieldViolation(allocator));
        if (case.valid) for (result.low, 0..) |word, i| {
            const shift: u7 = @intCast(16 * i);
            try std.testing.expectEqual(@as(u32, @intCast((@as(u128, case.left) >> shift) & 0xffff)), valueOf(QM31, &ctx, word));
        };
    }
}

test "direct full product accepts maximum wide carry recurrence" {
    const allocator = std.testing.allocator;
    inline for (.{
        .{ .width = 64, .maximum = @as(u128, std.math.maxInt(u64)) },
        .{ .width = 128, .maximum = std.math.maxInt(u128) },
    }) |case| {
        const limb_count: usize = case.width / 16;
        var ctx = try Context(QM31).init(allocator, 2 * limb_count);
        defer ctx.deinit();
        const left = try ctx.scratch().alloc(Var, limb_count);
        const right = try ctx.scratch().alloc(Var, limb_count);
        const left_bits = try ctx.scratch().alloc(Var, case.width);
        const right_bits = try ctx.scratch().alloc(Var, case.width);
        for (0..limb_count) |i| {
            const shift: u7 = @intCast(16 * i);
            const limb_value: u32 = @intCast((@as(u128, case.maximum) >> shift) & 0xffff);
            left[i] = try ctx.guess(hint(QM31, limb_value));
            right[i] = try ctx.guess(hint(QM31, limb_value));
            const a_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, left[i], 16);
            const b_part = try integer_bits.decomposeWordArithmetic(QM31, &ctx, right[i], 16);
            @memcpy(left_bits[16 * i ..][0..16], a_part);
            @memcpy(right_bits[16 * i ..][0..16], b_part);
        }
        const result = try fullProductArithmetic(QM31, &ctx, left, right, case.width, left_bits, right_bits);
        const outputs = try ctx.scratch().alloc(Var, 2 * limb_count);
        @memcpy(outputs[0..limb_count], result.low);
        @memcpy(outputs[limb_count..], result.high);
        try ctx.setOutputs(outputs);
        try ctx.finalize(false);
        try std.testing.expect(try ctx.isCircuitValid());
        try std.testing.expectEqual(null, try ctx.circuit.firstYieldViolation(allocator));
        const expected: u256 = @as(u256, case.maximum) * @as(u256, case.maximum);
        for (outputs, 0..) |word, i| {
            const shift: u8 = @intCast(16 * i);
            try std.testing.expectEqual(@as(u32, @intCast((expected >> shift) & 0xffff)), valueOf(QM31, &ctx, word));
        }
    }
}
