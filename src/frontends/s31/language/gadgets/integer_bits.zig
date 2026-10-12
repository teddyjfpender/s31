//! Bit-vector arithmetic without the circuit profile's large XOR table.
//!
//! A u16 input is reconstructed from constrained Boolean wires. Bitwise
//! results are algebraic Boolean expressions and are packed back to u16
//! limbs. Reusing the resulting bit wires across adjacent operations avoids
//! a second decomposition for straight-line hash-style code.

const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Var = circuit.builder.Var;

pub const Mode = enum { and_, or_, xor_, not_ };
pub const ShiftMode = enum { shl, shr_logical, shr_arithmetic, rotl, rotr };

/// Static shifts only select already proved Boolean wires or the constant
/// zero. Packing those wires proves the new word without another bit check.
pub fn shiftedBits(comptime V: type, ctx: *circuit.builder.Context(V), bits: []const Var, count: usize, mode: ShiftMode) ![]Var {
    const width = bits.len;
    if (width == 0 or count > width or
        ((mode == .rotl or mode == .rotr) and count >= width)) return error.InvalidIntegerBits;
    const result = try ctx.scratch().alloc(Var, width);
    for (result, 0..) |*out, i| {
        out.* = switch (mode) {
            .shl => if (i < count) ctx.zero() else bits[i - count],
            .shr_logical => if (i + count >= width) ctx.zero() else bits[i + count],
            .shr_arithmetic => if (i + count >= width) bits[width - 1] else bits[i + count],
            .rotl => bits[(i + width - count) % width],
            .rotr => bits[(i + count) % width],
        };
    }
    return result;
}

pub fn decomposeWord(comptime V: type, ctx: *circuit.builder.Context(V), word: Var, per_limb: usize) ![]Var {
    if (per_limb != 8 and per_limb != 16) return error.InvalidIntegerBits;
    const bits = try ctx.scratch().alloc(Var, per_limb);
    const value: u32 = if (comptime V == QM31) ctx.get(word).toM31Array()[0].v else 0;
    for (bits, 0..) |*slot, i| {
        const bit_value: u32 = (value >> @as(u5, @intCast(i))) & 1;
        const bit = try ctx.guess(circuit.builder.ivalue.fromQm31(V, QM31.fromBase(M31.fromCanonical(bit_value))));
        try ctx.eq(try ctx.mul(bit, bit), bit);
        slot.* = bit;
    }
    const reconstructed = try packWord(V, ctx, bits);
    try ctx.eq(reconstructed, word);
    return bits;
}

/// A byte or 16-bit word range proof using only arithmetic gates. Each bit
/// has one producing self-product gate b*b=b; the packed value equals `word`.
/// The reconstruction's self-loop assertion is accepted by the direct AIR.
pub fn decomposeWordArithmetic(comptime V: type, ctx: *circuit.builder.Context(V), word: Var, width: usize) ![]Var {
    if (width != 8 and width != 16) return error.InvalidIntegerBits;
    const bits = try ctx.scratch().alloc(Var, width);
    const value: u32 = if (comptime V == QM31) ctx.get(word).toM31Array()[0].v else 0;
    for (bits, 0..) |*slot, i| {
        const bit_value: u32 = (value >> @as(u5, @intCast(i))) & 1;
        const bit = try ctx.newVar(circuit.builder.ivalue.fromQm31(V, QM31.fromBase(M31.fromCanonical(bit_value))));
        try ctx.mulInto(bit, bit, bit);
        slot.* = bit;
    }
    try assertZeroArithmetic(V, ctx, try ctx.sub(try packWord(V, ctx, bits), word));
    return bits;
}

pub fn decomposeByteArithmetic(comptime V: type, ctx: *circuit.builder.Context(V), word: Var) ![]Var {
    return decomposeWordArithmetic(V, ctx, word, 8);
}

fn assertZeroArithmetic(comptime V: type, ctx: *circuit.builder.Context(V), value: Var) !void {
    const anchor = try ctx.newVar(circuit.builder.ivalue.fromQm31(V, QM31.zero()));
    try ctx.addInto(anchor, value, anchor);
}

pub fn combine(comptime V: type, ctx: *circuit.builder.Context(V), lhs: []const Var, rhs: ?[]const Var, mode: Mode) ![]Var {
    if (rhs) |right| if (right.len != lhs.len) return error.InvalidIntegerBits;
    if (mode != .not_ and rhs == null) return error.InvalidIntegerBits;
    const output = try ctx.scratch().alloc(Var, lhs.len);
    for (lhs, output, 0..) |a, *result, i| {
        result.* = switch (mode) {
            .not_ => try ctx.sub(ctx.one(), a),
            .and_ => try ctx.mul(a, rhs.?[i]),
            .or_ => blk: {
                const b = rhs.?[i];
                break :blk try ctx.sub(try ctx.add(a, b), try ctx.mul(a, b));
            },
            .xor_ => blk: {
                const b = rhs.?[i];
                const both = try ctx.mul(a, b);
                break :blk try ctx.sub(try ctx.add(a, b), try ctx.add(both, both));
            },
        };
    }
    return output;
}

fn packWord(comptime V: type, ctx: *circuit.builder.Context(V), bits: []const Var) !Var {
    var value = ctx.zero();
    for (0..bits.len) |offset| {
        const bit = bits[bits.len - 1 - offset];
        value = try ctx.add(try ctx.add(value, value), bit);
    }
    return value;
}

pub fn pack(comptime V: type, ctx: *circuit.builder.Context(V), bits: []const Var, width: u32) ![]Var {
    const per_limb: usize = if (width == 8) 8 else 16;
    if (bits.len != @as(usize, @intCast(width))) return error.InvalidIntegerBits;
    const words = try ctx.scratch().alloc(Var, bits.len / per_limb);
    for (words, 0..) |*word, limb| {
        word.* = try packWord(V, ctx, bits[limb * per_limb ..][0..per_limb]);
    }
    return words;
}
