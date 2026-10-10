//! Wrapping fixed-width multiplication in the ordinary circuit AIR.
//!
//! Both inputs are constrained u16 limbs. Each limb is split into two
//! constrained bytes, then the low W product bits are computed by base-256
//! convolution. Every column sum is below 16*255^2+4096 < 2^31-1, and the
//! right side is below 256*65535+255 < 2^31-1. Thus a field equality is an
//! integer equality: a witness cannot exploit field wrap to forge a product.
//! Wrapping multiplication discards the high carry; full multiplication
//! constrains the terminal carry to zero.

const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");

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
