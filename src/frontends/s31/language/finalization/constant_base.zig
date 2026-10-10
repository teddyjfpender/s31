//! Deterministic constant derivation for small fixed-width relations.
//!
//! The engine's default minimum radix is 256 and yields a 255-row plus-one
//! chain even when a program uses only a few constants. A radix of 16 is
//! cheaper for small integer gadgets. The engine implementation of constant
//! derivation remains authoritative; this module only selects its parameter.

const circuit = @import("stwo_circuit_frontend");
const relation = @import("../relation.zig");

pub const compact_base: u32 = 16;
pub const max_compact_nodes: usize = 64;

pub fn selectedBase(program: relation.Program) ?u32 {
    if (program.nodes.len > max_compact_nodes) return null;
    var integer_operation = false;
    for (program.nodes) |node| switch (node.op) {
        .int_view, .int_add_checked, .int_add_wrapping, .int_sub_checked, .int_sub_wrapping, .int_le, .int_mul_wrapping, .int_mul_checked, .int_cast_checked, .int_bit_and, .int_bit_or, .int_bit_xor, .int_bit_not => integer_operation = true,
        .hash_blake2s, .hash_blake2s_leaf, .hash_blake2s_pair, .hash_poseidon2_leaf, .hash_poseidon2_pair, .hash_sha256d_header, .bitcoin_target_mainnet, .bitcoin_block_work, .bitcoin_prev_hash, .bitcoin_header_bits, .bitcoin_header_time, .bitcoin_genesis_hash_mainnet => return null,
        else => {},
    };
    return if (integer_operation) compact_base else null;
}

pub fn finish(comptime V: type, ctx: *circuit.builder.Context(V), program: relation.Program) !void {
    const base = selectedBase(program) orelse return ctx.finalize(false);
    if (ctx.reserved_vars.items.len != 0) return error.UnassignedReservedVars;
    try circuit.builder.finalize_constants.finalizeConstantsWithMinBase(V, ctx, base);
    try ctx.finalizeGuessedVars();
    ctx.finalized = true;
}
