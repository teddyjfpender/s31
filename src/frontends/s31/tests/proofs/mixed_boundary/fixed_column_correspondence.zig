//! Source-pinned N1/N8 Qm31 fixed-column audit for the direct mixed circuit.
//!
//! Expected rows follow the source family's scalar ABI, six-gate SIMD packs,
//! two packed public operations, eight lane extracts and eight output copies.
//! This fixture checks emitted preprocessed columns, not PCS authentication.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const binding = @import("../../../runtime/bounded_compiled_binding.zig");
const family = @import("../../../runtime/mixed_boundary/test_source.zig");

const M31 = core.fields.m31.M31;
const DirectCircuit = circuit.common.direct_arithmetic.Circuit;
const Sha256 = std.crypto.hash.sha2.Sha256;

fn pinnedSource(comptime count: usize) []const u8 {
    const original = family.forCount(count);
    const old = "\"name\":\"mixed_descriptor_matrix\"";
    const at = comptime std.mem.indexOf(u8, original, old) orelse @compileError("missing fixture name");
    return original[0..at] ++
        std.fmt.comptimePrint("\"name\":\"mixed_general_{d}\"", .{count}) ++
        original[at + old.len ..];
}

const Columns = struct {
    data: [8][]const M31,

    fn from(pp: *const DirectCircuit) !Columns {
        var result: Columns = undefined;
        for (circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, &result.data) |id, *column| {
            column.* = pp.columnValues(id) orelse return error.MissingFixedColumn;
            if (column.*.len != 512) return error.WrongFixedColumnLength;
        }
        return result;
    }

    fn at(self: Columns, column: usize, row: usize) u32 {
        return self.data[column][row].toU32();
    }

    fn expectRow(self: Columns, row: usize, opcode: usize, in0: u32, in1: u32, out: u32, mult: u32) !void {
        if (row >= 512) return error.WrongFixedRow;
        for (0..4) |flag| {
            if (self.at(flag, row) != @intFromBool(flag == opcode)) return error.WrongFixedRow;
        }
        const expected = [4]u32{ in0, in1, out, mult };
        for (expected, 4..) |want, column| {
            if (self.at(column, row) != want) return error.WrongFixedRow;
        }
    }
};

fn scalar(state: usize, lane: usize) u32 {
    std.debug.assert(lane < 4);
    return @intCast(if (state == 0) 11 + lane else 23 + 10 * (state - 1) + lane);
}

fn packedAddress(state: usize) u32 {
    return @intCast(22 + 10 * state);
}

/// The selected source rows have independent address and multiplicity
/// expectations. Constant-derivation and padding addresses outside these
/// rows are covered by a pinned native fixed-root regression value in `check`.
fn audit(pp: *const DirectCircuit, count: usize) !void {
    if (count != 1 and count != 8) return error.UnsupportedFixedFixture;
    const cols = try Columns.from(pp);
    const add_count = 468 - 7 * count;
    const mul_count = 30 + 3 * count;
    const pmul_count = 13 + 4 * count;
    const mul_start = add_count + 1;
    const pmul_start = mul_start + mul_count;
    if (pmul_start + pmul_count != 512 or pp.first_permutation_row != 512 or pp.n_outputs != 8)
        return error.WrongFixedSectionSize;
    // Every row has the expected opcode, including constants and padding.
    for (0..512) |row| {
        const opcode: usize = if (row < add_count) 0 else if (row == add_count) 1 else if (row < pmul_start) 2 else 3;
        for (0..4) |flag| {
            if (cols.at(flag, row) != @intFromBool(flag == opcode)) return error.WrongFixedSectionOpcode;
        }
    }

    // Each state packs four scalars with three Mul terms and three Add rows.
    // Only x and the final packed result feed the two public operations.
    for (0..count + 1) |state| {
        const base = packedAddress(state);
        const source = scalar(state, 0);
        const terms = [3]u32{ base - 5, base - 3, base - 1 };
        const basis = [3]u32{ 15, 2, 16 };
        const partial = [3]u32{ base - 4, base - 2, base };
        for (0..3) |part| {
            try cols.expectRow(mul_start + 3 * state + part, 2, basis[part], scalar(state, part + 1), terms[part], 1);
            const left = if (part == 0) source else partial[part - 1];
            const uses: u32 = if (part < 2) 1 else if (state == 0 or state == count) 2 else 0;
            try cols.expectRow(3 * state + part, 0, left, terms[part], partial[part], uses);
        }
    }

    const last = packedAddress(count);
    const sum = last + 1;
    const product = last + 2;
    try cols.expectRow(3 * (count + 1), 0, packedAddress(0), last, sum, 4);
    try cols.expectRow(pmul_start, 3, packedAddress(0), last, product, 4);

    // unpackIdx masks a packed coordinate, then multiplies by the inverse
    // basis for lanes 1..3. The product output reuses those inverse constants.
    const unit = [4]u32{ 1, 15, 2, 16 };
    const mask_offsets = [8]u32{ 3, 4, 7, 10, 13, 14, 16, 18 };
    const copy_offsets = [8]u32{ 3, 6, 9, 12, 13, 15, 17, 19 };
    const inverse_offsets = [6]u32{ 6, 9, 12, 15, 17, 19 };
    const inverse_input_offsets = [6]u32{ 5, 8, 11, 5, 8, 11 };
    const inverse_mask_slots = [6]usize{ 1, 2, 3, 5, 6, 7 };
    for (0..8) |slot| {
        const source = if (slot < 4) sum else product;
        try cols.expectRow(pmul_start + 1 + slot, 3, source, unit[slot % 4], last + mask_offsets[slot], 1);
        try cols.expectRow(3 * (count + 1) + 1 + slot, 0, last + copy_offsets[slot], 0, @intCast(3 + slot), 1);
    }
    for (0..6) |index| {
        const slot = inverse_mask_slots[index];
        try cols.expectRow(mul_start + 3 * (count + 1) + index, 2, last + mask_offsets[slot], last + inverse_input_offsets[index], last + inverse_offsets[index], 1);
    }

    // Finalization constrains every guessed scalar to M31. Each interior
    // endpoint is yielded to two chips, while the ends go to one chip.
    for (0..count + 1) |state| {
        for (0..4) |lane| {
            const address = scalar(state, lane);
            const mult: u32 = if (state == 0 or state == count) 3 else 4;
            try cols.expectRow(pmul_start + 9 + 4 * state + lane, 3, address, 1, address, mult);
        }
    }
}

fn check(comptime count: usize) !void {
    const allocator = std.testing.allocator;
    const source = comptime pinnedSource(count);
    const expected_source_sha256 = if (count == 1)
        "8c5296ef964e3be770e442cd28b66eed3051e210bdd6a97e265a4cd2c5962f75"
    else
        "08b5c20367e910261a194658bc3753038037fb85bc8f16dbc7f9191c7d1f45ff";
    var source_hash: [32]u8 = undefined;
    Sha256.hash(source, &source_hash, .{});
    const source_hex = std.fmt.bytesToHex(source_hash, .lower);
    if (!std.mem.eql(u8, &source_hex, expected_source_sha256)) return error.WrongFixedFixtureSource;

    const topology = try binding.compileSourceTopology(allocator, source);
    const expected_fixed_root = if (count == 1)
        "761dd5a42142ab2e8327ac0ca7ad31e1375b4f27c8e752eff766d7feea37cf00"
    else
        "68d7419f5be9e6e508ba2fafe1d8b34f4289cd2294708c332f4d646c4debe4b8";
    const root_hex = std.fmt.bytesToHex(topology.fixed_root, .lower);
    if (!std.mem.eql(u8, &root_hex, expected_fixed_root)) return error.WrongFixedFixtureRoot;
    var compiled = try binding.compileManyTopology(allocator, source, topology);
    defer compiled.deinit();
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&compiled.circuit);
    if (view.n_vars != 512 or view.add.len != 468 - 7 * count or view.sub.len != 1 or
        view.mul.len != 30 + 3 * count or view.pointwise_mul.len != 13 + 4 * count or
        view.nPermutations() != 0 or view.nQm31OpsRows() != 512)
        return error.WrongFixedFixtureShape;

    // Derive bridge endpoints from the source family rather than the emitted
    // maps, so their additional fixed multiplicities are checked too.
    var plan: cpu.private_many_boundary.Plan = .{ .count = count };
    for (0..count) |id| {
        var input: [4]u32 = undefined;
        var output: [4]u32 = undefined;
        for (0..4) |lane| {
            input[lane] = scalar(id, lane);
            output[lane] = scalar(id + 1, lane);
        }
        plan.calls[id] = .{
            .call_id = @intCast(id),
            .rounds = 16,
            .constant = M31.fromCanonical(@intCast(13 + id)),
            .input = input,
            .output = output,
        };
        try std.testing.expectEqualDeep(input, topology.calls[id].input);
        try std.testing.expectEqualDeep(output, topology.calls[id].output);
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    try std.testing.expectEqualDeep(topology.fixed_root, try pp.preprocessedRoot(allocator, 1));
    try audit(&pp, count);

    // Mutating a flag, input address, output address, or multiplicity must
    // invalidate the fixture check.
    for ([_]usize{ 0, 4, 6, 7 }) |column| {
        const original = pp.columns[column].values[0];
        pp.columns[column].values[0] = M31.fromCanonical(original.toU32() + 1);
        try std.testing.expectError(if (column == 0) error.WrongFixedSectionOpcode else error.WrongFixedRow, audit(&pp, count));
        pp.columns[column].values[0] = original;
    }
}

test "mixed N1 and N8 source base rows and proof envelope fixed-column correspondence" {
    try check(1);
    try check(8);
}
