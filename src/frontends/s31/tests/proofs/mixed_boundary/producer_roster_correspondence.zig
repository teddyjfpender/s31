//! Source-pinned N=1..8 logical Gate producer roster for the direct family.
//!
//! The modeled SourceMixedProducerCheck roster is one output per active Qm31
//! operation, followed by baseline yields. This test compares that exact
//! address/multiplicity projection with the production compiled gate lists and
//! fixed columns. It is an honest-circuit fixture, not proof authentication.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const binding = @import("../../../runtime/bounded_compiled_binding.zig");
const family = @import("../../../runtime/mixed_boundary/test_source.zig");

const M31 = core.fields.m31.M31;
const CircuitView = circuit.common.preprocessed.CircuitView;
const Preprocessed = circuit.common.direct_arithmetic.Circuit;
const BinaryGate = circuit.builder.circuit.BinaryGate;

const pinned_digests = [_][]const u8{
    "8c5296ef964e3be770e442cd28b66eed3051e210bdd6a97e265a4cd2c5962f75",
    "4b8f0660e7ac21ea31782fffc56300d0a5ad8bdb39b76317428e27380b4fc6ba",
    "06855c2bd39485f6a9b014da76b9db43c0f08f3c25ad216c45cd0442882686a6",
    "3508bf5b4e000e434e4c276758d66e85ddd8c2c4978f9a19d939792fd6e622d4",
    "168c4ada49a53759a4dd813fd51cf553de8b93656cb0a5e9870afa70d913e92e",
    "10acfa1c1d6694f88617cd7380e2663f705c70efc7b03baea2d3b8b529b14418",
    "425cfdafca60816bb38b1b6c46db3792e57534e15e9a237392b93d8fc0c39623",
    "08b5c20367e910261a194658bc3753038037fb85bc8f16dbc7f9191c7d1f45ff",
};

fn pinnedSource(comptime count: usize) []const u8 {
    const original = family.forCount(count);
    const old = "\"name\":\"mixed_descriptor_matrix\"";
    const at = comptime std.mem.indexOf(u8, original, old) orelse @compileError("missing fixture name");
    return original[0..at] ++
        std.fmt.comptimePrint("\"name\":\"mixed_general_{d}\"", .{count}) ++
        original[at + old.len ..];
}

const Row = struct { address: u32, multiplicity: u32 };

const Columns = struct {
    output: []const M31,
    multiplicity: []const M31,
    flags: [4][]const M31,

    fn from(pp: *const Preprocessed) !Columns {
        var flags: [4][]const M31 = undefined;
        for (circuit.common.preprocessed.QM31_OPS_COLUMN_IDS[0..4], &flags) |id, *column|
            column.* = pp.columnValues(id) orelse return error.MissingRosterColumn;
        const output = pp.columnValues(circuit.common.preprocessed.QM31_OPS_COLUMN_IDS[6]) orelse return error.MissingRosterColumn;
        const multiplicity = pp.columnValues(circuit.common.preprocessed.QM31_OPS_COLUMN_IDS[7]) orelse return error.MissingRosterColumn;
        for (flags) |flag| if (flag.len != output.len) return error.WrongRosterColumnLength;
        if (multiplicity.len != output.len) return error.WrongRosterColumnLength;
        return .{ .flags = flags, .output = output, .multiplicity = multiplicity };
    }
};

fn scanAddresses(rows: []const Row, bound: usize) !usize {
    if (bound != 512 or bound >= core.fields.m31.Modulus) return error.WrongRosterBound;
    var seen = [_]bool{false} ** 512;
    var active: usize = 0;
    for (rows) |row| {
        if (row.address >= bound) return error.ProducerAddressOutOfRange;
        if (row.multiplicity == 0) continue;
        if (seen[row.address]) return error.DuplicateLogicalProducer;
        seen[row.address] = true;
        active += 1;
    }
    return active;
}

fn checkGroup(cols: Columns, offset: usize, opcode: usize, gates: []const BinaryGate, uses: []const u32, rows: *[512]Row) !usize {
    for (gates, 0..) |gate, index| {
        const row = offset + index;
        if (row >= 512 or gate.out >= uses.len) return error.WrongRosterShape;
        for (cols.flags, 0..) |flag, bit|
            if (flag[row].toU32() != @intFromBool(bit == opcode)) return error.WrongRosterOpcode;
        if (cols.output[row].toU32() != gate.out or cols.multiplicity[row].toU32() != uses[gate.out])
            return error.WrongProducerRow;
        rows[row] = .{ .address = gate.out, .multiplicity = uses[gate.out] };
    }
    return offset + gates.len;
}

fn audit(allocator: std.mem.Allocator, view: CircuitView, pp: *const Preprocessed, topology: binding.Topology) !usize {
    // No other component in this family yields Gate values. Constants and
    // guessed inputs are already represented by finalization arithmetic rows;
    // public output and bridge events are Gate uses, not baseline yields.
    if (view.n_vars != 512 or view.nQm31OpsRows() != 512 or view.nPermutations() != 0 or
        view.eq.len != 0 or view.triple_xor.len != 0 or view.m31_to_u32.len != 0 or
        view.blake_g_gate.len != 0 or view.permutation_inputs.len != 0 or
        view.permutation_outputs.len != 0 or pp.first_permutation_row != 512 or
        pp.n_outputs != 8 or view.output.len != 9)
        return error.WrongRosterShape;
    const count = topology.call_count;
    if (count < 1 or count > 8 or view.add.len != 468 - 7 * count or view.sub.len != 1 or
        view.mul.len != 30 + 3 * count or view.pointwise_mul.len != 13 + 4 * count)
        return error.WrongRosterShape;
    for (view.output, 0..) |address, slot|
        if (address != 2 + slot) return error.WrongPublicUseRoster;

    const uses = try view.computeUses(allocator);
    defer allocator.free(uses);
    if (uses.len != 512) return error.WrongRosterBound;
    for (topology.callSlice(), 0..) |call, id| {
        if (call.call_id != id or call.rounds != 16 or call.constant != 13 + id)
            return error.WrongSourceCall;
        for (0..4) |lane| {
            const input: u32 = @intCast(if (id == 0) 11 + lane else 23 + 10 * (id - 1) + lane);
            const output: u32 = @intCast(23 + 10 * id + lane);
            if (call.input[lane] != input or call.output[lane] != output)
                return error.WrongSourceCall;
        }
        // One Gate use per bridge endpoint occurrence, including shared
        // intermediate states, exactly as production Plan.preprocessed does.
        for (call.input ++ call.output) |address| {
            if (address <= 2 or address >= view.n_vars) return error.ProducerAddressOutOfRange;
            try circuit.common.preprocessed.addCanonicalMultiplicity(&uses[address], 1);
        }
    }

    const cols = try Columns.from(pp);
    if (cols.output.len != 512) return error.WrongRosterColumnLength;
    var rows: [512]Row = undefined;
    var offset: usize = 0;
    offset = try checkGroup(cols, offset, 0, view.add, uses, &rows);
    offset = try checkGroup(cols, offset, 1, view.sub, uses, &rows);
    offset = try checkGroup(cols, offset, 2, view.mul, uses, &rows);
    offset = try checkGroup(cols, offset, 3, view.pointwise_mul, uses, &rows);
    if (offset != 512) return error.WrongRosterShape;

    // This is the executable Finset scan of SourceMixedProducerCheck's
    // `checkedRoster`: filter rows with positive multiplicity, take each
    // output address once, then append the empty baseline-yield list.
    const active = try scanAddresses(&rows, view.n_vars);
    if (active == 0 or active == rows.len) return error.WrongActiveRoster;
    for (topology.callSlice(), 0..) |call, id| {
        for (call.input ++ call.output, 0..) |address, slot| {
            const want: u32 = if ((id == 0 and slot < 4) or (id + 1 == count and slot >= 4)) 3 else 4;
            // Every endpoint is a guessed M31 variable, produced by its own
            // pointwise-mul finalization row, even if an internal address is
            // read by two adjacent bridges.
            const pointwise_index = 9 + 4 * (id + @intFromBool(slot >= 4)) + slot % 4;
            const guess_row = view.pointwise_mul[pointwise_index];
            if (guess_row.out != address or cols.multiplicity[view.add.len + view.sub.len + view.mul.len + pointwise_index].toU32() != want)
                return error.WrongEndpointProducer;
        }
    }
    return active;
}

fn mutableValue(pp: *Preprocessed, id: []const u8, row: usize) !*M31 {
    for (&pp.columns) |*column|
        if (std.mem.eql(u8, column.id, id)) return &column.values[row];
    return error.MissingRosterColumn;
}

fn fixture(comptime count: usize) !void {
    const allocator = std.testing.allocator;
    const source = comptime pinnedSource(count);
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(source, &digest, .{});
    const digest_hex = std.fmt.bytesToHex(digest, .lower);
    if (!std.mem.eql(u8, &digest_hex, pinned_digests[count - 1])) return error.WrongRosterSource;

    const topology = try binding.compileSourceTopology(allocator, source);
    if (!std.meta.eql(topology.source_sha256, digest)) return error.WrongRosterSource;
    var compiled = try binding.compileManyTopology(allocator, source, topology);
    defer compiled.deinit();
    const view = CircuitView.fromBuilder(&compiled.circuit);
    try view.validateUniqueProducers(allocator);
    var plan: cpu.private_many_boundary.Plan = .{ .count = count };
    for (topology.callSlice(), plan.calls[0..count]) |call, *slot|
        slot.* = .{ .call_id = call.call_id, .rounds = call.rounds, .constant = M31.fromCanonical(call.constant), .input = call.input, .output = call.output };
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const active = try audit(allocator, view, &pp, topology);
    try std.testing.expect(active > 8 * (count + 1));

    // A changed fixed address or multiplicity must break correspondence,
    // while a duplicate/out-of-range active producer breaks the scan itself.
    for ([_]usize{ 6, 7 }) |column| {
        const cell = try mutableValue(&pp, circuit.common.preprocessed.QM31_OPS_COLUMN_IDS[column], 0);
        const original = cell.*;
        cell.* = M31.fromCanonical(original.toU32() + 1);
        try std.testing.expectError(error.WrongProducerRow, audit(allocator, view, &pp, topology));
        cell.* = original;
    }
    const duplicate = [_]Row{ .{ .address = 11, .multiplicity = 1 }, .{ .address = 11, .multiplicity = 2 } };
    try std.testing.expectError(error.DuplicateLogicalProducer, scanAddresses(&duplicate, 512));
    const invalid = [_]Row{.{ .address = 512, .multiplicity = 1 }};
    try std.testing.expectError(error.ProducerAddressOutOfRange, scanAddresses(&invalid, 512));
    const inactive_invalid = [_]Row{.{ .address = 512, .multiplicity = 0 }};
    try std.testing.expectError(error.ProducerAddressOutOfRange, scanAddresses(&inactive_invalid, 512));
}

test "mixed N1 through N8 source logical producer roster" {
    inline for (1..9) |count| try fixture(count);
}

test "mixed fork counts every shared circuit-to-chip input in fixed multiplicity" {
    const allocator = std.testing.allocator;
    const source = @embedFile("../../../examples/boundary/private_arithmetic_chip_fork.s31.json");
    const topology = try binding.compileSourceTopology(allocator, source);
    try std.testing.expectEqual(@as(usize, 3), topology.call_count);
    try std.testing.expectEqualDeep(topology.calls[1].input, topology.calls[2].input);
    var compiled = try binding.compileManyTopology(allocator, source, topology);
    defer compiled.deinit();
    const view = CircuitView.fromBuilder(&compiled.circuit);
    try view.validateUniqueProducers(allocator);
    try std.testing.expectEqual(@as(usize, 512), view.nQm31OpsRows());
    var plan: cpu.private_many_boundary.Plan = .{ .count = 3 };
    for (topology.callSlice(), plan.calls[0..3]) |call, *slot| {
        slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const cols = try Columns.from(&pp);
    const ordinary_uses = try view.computeUses(allocator);
    defer allocator.free(ordinary_uses);

    // This is an independent oracle for the fixed Gate yield multiplicity:
    // circuit reads plus one read for *each* bridge endpoint occurrence.
    var expected = try allocator.dupe(u32, ordinary_uses);
    defer allocator.free(expected);
    for (topology.callSlice()) |call| {
        for (call.input ++ call.output) |address| {
            try circuit.common.preprocessed.addCanonicalMultiplicity(&expected[address], 1);
        }
    }
    var producer_count = [_]u8{0} ** 512;
    var row: usize = 0;
    inline for (.{ view.add, view.sub, view.mul, view.pointwise_mul }) |gates| {
        for (gates) |gate| {
            try std.testing.expect(gate.out < expected.len);
            try std.testing.expectEqual(gate.out, cols.output[row].toU32());
            try std.testing.expectEqual(expected[gate.out], cols.multiplicity[row].toU32());
            if (expected[gate.out] != 0) {
                try std.testing.expectEqual(@as(u8, 0), producer_count[gate.out]);
                producer_count[gate.out] = 1;
            }
            row += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 512), row);
    for (topology.calls[1].input) |shared| {
        try std.testing.expect(shared < expected.len);
        try std.testing.expectEqual(ordinary_uses[shared] + 2, expected[shared]);
        try std.testing.expectEqual(@as(u8, 1), producer_count[shared]);
    }
}
