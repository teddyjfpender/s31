//! Test-only reconstruction of a transparent Gate proof's producing trace.
//! The executable prints counts and commitment matches, never cells.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const prover = @import("stwo_prover_engine");
const postcard = @import("interop_postcard");
const s31 = @import("stwo_s31_prototype");
const canonical = s31.canonical;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Engine = cpu.Internal.Engine;
const Channel = cpu.Internal.Channel;
const ColumnEvaluation = prover.pcs.ColumnEvaluation;
const PP = circuit.common.preprocessed.PreprocessedCircuit;
const component = circuit.witness.components;
const trace = circuit.witness.trace;
const n_components = circuit.common.component_list.N_COMPONENTS;
const magic = "S31NAT1\x00";
const header_len = magic.len + 8 + n_components * 16;

fn fail(reason: []const u8) error{AuditMismatch} {
    std.debug.print("control claim trace: {s}\n", .{reason});
    return error.AuditMismatch;
}

fn cloneColumns(allocator: std.mem.Allocator, source: []const ColumnEvaluation) ![]ColumnEvaluation {
    const owned = try allocator.alloc(ColumnEvaluation, source.len);
    var ready: usize = 0;
    errdefer {
        for (owned[0..ready]) |entry| allocator.free(entry.values);
        allocator.free(owned);
    }
    for (source, owned) |entry, *slot| {
        slot.* = .{ .log_size = entry.log_size, .values = try allocator.dupe(M31, entry.values) };
        ready += 1;
    }
    return owned;
}

fn sameTopology(a: *const circuit.builder.Circuit, b: *const circuit.builder.Circuit) bool {
    if (a.n_vars != b.n_vars) return false;
    inline for (.{ "add", "sub", "mul", "pointwise_mul", "eq", "triple_xor", "m31_to_u32", "blake_g_gate", "output" }) |field| {
        const left = @field(a, field).items;
        const right = @field(b, field).items;
        if (left.len != right.len) return false;
        for (left, right) |x, y| if (!std.meta.eql(x, y)) return false;
    }
    return std.mem.eql(u32, a.permutation.ends.items, b.permutation.ends.items) and
        std.mem.eql(u32, a.permutation.inputs.items, b.permutation.inputs.items) and
        std.mem.eql(u32, a.permutation.outputs.items, b.permutation.outputs.items);
}

fn checkedSourceSpans(program: s31.relation.Program, ir: *const canonical.IR, maps: *const s31.relation_compiler.Maps, circuit_data: *const circuit.builder.Circuit) !void {
    if (ir.source_map.len != program.inputs.len + program.nodes.len or
        maps.nodes.items.len != ir.nodes.len or maps.node_wires.items.len != ir.nodes.len)
        return fail("source-to-canonical node roster changed");
    for (ir.source_map, 0..) |source, index| {
        const name = if (index < program.inputs.len) program.inputs[index].name else program.nodes[index - program.inputs.len].name;
        if (!std.mem.eql(u8, source.name, name) or source.id >= maps.nodes.items.len)
            return fail("source node lacks a physical compiler span");
        if (maps.nodes.items[source.id].id != source.id)
            return fail("source node points to a different physical span");
    }
    for (maps.nodes.items, 0..) |span, index| {
        const outputs = maps.node_wires.items[index];
        if (outputs.id != index) return fail("canonical node output wire id changed");
        for (outputs.wires) |address| if (address >= circuit_data.n_vars)
            return fail("canonical node output wire outside emitted circuit");
        if (span.id != index or span.var_start > span.var_end or span.var_end > circuit_data.n_vars or
            span.qm31_start > span.qm31_end or span.qm31_end > circuit_data.nQm31OpsRows() or
            span.eq_start > span.eq_end or span.eq_end > circuit_data.eq.items.len or
            span.triple_xor_start > span.triple_xor_end or span.triple_xor_end > circuit_data.triple_xor.items.len or
            span.m31_to_u32_start > span.m31_to_u32_end or span.m31_to_u32_end > circuit_data.m31_to_u32.items.len or
            span.blake_g_start > span.blake_g_end or span.blake_g_end > circuit_data.blake_g_gate.items.len)
            return fail("canonical node span is outside emitted circuit");
        if (index > 0) {
            const previous = maps.nodes.items[index - 1];
            if (previous.var_end != span.var_start or previous.qm31_end != span.qm31_start or
                previous.eq_end != span.eq_start or previous.triple_xor_end != span.triple_xor_start or
                previous.m31_to_u32_end != span.m31_to_u32_start or previous.blake_g_end != span.blake_g_start)
                return fail("canonical node spans leave an unowned physical row gap");
        }
    }
}

fn sameSourceSpans(a: *const s31.relation_compiler.Maps, b: *const s31.relation_compiler.Maps) bool {
    if (a.nodes.items.len != b.nodes.items.len or a.assertions.items.len != b.assertions.items.len or
        a.bindings.items.len != b.bindings.items.len or
        a.gate_op_spans.items.len != b.gate_op_spans.items.len or
        a.node_wires.items.len != b.node_wires.items.len) return false;
    for (a.nodes.items, b.nodes.items) |x, y| if (!std.meta.eql(x, y)) return false;
    for (a.gate_op_spans.items, b.gate_op_spans.items) |x, y| if (!std.meta.eql(x, y)) return false;
    for (a.node_wires.items, b.node_wires.items) |x, y| {
        if (x.id != y.id or !std.mem.eql(u32, x.wires, y.wires)) return false;
    }
    for (a.assertions.items, b.assertions.items) |x, y| if (!std.meta.eql(x, y)) return false;
    for (a.bindings.items, b.bindings.items) |x, y| {
        if (!std.mem.eql(u8, x.name, y.name) or x.word_start != y.word_start or x.word_count != y.word_count or
            x.conversion_var_start != y.conversion_var_start or x.conversion_var_end != y.conversion_var_end or
            x.conversion_qm31_start != y.conversion_qm31_start or x.conversion_qm31_end != y.conversion_qm31_end or
            x.conversion_m31_to_u32_start != y.conversion_m31_to_u32_start or
            x.conversion_m31_to_u32_end != y.conversion_m31_to_u32_end or
            x.binding_qm31_start != y.binding_qm31_start or x.binding_qm31_end != y.binding_qm31_end) return false;
    }
    return true;
}

const Range = struct { start: usize, end: usize };
const SourcePhysical = struct {
    name: []const u8,
    canonical_id: u32,
    canonical_tag: []const u8,
    packed_outputs: []const u32,
    add: Range,
    sub: Range,
    mul: Range,
    pointwise_mul: Range,
};
const AddConstComposition = struct {
    canonical_id: u32,
    lhs_canonical_id: u32,
    constant: u32,
    constant_address: u32,
    physical_in1: u32,
    lhs_packed_outputs: []const u32,
    output_packed_outputs: []const u32,
    add: Range,
};
const PhysicalCertificate = struct {
    schema: []const u8 = "s31-gate-source-physical-v4",
    program_sha256: []const u8,
    canonical_ir_sha256: []const u8,
    preprocessed_root: []const u8,
    n_vars: u32,
    canonical_node_count: usize,
    qm31_binary_rows: usize,
    source_qm31_rows: usize,
    primitive_nodes_checked: usize,
    add_const_compositions: []const AddConstComposition,
    seven_finalizations: []const SevenFinalization,
    constant_finalizations: []const ConstantFinalization,
    source_map: []const SourcePhysical,
};
const FinalizationGate = struct {
    kind: []const u8,
    row: usize,
    in0: u32,
    in1: u32,
    out: u32,
};
const SevenFinalization = struct {
    canonical_id: u32,
    constant_address: u32,
    gates: [15]FinalizationGate,
};
const ConstantFinalization = struct {
    canonical_id: u32,
    constant: u32,
    constant_address: u32,
    anchors: [3]FinalizationGate,
    steps: []const FinalizationGate,
};
const PhysicalCertificateResult = struct { source_rows: usize, digest: [32]u8 };

fn finalizationGate(circuit_data: *const circuit.builder.Circuit, pp: *const PP,
    base: *const trace.BaseTrace, values: []const QM31,
    source_ends: [3]usize,
    comptime kind: []const u8, in0: u32, in1: u32, expected_out: ?u32) !FinalizationGate {
    const gates = @field(circuit_data.*, kind).items;
    const offset = if (std.mem.eql(u8, kind, "add")) 0 else if (std.mem.eql(u8, kind, "sub"))
        circuit_data.add.items.len else circuit_data.add.items.len + circuit_data.sub.items.len;
    const flag: usize = if (std.mem.eql(u8, kind, "add")) 0 else if (std.mem.eql(u8, kind, "sub")) 1 else 2;
    var found: ?FinalizationGate = null;
    for (gates, 0..) |gate, index| {
        if (index < source_ends[flag] or gate.in0 != in0 or gate.in1 != in1 or
            (expected_out != null and gate.out != expected_out.?)) continue;
        const row = offset + index;
        const mult = pp.columnValues(circuit.common.preprocessed.QM31_OPS_COLUMN_IDS[7]) orelse
            return fail("finalization multiplicity missing");
        if (row >= mult.len or mult[row].toU32() == 0) continue;
        const ids = circuit.common.preprocessed.QM31_OPS_COLUMN_IDS;
        inline for (0..4) |column| {
            const fixed = pp.columnValues(ids[column]) orelse return fail("finalization selector missing");
            if (row >= fixed.len or fixed[row].toU32() != @intFromBool(column == flag))
                return fail("finalization selector differs from installed row");
        }
        inline for (0..3) |column| {
            const fixed = pp.columnValues(ids[4 + column]) orelse return fail("finalization address missing");
            const address = if (column == 0) gate.in0 else if (column == 1) gate.in1 else gate.out;
            if (row >= fixed.len or fixed[row].toU32() != address)
                return fail("finalization address differs from installed row");
        }
        const first = trace.traceWidths()[0];
        if (gate.in0 >= values.len or gate.in1 >= values.len or gate.out >= values.len)
            return fail("finalization address exceeds value table");
        const expected = .{ values[gate.in0].toM31Array(), values[gate.in1].toM31Array(), values[gate.out].toM31Array() };
        inline for (0..3) |part| inline for (0..4) |coord| {
            const column = first + part * 4 + coord;
            if (column >= base.columns.len or row >= base.columns[column].values.len or
                !base.columns[column].values[row].eql(expected[part][coord]))
                return fail("finalization row differs from reconstructed committed base cells");
        };
        var words: [component.qm31_ops.n_columns]M31 = undefined;
        for (&words, base.columns[first..][0..component.qm31_ops.n_columns]) |*word, column|
            word.* = column.values[row];
        const lookups = component.qm31_ops.lookups(&words, .{
            .in0 = (pp.columnValues(ids[4]) orelse unreachable)[row],
            .in1 = (pp.columnValues(ids[5]) orelse unreachable)[row],
            .out = (pp.columnValues(ids[6]) orelse unreachable)[row],
            .mults = mult[row],
        });
        if (!gateYield(lookups[2], (pp.columnValues(ids[6]) orelse unreachable)[row],
            mult[row], words[8..12]))
            return fail("finalization Gate producer lookup differs from row cells");
        found = .{ .kind = kind, .row = row, .in0 = gate.in0, .in1 = gate.in1, .out = gate.out };
        break;
    }
    return found orelse fail("finalization gate missing");
}

fn checkedSevenFinalizations(allocator: std.mem.Allocator, compositions: []const AddConstComposition,
    circuit_data: *const circuit.builder.Circuit, pp: *const PP,
    base: *const trace.BaseTrace, values: []const QM31, source_ends: [3]usize) ![]SevenFinalization {
    var count: usize = 0;
    for (compositions) |entry| if (entry.constant == 7) { count += 1; };
    const paths = try allocator.alloc(SevenFinalization, count);
    errdefer allocator.free(paths);
    if (count == 0) return paths;
    if (circuit_data.output.items.len == 0 or circuit_data.output.items[0] != 2 or
        values.len <= 2 or !values[2].eql(QM31.fromU32Unchecked(0, 0, 1, 0)))
        return fail("seven finalization public u anchor differs");
    var next: usize = 0;
    for (compositions) |entry| {
        if (entry.constant != 7) continue;
        var gates: [15]FinalizationGate = undefined;
        gates[0] = try finalizationGate(circuit_data, pp, base, values, source_ends, "add", 0, 0, 0);
        gates[1] = try finalizationGate(circuit_data, pp, base, values, source_ends, "add", 1, 0, 1);
        gates[2] = try finalizationGate(circuit_data, pp, base, values, source_ends, "mul", 2, 1, 2);
        gates[3] = try finalizationGate(circuit_data, pp, base, values, source_ends, "add", 1, 1, null);
        for (4..9) |index| gates[index] = try finalizationGate(circuit_data, pp, base, values, source_ends,
            "add", gates[index - 1].out, 1, null);
        gates[9] = try finalizationGate(circuit_data, pp, base, values, source_ends, "mul", 2, 2, null);
        gates[10] = try finalizationGate(circuit_data, pp, base, values, source_ends, "sub", gates[9].out, gates[3].out, null);
        gates[11] = try finalizationGate(circuit_data, pp, base, values, source_ends, "add", gates[10].out, 1, null);
        gates[12] = try finalizationGate(circuit_data, pp, base, values, source_ends, "mul", gates[11].out, 2, null);
        gates[13] = try finalizationGate(circuit_data, pp, base, values, source_ends, "add", gates[11].out, gates[12].out, null);
        gates[14] = try finalizationGate(circuit_data, pp, base, values, source_ends, "mul", gates[8].out,
            gates[13].out, entry.constant_address);
        const seven = QM31.fromU32Unchecked(7, 7, 7, 7);
        if (!values[entry.constant_address].eql(seven))
            return fail("seven finalization constant cell differs from seven");
        paths[next] = .{ .canonical_id = entry.canonical_id,
            .constant_address = entry.constant_address, .gates = gates };
        next += 1;
    }
    return paths;
}

fn finalizationProducer(circuit_data: *const circuit.builder.Circuit, pp: *const PP,
    base: *const trace.BaseTrace, values: []const QM31,
    source_ends: [3]usize, address: u32) !FinalizationGate {
    const ids = circuit.common.preprocessed.QM31_OPS_COLUMN_IDS;
    const multiplicities = pp.columnValues(ids[7]) orelse
        return fail("constant DAG output multiplicity column missing");
    var found: ?FinalizationGate = null;
    inline for (.{ "add", "sub", "mul" }, 0..) |kind, class| {
        const gates = @field(circuit_data.*, kind).items;
        const offset = if (class == 0) 0 else if (class == 1)
            circuit_data.add.items.len else circuit_data.add.items.len + circuit_data.sub.items.len;
        for (gates[source_ends[class]..], source_ends[class]..) |gate, index| {
            const row = offset + index;
            if (gate.out != address or row >= multiplicities.len or
                multiplicities[row].toU32() == 0) continue;
            if (found != null) return fail("constant DAG has two active finalization producers");
            found = try finalizationGate(circuit_data, pp, base, values,
                source_ends, kind, gate.in0, gate.in1, address);
        }
    }
    return found orelse fail("constant DAG target lacks active finalization producer");
}

const ConstantPathBuilder = struct {
    allocator: std.mem.Allocator,
    circuit_data: *const circuit.builder.Circuit,
    pp: *const PP,
    base: *const trace.BaseTrace,
    values: []const QM31,
    source_ends: [3]usize,
    known: std.AutoHashMap(u32, QM31),
    visiting: std.AutoHashMap(u32, void),
    steps: std.ArrayListUnmanaged(FinalizationGate) = .empty,

    fn init(allocator: std.mem.Allocator, circuit_data: *const circuit.builder.Circuit,
        pp: *const PP, base: *const trace.BaseTrace, values: []const QM31,
        source_ends: [3]usize) !ConstantPathBuilder {
        var result: ConstantPathBuilder = .{
            .allocator = allocator, .circuit_data = circuit_data, .pp = pp,
            .base = base, .values = values, .source_ends = source_ends,
            .known = std.AutoHashMap(u32, QM31).init(allocator),
            .visiting = std.AutoHashMap(u32, void).init(allocator),
        };
        errdefer result.deinit();
        try result.known.put(0, QM31.zero());
        try result.known.put(1, QM31.fromU32Unchecked(1, 0, 0, 0));
        try result.known.put(2, QM31.fromU32Unchecked(0, 0, 1, 0));
        return result;
    }

    fn deinit(self: *ConstantPathBuilder) void {
        self.known.deinit();
        self.visiting.deinit();
        self.steps.deinit(self.allocator);
    }

    fn derive(self: *ConstantPathBuilder, address: u32, depth: usize) !QM31 {
        if (self.known.get(address)) |value| return value;
        if (depth > self.values.len or address >= self.values.len)
            return fail("constant DAG depth or address exceeds circuit bound");
        const visiting = try self.visiting.getOrPut(address);
        if (visiting.found_existing) return fail("constant DAG has a cycle");
        defer _ = self.visiting.remove(address);
        const gate = try finalizationProducer(self.circuit_data, self.pp, self.base,
            self.values, self.source_ends, address);
        const left = try self.derive(gate.in0, depth + 1);
        const right = try self.derive(gate.in1, depth + 1);
        const expected = if (std.mem.eql(u8, gate.kind, "add")) left.add(right) else
            if (std.mem.eql(u8, gate.kind, "sub")) left.sub(right) else left.mul(right);
        if (!self.values[address].eql(expected))
            return fail("constant DAG AIR-derived value differs from reconstructed base cell");
        try self.steps.append(self.allocator, gate);
        try self.known.put(address, expected);
        return expected;
    }
};

fn checkedConstantFinalizations(allocator: std.mem.Allocator,
    compositions: []const AddConstComposition,
    circuit_data: *const circuit.builder.Circuit, pp: *const PP,
    base: *const trace.BaseTrace, values: []const QM31,
    source_ends: [3]usize) ![]ConstantFinalization {
    const paths = try allocator.alloc(ConstantFinalization, compositions.len);
    var made: usize = 0;
    errdefer {
        for (paths[0..made]) |path| allocator.free(path.steps);
        allocator.free(paths);
    }
    if (compositions.len == 0) return paths;
    if (circuit_data.output.items.len == 0 or circuit_data.output.items[0] != 2 or
        values.len <= 2 or !values[0].eql(QM31.zero()) or
        !values[1].eql(QM31.fromU32Unchecked(1, 0, 0, 0)) or
        !values[2].eql(QM31.fromU32Unchecked(0, 0, 1, 0)))
        return fail("constant DAG public roots differ from native anchor values");
    const anchors: [3]FinalizationGate = .{
        try finalizationProducer(circuit_data, pp, base, values, source_ends, 0),
        try finalizationProducer(circuit_data, pp, base, values, source_ends, 1),
        try finalizationProducer(circuit_data, pp, base, values, source_ends, 2),
    };
    if (!std.mem.eql(u8, anchors[0].kind, "add") or anchors[0].in0 != 0 or
        anchors[0].in1 != 0 or !std.mem.eql(u8, anchors[1].kind, "add") or
        anchors[1].in0 != 1 or anchors[1].in1 != 0 or
        !std.mem.eql(u8, anchors[2].kind, "mul") or
        anchors[2].in0 != 2 or anchors[2].in1 != 1)
        return fail("constant DAG zero, one, or public u anchor differs");
    for (compositions) |entry| {
        var builder = try ConstantPathBuilder.init(allocator, circuit_data, pp, base,
            values, source_ends);
        defer builder.deinit();
        const forced = try builder.derive(entry.constant_address, 0);
        const scalar = M31.fromCanonical(entry.constant);
        const expected = QM31.fromM31(scalar, scalar, scalar, scalar);
        if (!forced.eql(expected))
            return fail("constant DAG result differs from canonical add_const literal");
        paths[made] = .{ .canonical_id = entry.canonical_id,
            .constant = entry.constant, .constant_address = entry.constant_address,
            .anchors = anchors, .steps = try builder.steps.toOwnedSlice(allocator) };
        made += 1;
    }
    return paths;
}

fn checkedAddConstCompositions(allocator: std.mem.Allocator, ir: *const canonical.IR,
    maps: *const s31.relation_compiler.Maps, ctx: *const circuit.builder.Context(circuit.builder.NoValue)) ![]AddConstComposition {
    var count: usize = 0;
    for (ir.nodes) |node| if (node.tag == .add_const) { count += 1; };
    const checked = try allocator.alloc(AddConstComposition, count);
    errdefer allocator.free(checked);
    var next: usize = 0;
    for (ir.nodes, 0..) |node, id| {
        if (node.tag != .add_const) continue;
        const lhs_id = node.lhs orelse return fail("add_const canonical lhs missing");
        const constant = node.constant orelse return fail("add_const canonical constant missing");
        if (constant == 0) return fail("zero add_const should have canonicalized to an alias");
        const value = M31.fromCanonical(constant);
        const broadcast = QM31.fromM31(value, value, value, value);
        const constant_var = ctx.constants.get(circuit.builder.context.constantKey(broadcast)) orelse
            return fail("add_const broadcast constant is not interned");
        const lhs = maps.node_wires.items[lhs_id].wires;
        const output = maps.node_wires.items[id].wires;
        const span = maps.gate_op_spans.items[id];
        if (lhs.len != output.len or output.len == 0 or span.add_end < span.add_start or
            span.add_end > ctx.circuit.add.items.len or
            span.add_end - span.add_start != output.len or
            span.sub_end != span.sub_start or span.mul_end != span.mul_start or
            span.pointwise_end != span.pointwise_start)
            return fail("add_const node does not have one add row per packed word");
        for (lhs, output, 0..) |left, out, index| {
            const gate = ctx.circuit.add.items[span.add_start + index];
            if (gate.in0 != left or gate.in1 != constant_var.idx or gate.out != out)
                return fail("add_const physical row differs from canonical port or constant");
        }
        checked[next] = .{
            .canonical_id = @intCast(id), .lhs_canonical_id = @intCast(lhs_id),
            .constant = constant, .constant_address = constant_var.idx,
            .physical_in1 = ctx.circuit.add.items[span.add_start].in1,
            .lhs_packed_outputs = lhs, .output_packed_outputs = output,
            .add = .{ .start = span.add_start, .end = span.add_end },
        };
        next += 1;
    }
    return checked;
}

fn checkedPrimitiveNodes(ir: *const canonical.IR, maps: *const s31.relation_compiler.Maps,
    circuit_data: *const circuit.builder.Circuit) !usize {
    var checked: usize = 0;
    for (ir.nodes, 0..) |node, id| {
        const kind: usize = switch (node.tag) {
            .add => 0,
            .sub => 1,
            .mul => 3,
            else => continue,
        };
        const lhs = maps.node_wires.items[node.lhs.?].wires;
        const rhs = maps.node_wires.items[node.rhs.?].wires;
        const outputs = maps.node_wires.items[id].wires;
        if (outputs.len != lhs.len or outputs.len != rhs.len)
            return fail("primitive canonical node has mismatched packed port count");
        const span = maps.gate_op_spans.items[id];
        const gates = switch (kind) {
            0 => circuit_data.add.items,
            1 => circuit_data.sub.items,
            else => circuit_data.pointwise_mul.items,
        };
        const start = if (kind == 0) span.add_start else if (kind == 1) span.sub_start else span.pointwise_start;
        const end = if (kind == 0) span.add_end else if (kind == 1) span.sub_end else span.pointwise_end;
        for (outputs, lhs, rhs) |out, left, right| {
            var found = false;
            for (gates[start..end]) |gate| {
                if (gate.out == out and gate.in0 == left and gate.in1 == right) {
                    found = true;
                    break;
                }
            }
            if (!found) return fail("primitive canonical node lacks matching physical operation gate");
        }
        checked += 1;
    }
    return checked;
}

fn checkedPhysicalRows(allocator: std.mem.Allocator, source: []const u8, ir: *const canonical.IR,
    maps: *const s31.relation_compiler.Maps, circuit_data: *const circuit.builder.Circuit,
    ctx: *const circuit.builder.Context(circuit.builder.NoValue),
    pp: *const PP, base: *const trace.BaseTrace, values: []const QM31,
    certificate_path: ?[]const u8) !PhysicalCertificateResult {
    if (maps.gate_op_spans.items.len != ir.nodes.len) return fail("canonical QM31 per-op spans missing");
    const ids = circuit.common.preprocessed.QM31_OPS_COLUMN_IDS;
    var fixed: [ids.len][]const M31 = undefined;
    for (ids, &fixed) |id, *column| column.* = pp.columnValues(id) orelse return fail("QM31 fixed column missing");
    const offsets = [4]usize{ 0, circuit_data.add.items.len,
        circuit_data.add.items.len + circuit_data.sub.items.len,
        circuit_data.add.items.len + circuit_data.sub.items.len + circuit_data.mul.items.len };
    const groups = .{ circuit_data.add.items, circuit_data.sub.items,
        circuit_data.mul.items, circuit_data.pointwise_mul.items };
    const start_names = .{ "add_start", "sub_start", "mul_start", "pointwise_start" };
    const end_names = .{ "add_end", "sub_end", "mul_end", "pointwise_end" };
    const binary_rows = offsets[3] + circuit_data.pointwise_mul.items.len;
    if (binary_rows != pp.first_permutation_row) return fail("QM31 physical binary prefix changed");
    const primitive_nodes = try checkedPrimitiveNodes(ir, maps, circuit_data);
    const add_const_compositions = try checkedAddConstCompositions(allocator, ir, maps, ctx);
    defer allocator.free(add_const_compositions);
    const source_ends: [3]usize = if (maps.gate_op_spans.items.len == 0) .{ 0, 0, 0 } else blk: {
        const last = maps.gate_op_spans.items[maps.gate_op_spans.items.len - 1];
        break :blk .{ last.add_end, last.sub_end, last.mul_end };
    };
    const seven_finalizations = try checkedSevenFinalizations(allocator, add_const_compositions,
        circuit_data, pp, base, values, source_ends);
    defer allocator.free(seven_finalizations);
    const constant_finalizations = try checkedConstantFinalizations(allocator,
        add_const_compositions, circuit_data, pp, base, values, source_ends);
    defer {
        for (constant_finalizations) |path| allocator.free(path.steps);
        allocator.free(constant_finalizations);
    }
    var source_rows: usize = 0;
    for (maps.gate_op_spans.items, 0..) |span, id| {
        if (span.id != id) return fail("canonical QM31 per-op span id changed");
        inline for (groups, 0..) |gates, kind| {
            const start = @field(span, start_names[kind]);
            const end = @field(span, end_names[kind]);
            if (start > end or end > gates.len) return fail("canonical QM31 span outside physical component");
            if (id > 0 and @field(maps.gate_op_spans.items[id - 1], end_names[kind]) != start)
                return fail("canonical QM31 per-op spans leave a source row gap");
            for (start..end) |gate_index| {
                const row = offsets[kind] + gate_index;
                const gate = gates[gate_index];
                if (row >= fixed[0].len or fixed[4][row].toU32() != gate.in0 or
                    fixed[5][row].toU32() != gate.in1 or fixed[6][row].toU32() != gate.out)
                    return fail("source gate differs from physical fixed addresses");
                inline for (0..4) |flag| if (fixed[flag][row].toU32() != @intFromBool(kind == flag))
                    return fail("source gate differs from physical AIR selector");
                source_rows += 1;
            }
        }
    }
    var certificate_digest: [32]u8 = .{0} ** 32;
    if (certificate_path) |path| {
        const mapped = try allocator.alloc(SourcePhysical, ir.source_map.len);
        defer allocator.free(mapped);
        for (ir.source_map, mapped) |source_node, *item| {
            const span = maps.gate_op_spans.items[source_node.id];
            item.* = .{
                .name = source_node.name, .canonical_id = source_node.id,
                .canonical_tag = @tagName(ir.nodes[source_node.id].tag),
                .packed_outputs = maps.node_wires.items[source_node.id].wires,
                .add = .{ .start = span.add_start, .end = span.add_end },
                .sub = .{ .start = offsets[1] + span.sub_start, .end = offsets[1] + span.sub_end },
                .mul = .{ .start = offsets[2] + span.mul_start, .end = offsets[2] + span.mul_end },
                .pointwise_mul = .{ .start = offsets[3] + span.pointwise_start,
                    .end = offsets[3] + span.pointwise_end },
            };
        }
        var source_digest: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(source, &source_digest, .{});
        const source_hex = std.fmt.bytesToHex(source_digest, .lower);
        const ir_hex = std.fmt.bytesToHex(ir.sha256, .lower);
        const root_hex = std.fmt.bytesToHex(try pp.preprocessedRoot(allocator, 1), .lower);
        const cert: PhysicalCertificate = .{
            .program_sha256 = &source_hex,
            .canonical_ir_sha256 = &ir_hex,
            .preprocessed_root = &root_hex,
            .n_vars = circuit_data.n_vars,
            .canonical_node_count = ir.nodes.len,
            .qm31_binary_rows = binary_rows,
            .source_qm31_rows = source_rows,
            .primitive_nodes_checked = primitive_nodes,
            .add_const_compositions = add_const_compositions,
            .seven_finalizations = seven_finalizations,
            .constant_finalizations = constant_finalizations,
            .source_map = mapped,
        };
        const encoded = try std.json.Stringify.valueAlloc(allocator, cert, .{});
        defer allocator.free(encoded);
        std.crypto.hash.sha2.Sha256.hash(encoded, &certificate_digest, .{});
        try std.fs.cwd().writeFile(.{ .sub_path = path, .data = encoded });
    }
    return .{ .source_rows = source_rows, .digest = certificate_digest };
}

fn gateYield(lookup: component.Lookup, address: M31, multiplicity: M31, expected: []const M31) bool {
    if (lookup.relation() != circuit.common.component_list.GATE_RELATION_ID or
        !lookup.numerator.eql(multiplicity.neg()) or
        lookup.len != expected.len + 2 or
        lookup.tuple[1].toU32() != address.toU32()) return false;
    for (expected, lookup.tuple[2..lookup.len]) |a, b| if (!a.eql(b)) return false;
    return true;
}

/// All four Gate-producing components are enumerated. The table components
/// have no Gate yields. A zero multiplicity is not an active producer.
fn producerCounts(pp: *const PP, columns: []const ColumnEvaluation) ![4]usize {
    var seen = std.AutoHashMap(u32, void).init(std.heap.page_allocator);
    defer seen.deinit();
    const widths = trace.traceWidths();
    var offsets: [n_components]usize = undefined;
    var offset: usize = 0;
    for (widths, &offsets) |width, *slot| { slot.* = offset; offset += width; }
    if (columns.len != offset) return fail("base component width changed");
    const groups = .{
        .{ component.qm31_ops, 1, circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, 6, 7, 8, 12, 2 },
        .{ component.triple_xor, 2, circuit.common.preprocessed.TRIPLE_XOR_COLUMN_IDS, 3, 4, 6, 8, 11 },
        .{ component.m31_to_u32, 3, circuit.common.preprocessed.M31_TO_U32_COLUMN_IDS, 1, 2, 1, 3, 4 },
        .{ component.blake_g_gate, 4, circuit.common.preprocessed.BLAKE_G_GATE_COLUMN_IDS, 6, 10, 12, 20, 25 },
    };
    var counts: [4]usize = @splat(0);
    inline for (groups, 0..) |group, group_index| {
        const K = group[0];
        const component_index = group[1];
        const ids = group[2];
        const out_col = pp.columnValues(ids[group[3]]) orelse return fail("missing fixed output address");
        const mult_col = pp.columnValues(ids[group[4]]) orelse return fail("missing fixed output multiplicity");
        const width = K.n_columns;
        const start = offsets[component_index];
        const rows = columns[start].values.len;
        if (out_col.len != rows or mult_col.len != rows) return fail("producer component row count changed");
        for (0..rows) |r| {
            const mult = mult_col[r].toU32();
            if (mult == 0) continue;
            var words: [width]M31 = undefined;
            for (&words, columns[start..][0..width]) |*word, col| word.* = col.values[r];
            // This checks the concrete base cells and fixed cells used by the
            // installed lookup tuple. The row's AIR residuals are separate.
            const output = words[group[5]..group[6]];
            if (group_index == 0) {
                const lookups = K.lookups(&words, .{
                    .in0 = (pp.columnValues(ids[4]) orelse unreachable)[r],
                    .in1 = (pp.columnValues(ids[5]) orelse unreachable)[r],
                    .out = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("QM31 producer tuple differs from base cells");
            } else if (group_index == 1) {
                const lookups = K.lookups(&words, .{
                    .in0 = (pp.columnValues(ids[0]) orelse unreachable)[r],
                    .in1 = (pp.columnValues(ids[1]) orelse unreachable)[r],
                    .in2 = (pp.columnValues(ids[2]) orelse unreachable)[r],
                    .out = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("triple XOR producer tuple differs from base cells");
            } else if (group_index == 2) {
                const lookups = K.lookups(&words, .{
                    .input = (pp.columnValues(ids[0]) orelse unreachable)[r],
                    .output = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("conversion producer tuple differs from base cells");
            } else {
                var inputs: [6]M31 = undefined;
                var outputs: [4]M31 = undefined;
                inline for (0..6) |i| inputs[i] = (pp.columnValues(ids[i]) orelse unreachable)[r];
                inline for (0..4) |i| outputs[i] = (pp.columnValues(ids[6 + i]) orelse unreachable)[r];
                const lookups = K.lookups(&words, .{ .inputs = inputs, .outputs = outputs, .mults = mult_col[r] });
                // Four output tuples, each encoded by two base limbs.
                for (0..4) |i| {
                    if (!gateYield(lookups[22 + i], outputs[i], mult_col[r], words[12 + i * 2 ..][0..2]))
                        return fail("Blake G producer tuple differs from base cells");
                    const entry = try seen.getOrPut(outputs[i].toU32());
                    if (entry.found_existing) return fail("two active Gate components own one address");
                }
            }
            if (group_index != 3) {
                const entry = try seen.getOrPut(out_col[r].toU32());
                if (entry.found_existing) return fail("two active Gate components own one address");
            }
            counts[group_index] += if (group_index == 3) 4 else 1;
        }
    }
    return counts;
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 5 and args.len != 6) return fail("usage: native-control-claim-trace source.s31.json assignment.json proof statement.json [certificate.json]");
    const source_bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(source_bytes);
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 1 << 20);
    defer allocator.free(assignment_bytes);
    const proof_bytes = try std.fs.cwd().readFileAlloc(allocator, args[3], 16 << 20);
    defer allocator.free(proof_bytes);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[4], 1 << 20);
    defer allocator.free(statement_bytes);
    var program = try s31.relation.parseProgram(allocator, source_bytes);
    defer program.deinit();
    var assignment = try s31.relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    var statement = try s31.relation.parseAssignment(allocator, statement_bytes);
    defer statement.deinit();
    if (program.value.proof_mode != .transparent) return fail("only deterministic transparent Gate profile is audited");
    const words = try s31.relation.claimedWords(allocator, program.value, statement.value);
    const witness_words = try s31.relation.claimedWords(allocator, program.value, assignment.value);
    if (!std.meta.eql(words, witness_words)) return fail("assignment and public statement differ");
    const evaluated_words = try s31.relation.evaluate(allocator, program.value, assignment.value);
    if (!std.meta.eql(words, evaluated_words)) return fail("source evaluator and public statement differ");
    var ir = try canonical.build(allocator, program.value);
    defer ir.deinit();
    var value_maps: s31.relation_compiler.Maps = .{ .capture_gate_op_spans = true, .capture_node_wires = true };
    defer value_maps.deinit(allocator);
    var topology_maps: s31.relation_compiler.Maps = .{ .capture_gate_op_spans = true, .capture_node_wires = true };
    defer topology_maps.deinit(allocator);
    var value_ctx = try s31.relation_compiler.compileWithSpans(QM31, allocator, program.value, assignment.value, &value_maps);
    defer value_ctx.deinit();
    var topology_ctx = try s31.relation_compiler.compileWithSpans(circuit.builder.NoValue, allocator, program.value, null, &topology_maps);
    defer topology_ctx.deinit();
    if (!sameSourceSpans(&value_maps, &topology_maps))
        return fail("witness changes source-to-circuit physical spans");
    try checkedSourceSpans(program.value, &ir, &topology_maps, &topology_ctx.circuit);
    if (!sameTopology(&value_ctx.circuit, &topology_ctx.circuit)) return fail("value-dependent compiler topology");
    try circuit.common.finalize.padContext(QM31, &value_ctx);
    try circuit.common.finalize.padContext(circuit.builder.NoValue, &topology_ctx);
    if (!sameTopology(&value_ctx.circuit, &topology_ctx.circuit) or !(try value_ctx.isCircuitValid()))
        return fail("padded compiler topology or witness invalid");
    var pp = try PP.fromBuilderCircuit(allocator, &topology_ctx.circuit);
    defer pp.deinit(allocator);
    var base = try trace.writeTrace(allocator, value_ctx.values(), &pp);
    defer base.deinit();
    if (base.output_values.len != words.len) return fail("public word count differs from trace");
    for (words, base.output_values) |word, output| {
        if (!output.eql(QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0)))
            return fail("public claim differs from base output cells");
    }
    const counts = try producerCounts(&pp, base.columns);
    if (proof_bytes.len < header_len or !std.mem.eql(u8, proof_bytes[0..magic.len], magic))
        return fail("proof envelope changed");
    const nonce = std.mem.readInt(u64, proof_bytes[magic.len..][0..8], .little);
    var sums: [n_components]QM31 = undefined;
    for (&sums, 0..) |*sum, i| {
        const offset = magic.len + 8 + i * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, proof_bytes[offset + j * 4 ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return fail("noncanonical interaction claim");
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    var stream = std.io.fixedBufferStream(proof_bytes[header_len..]);
    var stark = try postcard.deserializeProof(H, allocator, stream.reader());
    defer stark.deinit(allocator);
    if (stream.pos != proof_bytes.len - header_len or stark.commitment_scheme_proof.commitments.items.len != 4)
        return fail("proof commitment shape changed");
    const roots = stark.commitment_scheme_proof.commitments.items;
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndTraceSize(
        try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1), pp.traceLogSize());
    var fixed = try cpu.prove.PreprocessedCommitment.build(allocator, &pp, pcs, .{});
    defer fixed.deinit(allocator);
    if (!std.meta.eql(fixed.root(), roots[0])) return fail("fixed proof root changed");
    var channel = Channel{};
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try Engine.initRevision(allocator, pcs);
    defer Engine.deinit(&scheme, allocator);
    scheme.setStorePolynomialsCoefficients();
    {
        var lease = fixed.tree.retainShared();
        errdefer lease.deinit(allocator);
        try scheme.appendCommittedTree(allocator, lease, &channel);
    }
    const hash = try circuit.common.circuit_hash.hostCircuitHash(base.log_sizes, pcs.fri_config.log_blowup_factor, roots[0]);
    cpu.prove.profiles.Blake2sM31MerkleChannel.mixRoot(&channel, hash);
    channel.mixFelts(base.output_values);
    try Engine.commit(&scheme, allocator, try cloneColumns(allocator, base.columns), null, &channel);
    try Engine.flushPendingCommit(&scheme, allocator, &channel);
    if (!std.meta.eql(scheme.trees.items[1].commitment.root(), roots[1]))
        return fail("reconstructed base cells differ from committed main root");
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return fail("interaction nonce changed");
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    var interaction = try trace.writeInteractionTrace(allocator, base.columns, base.log_sizes, &pp, lookup.z, lookup.alpha);
    defer interaction.deinit();
    for (interaction.claimed_sums.toArray(), sums) |actual, claimed| {
        if (!actual.eql(claimed)) return fail("interaction claim differs from committed base-cell lookup reconstruction");
    }
    if (!(try trace.lookupSum(base.output_values, interaction.claimed_sums, lookup.z, lookup.alpha)).isZero())
        return fail("reconstructed public Gate interaction does not close");
    core.channel.lookup_transcript.mixInteractionClaim(&channel, &sums);
    try Engine.commit(&scheme, allocator, try cloneColumns(allocator, interaction.columns), null, &channel);
    try Engine.flushPendingCommit(&scheme, allocator, &channel);
    if (!std.meta.eql(scheme.trees.items[2].commitment.root(), roots[2]))
        return fail("reconstructed interaction cells differ from committed interaction root");
    const source_result = try checkedPhysicalRows(allocator, source_bytes, &ir,
        &topology_maps, &topology_ctx.circuit, &topology_ctx, &pp, &base,
        value_ctx.values(), if (args.len == 6) args[5] else null);
    const digest_hex = std.fmt.bytesToHex(source_result.digest, .lower);
    std.debug.print("{{\"schema\":\"s31-control-claim-trace-v1\",\"source_semantics_match\":true,\"source_nodes_mapped\":{d},\"source_qm31_rows\":{d},\"physical_certificate_sha256\":\"{s}\",\"base_root_match\":true,\"interaction_root_match\":true,\"all_component_claims_match\":true,\"producer_counts\":[{d},{d},{d},{d}]}}\n", .{ ir.source_map.len, source_result.source_rows, &digest_hex, counts[0], counts[1], counts[2], counts[3] });
}
