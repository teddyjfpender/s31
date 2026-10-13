//! Finite source-to-value-carrying-circuit audit for the Lean structural M31
//! fragment. The Python caller obtains exact source/relation/assignment bytes
//! from its compiler and Lean gate; expected node words are independently
//! calculated from the handwritten source equations. This is an executable
//! differential check, not a general compiler theorem or proof verifier.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const s31 = @import("stwo_s31_prototype");

const QM31 = core.fields.qm31.QM31;

const Node = struct {
    id: u32,
    name: ?[]const u8 = null,
    canonical_id: ?u32 = null,
    words: []u32,
    op: ?[]const u8 = null,
    lhs: ?u32 = null,
    rhs: ?u32 = null,
    constant: ?u32 = null,
};
const Case = struct {
    label: []const u8,
    relation: []const u8,
    assignment: []const u8,
    expected_inputs: ?[]Node = null,
    expected_nodes: []Node,
    expected_output_source_id: ?u32 = null,
    expected_valid: bool,
    expected_circuit_valid: bool,
    expected_public_match: bool,
};
const Corpus = struct { schema: []const u8, cases: []Case };

fn fail(label: []const u8, reason: []const u8) error{CorpusMismatch} {
    std.debug.print("structural witness {s}: {s}\n", .{ label, reason });
    return error.CorpusMismatch;
}

fn laneWords(value: QM31) [4]u32 {
    return .{
        value.c0.a.toU32(), value.c0.b.toU32(),
        value.c1.a.toU32(), value.c1.b.toU32(),
    };
}

fn checkNodeWords(label: []const u8, values: []const QM31, expected: Node, address: u32) !void {
    if (address >= values.len or expected.words.len == 0 or expected.words.len > 4)
        return fail(label, "source node address or lane count invalid");
    const actual = laneWords(values[address]);
    if (!std.mem.eql(u32, actual[0..expected.words.len], expected.words))
        return fail(label, "compiled node value differs from source equation");
}

fn checkGate(
    label: []const u8,
    ctx: *const circuit.builder.Context(QM31),
    maps: []const s31.relation_compiler.NodeWires,
    source_map: []const s31.canonical.Source,
    canonical_nodes: []const s31.canonical.Node,
    expected: Node,
    output: u32,
) !void {
    const op = expected.op orelse return;
    const lhs_id = expected.lhs orelse return fail(label, "source node lacks lhs");
    if (lhs_id >= source_map.len or source_map[lhs_id].id >= maps.len or
        maps[source_map[lhs_id].id].wires.len != 1)
        return fail(label, "source lhs address invalid");
    const lhs = maps[source_map[lhs_id].id].wires[0];
    const is_add = std.mem.eql(u8, op, "add") or std.mem.eql(u8, op, "add_const");
    const is_sub = std.mem.eql(u8, op, "sub");
    const is_mul = std.mem.eql(u8, op, "mul") or std.mem.eql(u8, op, "mul_const");
    if (!is_add and !is_sub and !is_mul) return fail(label, "unsupported source opcode");
    const gates = if (is_add) ctx.circuit.add.items else if (is_sub) ctx.circuit.sub.items else ctx.circuit.pointwise_mul.items;
    const constant_mode = std.mem.endsWith(u8, op, "_const");
    const rhs = if (constant_mode) null else blk: {
        const rhs_id = expected.rhs orelse return fail(label, "source node lacks rhs");
        if (rhs_id >= source_map.len or source_map[rhs_id].id >= maps.len or
            maps[source_map[rhs_id].id].wires.len != 1)
            return fail(label, "source rhs address invalid");
        break :blk maps[source_map[rhs_id].id].wires[0];
    };
    if (constant_mode == (expected.constant == null) or (!constant_mode and expected.rhs == null) or
        (constant_mode and expected.rhs != null))
        return fail(label, "source gate metadata inconsistent");
    const canonical_id = source_map[expected.id].id;
    if (canonical_id >= canonical_nodes.len) return fail(label, "canonical node ID invalid");
    if (canonical_nodes[canonical_id].tag == .constant) {
        const lanes = laneWords(ctx.values()[output]);
        for (lanes) |limb| if (limb != canonical_nodes[canonical_id].constant.?)
            return fail(label, "folded native constant differs from source");
        return;
    }
    if (constant_mode and output == lhs and
        ((is_add and expected.constant.? == 0) or
            (is_mul and expected.constant.? == 1))) return;
    if (constant_mode and is_mul and expected.constant.? == 0 and
        ctx.values()[output].isZero()) return;
    var found = false;
    for (gates) |gate| {
        if (gate.out != output) continue;
        const ordered = gate.in0 == lhs and
            (if (constant_mode) true else gate.in1 == rhs.?);
        const swapped = !is_sub and gate.in1 == lhs and
            (if (constant_mode) true else gate.in0 == rhs.?);
        if (!ordered and !swapped) continue;
        if (constant_mode) {
            const address = if (ordered) gate.in1 else gate.in0;
            if (address >= ctx.values().len) return fail(label, "source constant address invalid");
            const limbs = laneWords(ctx.values()[address]);
            for (limbs) |limb| if (limb != expected.constant.?)
                return fail(label, "native gate constant differs from source");
        }
        found = true;
        break;
    }
    if (!found) return fail(label, "native gate operation or operands differ from source");
}

fn checkCase(allocator: std.mem.Allocator, item: Case) !void {
    var program = try s31.relation.parseProgram(allocator, item.relation);
    defer program.deinit();
    var ir = try s31.canonical.build(allocator, program.value);
    defer ir.deinit();
    var assignment = try s31.relation.parseAssignment(allocator, item.assignment);
    defer assignment.deinit();
    const evaluated = s31.relation.evaluate(allocator, program.value, assignment.value);
    if (!item.expected_valid) {
        if (evaluated) |_| return fail(item.label, "wrong claim accepted by evaluator") else |_| {}
    } else {
        _ = evaluated catch return fail(item.label, "honest assignment rejected by evaluator");
    }

    var topology_maps = s31.relation_compiler.Maps{ .capture_node_wires = true };
    defer topology_maps.deinit(allocator);
    var topology = try s31.relation_compiler.compileDirectWithSpans(circuit.builder.NoValue, allocator, program.value, null, &topology_maps, false);
    defer topology.deinit();
    var maps = s31.relation_compiler.Maps{ .capture_node_wires = true };
    defer maps.deinit(allocator);
    var witness = try s31.relation_compiler.compileDirectWithSpans(QM31, allocator, program.value, assignment.value, &maps, false);
    defer witness.deinit();
    if (witness.circuit.n_vars != topology.circuit.n_vars or
        witness.circuit.nQm31OpsRows() != topology.circuit.nQm31OpsRows() or
        maps.node_wires.items.len != ir.nodes.len or
        topology_maps.node_wires.items.len != maps.node_wires.items.len)
    {
        std.debug.print("n_vars {d}/{d}; rows {d}/{d}; node wires {d}/{d}/{d}\n", .{
            witness.circuit.n_vars,         topology.circuit.n_vars,
            witness.circuit.nQm31OpsRows(), topology.circuit.nQm31OpsRows(),
            maps.node_wires.items.len,      topology_maps.node_wires.items.len,
            item.expected_nodes.len,
        });
        return fail(item.label, "compiled topology or node count differs");
    }
    if (ir.source_map.len != program.value.inputs.len + item.expected_nodes.len)
        return fail(item.label, "canonical source map length differs");
    if (item.expected_output_source_id) |source_id| {
        if (source_id >= ir.source_map.len or ir.public_outputs.len != 1 or
            ir.public_outputs[0].id != ir.source_map[source_id].id or
            !std.mem.eql(u8, ir.public_outputs[0].name, ir.source_map[source_id].name))
            return fail(item.label, "source-selected public output differs");
    }
    if (item.expected_inputs) |inputs| {
        if (inputs.len != program.value.inputs.len) return fail(item.label, "source input count differs");
        for (inputs, 0..) |expected, source_id| {
            const mapped = ir.source_map[source_id];
            if (mapped.id >= maps.node_wires.items.len) return fail(item.label, "source input map invalid");
            const actual = maps.node_wires.items[mapped.id];
            const fixed = topology_maps.node_wires.items[mapped.id];
            if (expected.id != source_id or actual.id != mapped.id or fixed.id != mapped.id or
                (expected.canonical_id != null and expected.canonical_id.? != mapped.id) or
                (expected.name != null and !std.mem.eql(u8, expected.name.?, mapped.name)) or
                actual.wires.len != 1 or fixed.wires.len != 1 or
                actual.wires[0] != fixed.wires[0])
                return fail(item.label, "source input address differs");
            try checkNodeWords(item.label, witness.values(), expected, actual.wires[0]);
        }
    }
    for (item.expected_nodes, 0..) |expected, node_index| {
        const source_id = program.value.inputs.len + node_index;
        const mapped = ir.source_map[source_id];
        if (mapped.id >= maps.node_wires.items.len) return fail(item.label, "source node map invalid");
        const actual = maps.node_wires.items[mapped.id];
        const fixed = topology_maps.node_wires.items[mapped.id];
        if (expected.id != source_id or actual.id != mapped.id or fixed.id != mapped.id or
            (expected.canonical_id != null and expected.canonical_id.? != mapped.id) or
            (expected.name != null and !std.mem.eql(u8, expected.name.?, mapped.name)) or
            actual.wires.len != 1 or fixed.wires.len != 1 or
            fixed.wires[0] != actual.wires[0] or expected.words.len == 0 or
            expected.words.len > 4 or actual.wires[0] >= witness.values().len)
            return fail(item.label, "source node address differs");
        try checkNodeWords(item.label, witness.values(), expected, actual.wires[0]);
        try checkGate(item.label, &witness, maps.node_wires.items, ir.source_map, ir.nodes, expected, actual.wires[0]);
    }
    if ((try witness.isCircuitValid()) != item.expected_circuit_valid)
        return fail(item.label, "value carrying circuit gate validity differs");
    const claimed = try s31.relation.claimedWords(allocator, program.value, assignment.value);
    if (witness.circuit.output.items.len != 9)
        return fail(item.label, "public circuit output width differs");
    var matches = true;
    for (claimed, 0..) |word, index| {
        const address = witness.circuit.output.items[index + 1];
        if (address >= witness.values().len) return fail(item.label, "public circuit output address invalid");
        const actual = try witness.values()[address].tryIntoM31();
        if (actual.toU32() != word) matches = false;
    }
    if (matches != item.expected_public_match or
        item.expected_valid != (item.expected_circuit_valid and item.expected_public_match))
        return fail(item.label, "compiled public words are not bound to claimed words");
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 2) return error.ExpectedCorpusPath;
    const bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(bytes);
    var parsed = try std.json.parseFromSlice(Corpus, allocator, bytes, .{
        .duplicate_field_behavior = .@"error",
        .ignore_unknown_fields = false,
    });
    defer parsed.deinit();
    if (!std.mem.eql(u8, parsed.value.schema, "s31-structural-m31-native-witness-corpus-v1") or
        parsed.value.cases.len == 0 or parsed.value.cases.len > 32)
        return error.InvalidCorpus;
    for (parsed.value.cases) |item| try checkCase(allocator, item);
    var buffer: [128]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.print("{{\"checked\":{d}}}\n", .{parsed.value.cases.len});
    try stdout.interface.flush();
}
