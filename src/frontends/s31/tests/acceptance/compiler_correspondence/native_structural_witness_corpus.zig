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

fn equalItems(comptime T: type, left: []const T, right: []const T) bool {
    if (left.len != right.len) return false;
    for (left, right) |a, b| if (!std.meta.eql(a, b)) return false;
    return true;
}

/// Compare the entire gate graph, including the output and permutation
/// rosters. A row count alone permits a changed opcode or operand address.
fn sameCircuitGraph(a: *const circuit.builder.Circuit, b: *const circuit.builder.Circuit) bool {
    return a.n_vars == b.n_vars and
        equalItems(circuit.builder.circuit.BinaryGate, a.add.items, b.add.items) and
        equalItems(circuit.builder.circuit.BinaryGate, a.sub.items, b.sub.items) and
        equalItems(circuit.builder.circuit.BinaryGate, a.mul.items, b.mul.items) and
        equalItems(circuit.builder.circuit.BinaryGate, a.pointwise_mul.items, b.pointwise_mul.items) and
        equalItems(circuit.builder.circuit.EqGate, a.eq.items, b.eq.items) and
        equalItems(circuit.builder.circuit.TripleXorGate, a.triple_xor.items, b.triple_xor.items) and
        equalItems(circuit.builder.circuit.M31ToU32Gate, a.m31_to_u32.items, b.m31_to_u32.items) and
        equalItems(circuit.builder.circuit.BlakeGGate, a.blake_g_gate.items, b.blake_g_gate.items) and
        std.mem.eql(u32, a.permutation.ends.items, b.permutation.ends.items) and
        std.mem.eql(u32, a.permutation.inputs.items, b.permutation.inputs.items) and
        std.mem.eql(u32, a.permutation.outputs.items, b.permutation.outputs.items) and
        std.mem.eql(u32, a.output.items, b.output.items);
}

fn sameMaps(a: *const s31.relation_compiler.Maps, b: *const s31.relation_compiler.Maps) bool {
    if (!equalItems(s31.relation_compiler.Span, a.nodes.items, b.nodes.items) or
        !equalItems(s31.relation_compiler.AssertionSpan, a.assertions.items, b.assertions.items) or
        !std.meta.eql(a.finalization, b.finalization) or
        a.node_wires.items.len != b.node_wires.items.len or
        a.bindings.items.len != b.bindings.items.len) return false;
    for (a.node_wires.items, b.node_wires.items) |left, right| {
        if (left.id != right.id or !std.mem.eql(u32, left.wires, right.wires)) return false;
    }
    for (a.bindings.items, b.bindings.items) |left, right| {
        if (!std.mem.eql(u8, left.name, right.name) or
            left.word_start != right.word_start or left.word_count != right.word_count or
            left.conversion_qm31_start != right.conversion_qm31_start or
            left.conversion_qm31_end != right.conversion_qm31_end or
            left.conversion_m31_to_u32_start != right.conversion_m31_to_u32_start or
            left.conversion_m31_to_u32_end != right.conversion_m31_to_u32_end or
            left.binding_qm31_start != right.binding_qm31_start or
            left.binding_qm31_end != right.binding_qm31_end) return false;
    }
    return true;
}

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
    tamper_extra_gate_for_test: bool = false,
    tamper_changed_gate_for_test: bool = false,
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

fn isZeroConstant(nodes: []const s31.canonical.Node, id: u32) bool {
    return id < nodes.len and nodes[id].tag == .constant and nodes[id].constant.? == 0;
}

/// One canonical packed arithmetic node must own exactly its one primitive
/// gate. The only admitted zero-row arithmetic node is add with the builder's
/// literal-zero peephole; its result must alias the other operand wire.
fn checkCanonicalSpans(
    label: []const u8,
    nodes: []const s31.canonical.Node,
    maps: *const s31.relation_compiler.Maps,
) !void {
    if (maps.nodes.items.len != nodes.len or maps.node_wires.items.len != nodes.len)
        return fail(label, "canonical node span count differs");
    for (nodes, maps.nodes.items, maps.node_wires.items, 0..) |node, span, wire, id| {
        if (span.id != id or wire.id != id or wire.wires.len != 1 or
            span.qm31_end < span.qm31_start or span.eq_end < span.eq_start or
            span.m31_to_u32_end < span.m31_to_u32_start or
            span.triple_xor_end < span.triple_xor_start or span.blake_g_end < span.blake_g_start)
            return fail(label, "canonical node span malformed");
        const rows = span.qm31_end - span.qm31_start;
        switch (node.tag) {
            .input => {},
            .constant => if (rows != 0) return fail(label, "constant node emitted unexpected arithmetic gate"),
            .add, .sub, .mul, .add_const, .mul_const => {
                const zero_left = node.tag == .add and isZeroConstant(nodes, node.lhs.?);
                const zero_right = node.tag == .add and isZeroConstant(nodes, node.rhs.?);
                const expected_rows: usize = if (zero_left or zero_right) 0 else 1;
                if (rows != expected_rows or span.eq_start != span.eq_end or
                    span.m31_to_u32_start != span.m31_to_u32_end or
                    span.triple_xor_start != span.triple_xor_end or span.blake_g_start != span.blake_g_end)
                    return fail(label, "canonical arithmetic node has extra or missing gates");
                if (expected_rows == 0) {
                    const other_id = if (zero_left) node.rhs.? else node.lhs.?;
                    if (wire.wires[0] != maps.node_wires.items[other_id].wires[0])
                        return fail(label, "elided zero addition did not alias operand");
                }
            },
            else => return fail(label, "canonical node outside native structural subset"),
        }
    }
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
    if (is_add and !constant_mode and canonical_nodes[canonical_id].tag == .add) {
        const canonical = canonical_nodes[canonical_id];
        if (isZeroConstant(canonical_nodes, canonical.lhs.?) or
            isZeroConstant(canonical_nodes, canonical.rhs.?))
        {
            const other_id = if (isZeroConstant(canonical_nodes, canonical.lhs.?))
                canonical.rhs.?
            else
                canonical.lhs.?;
            if (other_id < maps.len and maps[other_id].wires.len == 1 and
                output == maps[other_id].wires[0]) return;
        }
    }
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
    // Deliberate adversarial controls for the acceptance runner. These gates
    // satisfy zero = zero, so checking only gate validity would miss them.
    if (item.tamper_extra_gate_for_test)
        try witness.circuit.add.append(allocator, .{ .in0 = 0, .in1 = 0, .out = 0 });
    if (item.tamper_changed_gate_for_test) {
        if (witness.circuit.add.items.len == 0) return fail(item.label, "no add gate to tamper");
        witness.circuit.add.items[0].in0 = 0;
    }
    if (!sameCircuitGraph(&witness.circuit, &topology.circuit) or
        !sameMaps(&maps, &topology_maps) or
        !std.mem.eql(u128, witness.constants.keys(), topology.constants.keys()) or
        !equalItems(circuit.builder.Var, witness.constantVars(), topology.constantVars()) or
        maps.node_wires.items.len != ir.nodes.len)
        return fail(item.label, "witness and witness-free gate graphs differ");
    try checkCanonicalSpans(item.label, ir.nodes, &maps);
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
