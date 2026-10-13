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

const Node = struct { id: u32, words: []u32 };
const Case = struct {
    label: []const u8,
    relation: []const u8,
    assignment: []const u8,
    expected_nodes: []Node,
    expected_valid: bool,
    expected_circuit_valid: bool,
    expected_public_match: bool,
};
const Corpus = struct { schema: []const u8, cases: []Case };

fn fail(label: []const u8, reason: []const u8) error{CorpusMismatch} {
    std.debug.print("structural witness {s}: {s}\n", .{ label, reason });
    return error.CorpusMismatch;
}

fn checkCase(allocator: std.mem.Allocator, item: Case) !void {
    var program = try s31.relation.parseProgram(allocator, item.relation);
    defer program.deinit();
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
        maps.node_wires.items.len != program.value.inputs.len + item.expected_nodes.len or
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
    for (item.expected_nodes, maps.node_wires.items[program.value.inputs.len..], topology_maps.node_wires.items[program.value.inputs.len..]) |expected, actual, fixed| {
        if (actual.id != expected.id or fixed.id != actual.id or
            actual.wires.len != 1 or fixed.wires.len != 1 or
            fixed.wires[0] != actual.wires[0] or expected.words.len == 0 or
            expected.words.len > 4 or actual.wires[0] >= witness.values().len)
            return fail(item.label, "source node address differs");
        const value = witness.values()[actual.wires[0]];
        const lanes = [4]u32{
            value.c0.a.toU32(), value.c0.b.toU32(),
            value.c1.a.toU32(), value.c1.b.toU32(),
        };
        if (!std.mem.eql(u32, lanes[0..expected.words.len], expected.words)) {
            std.debug.print("node id {d}, wire {d}, actual {any}, expected {any}\n", .{
                actual.id, actual.wires[0], lanes, expected.words,
            });
            return fail(item.label, "compiled node value differs from source equation");
        }
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
