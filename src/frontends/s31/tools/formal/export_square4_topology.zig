//! Extract the gate chain produced by the real S31 direct compiler for the
//! normalized functional_square4 program. The Python formal gate supplies
//! the IR freshly compiled from the `.s31` source on every run.
const std = @import("std");
const circuit = @import("stwo_circuit_frontend");
const QM31 = @import("stwo_core").fields.qm31.QM31;
const s31 = @import("stwo_s31_prototype");

fn writeGates(writer: *std.Io.Writer, name: []const u8, gates: anytype) !void {
    try writer.print("def {s} : List Gate := [", .{name});
    for (gates, 0..) |gate, i| {
        if (i != 0) try writer.writeAll(", ");
        try writer.print("⟨{d}, {d}, {d}⟩", .{ gate.in0, gate.in1, gate.out });
    }
    try writer.writeAll("]\n");
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 2) return error.ExpectedNormalizedSourcePath;
    const source = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(source);
    var parsed = try s31.relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const program = parsed.value;
    if (!std.mem.eql(u8, program.name, "functional_square4") or
        program.inputs.len != 1 or program.nodes.len != 2 or
        program.assertions.len != 0 or program.public_outputs.len != 1 or
        program.inputs[0].kind != .m31 or program.inputs[0].length != 4 or
        program.inputs[0].visibility != .public or
        !std.mem.eql(u8, program.inputs[0].name, "x") or
        program.nodes[0].op != .mul or program.nodes[1].op != .mul or
        !std.mem.eql(u8, program.nodes[0].name, "_s31_i1_0") or
        !std.mem.eql(u8, program.nodes[1].name, "result") or
        !std.mem.eql(u8, program.public_outputs[0], "result"))
        return error.UnexpectedFunctionalProgram;

    var maps = s31.relation_compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try s31.relation_compiler.compileDirectWithSpans(circuit.builder.NoValue, allocator, program, null, &maps, false);
    defer ctx.deinit();
    if (maps.nodes.items.len != 3) return error.UnexpectedCanonicalNodeCount;
    const first_span = maps.nodes.items[1];
    const second_span = maps.nodes.items[2];
    if (first_span.qm31_end != first_span.qm31_start + 1 or
        second_span.qm31_end != second_span.qm31_start + 1 or
        first_span.qm31_end != second_span.qm31_start)
        return error.UnexpectedArithmeticRowSpan;
    if (ctx.circuit.pointwise_mul.items.len < 2)
        return error.MissingPointwiseGates;
    const first = ctx.circuit.pointwise_mul.items[0];
    const second = ctx.circuit.pointwise_mul.items[1];
    if (first.in0 != first.in1 or second.in0 != second.in1 or
        second.in0 != first.out)
        return error.UnexpectedSquareGateChain;
    if (ctx.circuit.mul.items.len < 3 or ctx.circuit.add.items.len < 3)
        return error.MissingInputPackingGates;
    const pack_mul = ctx.circuit.mul.items[0..3];
    const pack_add = ctx.circuit.add.items[0..3];
    if (pack_add[0].in1 != pack_mul[0].out or
        pack_add[1].in0 != pack_add[0].out or pack_add[1].in1 != pack_mul[1].out or
        pack_add[2].in0 != pack_add[1].out or pack_add[2].in1 != pack_mul[2].out or
        pack_add[2].out != first.in0 or
        maps.nodes.items[0].qm31_end != first_span.qm31_start)
        return error.UnexpectedInputPacking;
    const unit_i = ctx.constants.get(circuit.builder.context.constantKey(QM31.fromU32Unchecked(0, 1, 0, 0))) orelse return error.MissingBasis;
    const unit_u = ctx.constants.get(circuit.builder.context.constantKey(QM31.fromU32Unchecked(0, 0, 1, 0))) orelse return error.MissingBasis;
    const unit_iu = ctx.constants.get(circuit.builder.context.constantKey(QM31.fromU32Unchecked(0, 0, 0, 1))) orelse return error.MissingBasis;
    if (pack_mul[0].in0 != unit_i.idx or pack_mul[1].in0 != unit_u.idx or
        pack_mul[2].in0 != unit_iu.idx)
        return error.UnexpectedInputBasis;
    if (ctx.circuit.pointwise_mul.items.len < 6 or ctx.circuit.mul.items.len < 6 or
        ctx.circuit.add.items.len < 11)
        return error.MissingPublicBoundaryGates;
    const input_bind = ctx.circuit.add.items[3..7];
    const output_point = ctx.circuit.pointwise_mul.items[2..6];
    const output_mul = ctx.circuit.mul.items[3..6];
    const output_bind = ctx.circuit.add.items[7..11];
    const units = [4]QM31{
        QM31.fromU32Unchecked(1, 0, 0, 0),
        QM31.fromU32Unchecked(0, 1, 0, 0),
        QM31.fromU32Unchecked(0, 0, 1, 0),
        QM31.fromU32Unchecked(0, 0, 0, 1),
    };
    const input_raw = [4]u32{ pack_add[0].in0, pack_mul[0].in1, pack_mul[1].in1, pack_mul[2].in1 };
    const zero = ctx.zero().idx;
    for (0..4) |i| {
        const unit_wire = ctx.constants.get(circuit.builder.context.constantKey(units[i])) orelse return error.MissingBasis;
        if (input_bind[i].in0 != input_raw[i] or input_bind[i].in1 != zero or
            output_point[i].in0 != second.out or output_point[i].in1 != unit_wire.idx or
            output_bind[i].in1 != zero)
            return error.UnexpectedPublicBoundary;
        const unpacked = if (i == 0) output_point[i].out else blk: {
            const inverse = units[i].inv() catch unreachable;
            const inverse_wire = ctx.constants.get(circuit.builder.context.constantKey(inverse)) orelse return error.MissingBasisInverse;
            const inverse_gate = output_mul[i - 1];
            if (inverse_gate.in0 != output_point[i].out or inverse_gate.in1 != inverse_wire.idx)
                return error.UnexpectedUnpackInverse;
            break :blk inverse_gate.out;
        };
        if (output_bind[i].in0 != unpacked)
            return error.UnexpectedOutputBinding;
        // Circuit output slot 0 is the builder's reserved wire; S31's eight
        // public words follow in source order.
        if (ctx.circuit.output.items.len != 9 or
            ctx.circuit.output.items[1 + i] != input_bind[i].out or
            ctx.circuit.output.items[5 + i] != output_bind[i].out)
            return error.UnexpectedPublicOutputOrder;
    }

    var buffer: [4096]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    const writer = &stdout.interface;
    try writer.writeAll("import S31.Gadgets.Functional.TextSquare4Air\n\n" ++
        "/-! Generated by the production S31 direct circuit compiler. -/\n" ++
        "namespace S31.Functional.TextSquare4Native\n\n" ++
        "structure Gate where\n  input0 : Nat\n  input1 : Nat\n  output : Nat\n" ++
        "deriving DecidableEq, Repr, Inhabited\n\n");
    try writer.print(
        "def first : Gate := ⟨{d}, {d}, {d}⟩\n" ++
            "def second : Gate := ⟨{d}, {d}, {d}⟩\n" ++
            "def nodeRowSpans : List (Nat × Nat) := [({d}, {d}), ({d}, {d})]\n",
        .{ first.in0, first.in1, first.out, second.in0, second.in1, second.out, first_span.qm31_start, first_span.qm31_end, second_span.qm31_start, second_span.qm31_end },
    );
    try writer.print(
        "def inputWires : List Nat := [{d}, {d}, {d}, {d}]\n" ++
            "def inputBasisWires : List Nat := [{d}, {d}, {d}]\n",
        .{ pack_add[0].in0, pack_mul[0].in1, pack_mul[1].in1, pack_mul[2].in1, unit_i.idx, unit_u.idx, unit_iu.idx },
    );
    try writer.print(
        "def inputPackMul : List Gate := " ++
            "[⟨{d}, {d}, {d}⟩, ⟨{d}, {d}, {d}⟩, ⟨{d}, {d}, {d}⟩]\n",
        .{ pack_mul[0].in0, pack_mul[0].in1, pack_mul[0].out, pack_mul[1].in0, pack_mul[1].in1, pack_mul[1].out, pack_mul[2].in0, pack_mul[2].in1, pack_mul[2].out },
    );
    try writer.print(
        "def inputPackAdd : List Gate := " ++
            "[⟨{d}, {d}, {d}⟩, ⟨{d}, {d}, {d}⟩, ⟨{d}, {d}, {d}⟩]\n\n",
        .{ pack_add[0].in0, pack_add[0].in1, pack_add[0].out, pack_add[1].in0, pack_add[1].in1, pack_add[1].out, pack_add[2].in0, pack_add[2].in1, pack_add[2].out },
    );
    try writer.print("def zeroWire : Nat := {d}\n", .{zero});
    try writeGates(writer, "inputBindingAdd", input_bind);
    try writeGates(writer, "outputUnpackPoint", output_point);
    try writeGates(writer, "outputUnpackMul", output_mul);
    try writeGates(writer, "outputBindingAdd", output_bind);
    try writer.print(
        "def publicInputWires : List Nat := [{d}, {d}, {d}, {d}]\n" ++
            "def publicOutputWires : List Nat := [{d}, {d}, {d}, {d}]\n\n",
        .{ input_bind[0].out, input_bind[1].out, input_bind[2].out, input_bind[3].out, output_bind[0].out, output_bind[1].out, output_bind[2].out, output_bind[3].out },
    );
    try writer.writeAll("end S31.Functional.TextSquare4Native\n");
    try stdout.interface.flush();
}
