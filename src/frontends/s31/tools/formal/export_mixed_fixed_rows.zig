//! Export the actual preprocessed Qm31 columns of the pinned N1/N8 mixed
//! source family. The independent Python checker supplies the row schedule.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const binding = @import("../../runtime/bounded_compiled_binding.zig");
const family = @import("../../runtime/mixed_boundary/test_source.zig");

const M31 = core.fields.m31.M31;
const Sha256 = std.crypto.hash.sha2.Sha256;

fn pinnedSource(comptime count: usize) []const u8 {
    const original = family.forCount(count);
    const old = "\"name\":\"mixed_descriptor_matrix\"";
    const at = comptime std.mem.indexOf(u8, original, old) orelse @compileError("missing fixture name");
    return original[0..at] ++
        std.fmt.comptimePrint("\"name\":\"mixed_general_{d}\"", .{count}) ++
        original[at + old.len ..];
}

fn writeCase(writer: *std.Io.Writer, allocator: std.mem.Allocator, comptime count: usize) !void {
    const source = comptime pinnedSource(count);
    var source_hash: [32]u8 = undefined;
    Sha256.hash(source, &source_hash, .{});
    const source_hex = std.fmt.bytesToHex(source_hash, .lower);
    const expected_source = if (count == 1)
        "8c5296ef964e3be770e442cd28b66eed3051e210bdd6a97e265a4cd2c5962f75"
    else
        "08b5c20367e910261a194658bc3753038037fb85bc8f16dbc7f9191c7d1f45ff";
    if (!std.mem.eql(u8, &source_hex, expected_source)) return error.WrongPinnedSource;
    const topology = try binding.compileSourceTopology(allocator, source);
    const root_hex = std.fmt.bytesToHex(topology.fixed_root, .lower);
    const expected_root = if (count == 1)
        "761dd5a42142ab2e8327ac0ca7ad31e1375b4f27c8e752eff766d7feea37cf00"
    else
        "68d7419f5be9e6e508ba2fafe1d8b34f4289cd2294708c332f4d646c4debe4b8";
    if (!std.mem.eql(u8, &root_hex, expected_root)) return error.WrongPinnedRoot;
    var compiled = try binding.compileManyTopology(allocator, source, topology);
    defer compiled.deinit();
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&compiled.circuit);
    var plan: cpu.private_many_boundary.Plan = .{ .count = count };
    for (0..count) |id| {
        var input: [4]u32 = undefined;
        var output: [4]u32 = undefined;
        for (0..4) |lane| {
            input[lane] = @intCast(if (id == 0) 11 + lane else 23 + 10 * (id - 1) + lane);
            output[lane] = @intCast(23 + 10 * id + lane);
        }
        plan.calls[id] = .{
            .call_id = @intCast(id),
            .rounds = 16,
            .constant = M31.fromCanonical(@intCast(13 + id)),
            .input = input,
            .output = output,
        };
        if (!std.mem.eql(u32, &input, &topology.calls[id].input) or
            !std.mem.eql(u32, &output, &topology.calls[id].output))
            return error.WrongBridgeEndpoints;
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    if (!std.mem.eql(u8, &topology.fixed_root, &(try pp.preprocessedRoot(allocator, 1))))
        return error.WrongPreprocessedRoot;
    var columns: [8][]const M31 = undefined;
    for (circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, &columns) |id, *column| {
        column.* = pp.columnValues(id) orelse return error.MissingFixedColumn;
        if (column.*.len != 512) return error.WrongFixedColumnLength;
    }
    try writer.print("{{\"count\":{d},\"source_sha256\":\"{s}\",\"fixed_root\":\"{s}\",\"rows\":[", .{ count, &source_hex, &root_hex });
    for (0..512) |row| {
        if (row != 0) try writer.writeByte(',');
        try writer.writeByte('[');
        for (0..8) |col| {
            if (col != 0) try writer.writeByte(',');
            try writer.print("{d}", .{columns[col][row].toU32()});
        }
        try writer.writeByte(']');
    }
    try writer.writeAll("]}");
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    var buffer: [4096]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    const writer = &stdout.interface;
    try writer.writeAll("{\"schema\":\"s31-mixed-fixed-native-v1\",\"cases\":[");
    try writeCase(writer, allocator, 1);
    try writer.writeByte(',');
    try writeCase(writer, allocator, 8);
    try writer.writeAll("]}\n");
    try writer.flush();
}
