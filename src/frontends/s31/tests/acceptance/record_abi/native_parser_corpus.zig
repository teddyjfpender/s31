//! Bounded native record-statement parser oracle for compiled-source fixtures.
//! This deliberately stops before proof verification.
//! Input: {"schema":"s31-record-statement-native-corpus-v2","cases":[
//!   {"label":"name","source":"<normalized relation JSON>",
//!    "statement":"<canonical statement JSON>",
//!    "expected_words":[0,0,0,0,0,0,0,0]}
//! ]}. Set expected_words to null for a required InvalidRecordStatement.
//! An accepted case may also supply a flat `assignment` JSON string; then
//! the parsed statement, flat assignment, and evaluated relation must agree.
const std = @import("std");
const s31 = @import("stwo_s31_prototype");

const Case = struct {
    label: []const u8,
    source: []const u8,
    statement: []const u8,
    expected_words: ?[8]u32,
    assignment: ?[]const u8 = null,
};

const Corpus = struct {
    schema: []const u8,
    cases: []Case,
};

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 2) return error.ExpectedCorpusPath;
    const raw = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(raw);
    var parsed = try std.json.parseFromSlice(Corpus, allocator, raw, .{
        .duplicate_field_behavior = .@"error",
        .ignore_unknown_fields = false,
    });
    defer parsed.deinit();
    if (!std.mem.eql(u8, parsed.value.schema, "s31-record-statement-native-corpus-v2") or
        parsed.value.cases.len == 0) return error.InvalidCorpus;
    var accepted: usize = 0;
    var rejected: usize = 0;
    for (parsed.value.cases) |case| {
        var program = try s31.relation.parseProgram(allocator, case.source);
        defer program.deinit();
        const actual = s31.record_abi.claimedWords(
            allocator,
            program.value,
            case.statement,
        ) catch |err| {
            if (case.expected_words != null) {
                std.debug.print("accepted case {s} rejected: {s}\n", .{ case.label, @errorName(err) });
                return error.CorpusMismatch;
            }
            if (err != error.InvalidRecordStatement) {
                std.debug.print("malformed case {s} failed outside statement parser: {s}\n", .{
                    case.label, @errorName(err),
                });
                return error.CorpusMismatch;
            }
            rejected += 1;
            continue;
        };
        const expected = case.expected_words orelse {
            std.debug.print("malformed case {s} accepted\n", .{case.label});
            return error.CorpusMismatch;
        };
        if (!std.mem.eql(u32, &expected, &actual)) {
            std.debug.print("case {s} projected wrong words\n", .{case.label});
            return error.CorpusMismatch;
        }
        if (case.assignment) |encoded_assignment| {
            var assignment = try s31.relation.parseAssignment(allocator, encoded_assignment);
            defer assignment.deinit();
            const claimed = try s31.relation.claimedWords(allocator, program.value, assignment.value);
            if (!std.mem.eql(u32, &expected, &claimed)) {
                std.debug.print("case {s} assignment public words differ\n", .{case.label});
                return error.CorpusMismatch;
            }
            const evaluated = s31.relation.evaluate(allocator, program.value, assignment.value) catch |err| {
                std.debug.print("case {s} relation evaluation failed: {s}\n", .{ case.label, @errorName(err) });
                return error.CorpusMismatch;
            };
            if (!std.mem.eql(u32, &expected, &evaluated)) {
                std.debug.print("case {s} evaluated public words differ\n", .{case.label});
                return error.CorpusMismatch;
            }
        }
        accepted += 1;
    }
    var buffer: [128]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.print("{{\"accepted\":{d},\"rejected\":{d}}}\n", .{ accepted, rejected });
    try stdout.interface.flush();
}
