//! Execute a source/descriptor corpus through the production relation parser.
//! Each rejected case must reach the record ABI validator, not merely fail an
//! unrelated relation or JSON precondition.
const std = @import("std");
const s31 = @import("stwo_s31_prototype");

const Case = struct {
    label: []const u8,
    source: []const u8,
    expected_valid: bool,
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
    const raw = try std.fs.cwd().readFileAlloc(allocator, args[1], 4 << 20);
    defer allocator.free(raw);
    var parsed = try std.json.parseFromSlice(Corpus, allocator, raw, .{
        .duplicate_field_behavior = .@"error",
        .ignore_unknown_fields = false,
    });
    defer parsed.deinit();
    if (!std.mem.eql(u8, parsed.value.schema, "s31-record-descriptor-native-corpus-v2") or
        parsed.value.cases.len == 0) return error.InvalidCorpus;
    var accepted: usize = 0;
    var rejected: usize = 0;
    for (parsed.value.cases) |case| {
        var program = s31.relation.parseProgram(allocator, case.source) catch |err| {
            if (case.expected_valid or err != error.InvalidRecordAbi) {
                std.debug.print("descriptor case {s}: unexpected rejection {s}\n", .{
                    case.label, @errorName(err),
                });
                return error.CorpusMismatch;
            }
            rejected += 1;
            continue;
        };
        defer program.deinit();
        if (!case.expected_valid) {
            std.debug.print("descriptor case {s}: malformed descriptor accepted\n", .{case.label});
            return error.CorpusMismatch;
        }
        accepted += 1;
    }
    var buffer: [128]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.print("{{\"accepted\":{d},\"rejected\":{d}}}\n", .{ accepted, rejected });
    try stdout.interface.flush();
}
