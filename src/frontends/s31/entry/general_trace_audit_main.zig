//! Build entry for the mixed general trace auditor.
const selected = @import("src/runtime/mixed_boundary/general_trace_audit_main.zig");

pub fn main() !void {
    try selected.main();
}
