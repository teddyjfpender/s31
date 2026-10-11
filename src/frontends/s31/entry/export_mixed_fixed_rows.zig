//! Build entry for tools/formal/export_mixed_fixed_rows.zig.
const selected = @import("src/tools/formal/export_mixed_fixed_rows.zig");

pub fn main() !void {
    try selected.main();
}
