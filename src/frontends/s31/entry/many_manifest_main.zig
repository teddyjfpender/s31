//! Build entry for runtime/many_manifest_main.zig.
const selected = @import("src/runtime/many_manifest_main.zig");

pub fn main() !void {
    try selected.main();
}
