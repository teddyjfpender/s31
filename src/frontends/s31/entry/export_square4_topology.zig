//! Build entry for tools/formal/export_square4_topology.zig.
const selected = @import("src/tools/formal/export_square4_topology.zig");

pub fn main() !void {
    try selected.main();
}

test {
    _ = selected;
}
