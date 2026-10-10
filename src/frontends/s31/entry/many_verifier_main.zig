//! Build entry for runtime/many_verifier_main.zig.
const selected = @import("src/runtime/many_verifier_main.zig");

pub fn main() !void {
    try selected.main();
}
