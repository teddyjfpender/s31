//! Build entry for runtime/pair_verifier_main.zig.
const selected = @import("src/runtime/pair_verifier_main.zig");

pub fn main() !void {
    try selected.main();
}
