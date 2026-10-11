//! Build entry for runtime/many_prover_main.zig.
const selected = @import("src/runtime/many_prover_main.zig");

pub fn main() !void {
    try selected.main();
}
