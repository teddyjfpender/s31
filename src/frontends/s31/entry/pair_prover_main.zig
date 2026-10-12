//! Build entry for runtime/pair_prover_main.zig.
const selected = @import("src/runtime/pair_prover_main.zig");

pub fn main() !void {
    try selected.main();
}
