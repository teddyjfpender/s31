//! Build entry for runtime/mixed_boundary/mixed_prover_main.zig.
const selected = @import("src/runtime/mixed_boundary/mixed_prover_main.zig");

pub fn main() !void {
    try selected.main();
}
