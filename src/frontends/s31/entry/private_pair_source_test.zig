//! Build entry for tests/proofs/private_pair_source_test.zig.
const selected = @import("src/tests/proofs/private_pair_source_test.zig");

pub fn main() !void {
    try selected.main();
}

test {
    _ = selected;
}
