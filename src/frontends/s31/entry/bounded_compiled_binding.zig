//! Focused compiled-endpoint, native-handle and experimental V4 wire tests.
test {
    _ = @import("src/runtime/bounded_compiled_binding.zig");
    _ = @import("src/runtime/many_native_package.zig");
    _ = @import("src/runtime/mixed_boundary/inspection.zig");
    _ = @import("src/runtime/mixed_boundary/registry.zig");
    _ = @import("src/runtime/mixed_boundary/descriptor.zig");
    _ = @import("src/runtime/mixed_boundary/registry_manifest.zig");
    _ = @import("src/runtime/mixed_boundary/package.zig");
    _ = @import("src/runtime/mixed_boundary/n4_package.zig");
    _ = @import("src/runtime/mixed_boundary/general_package.zig");
    _ = @import("src/runtime/mixed_boundary/witness_audit.zig");
    _ = @import("src/tests/proofs/mixed_boundary/trace_correspondence.zig");
    // This negative proof test needs its dedicated runner to account for the
    // verifier's expected Merkle error logs.
    if (@hasDecl(@import("root"), "s31_opening_authentication"))
        _ = @import("src/tests/proofs/mixed_boundary/opening_authentication.zig");
    _ = @import("src/tests/proofs/mixed_boundary/fixed_column_correspondence.zig");
    _ = @import("src/tests/proofs/mixed_boundary/producer_roster_correspondence.zig");
}
