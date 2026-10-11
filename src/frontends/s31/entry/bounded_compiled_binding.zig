//! Focused compiled-endpoint, native-handle and experimental V4 wire tests.
test {
    _ = @import("src/runtime/bounded_compiled_binding.zig");
    _ = @import("src/runtime/many_native_package.zig");
    _ = @import("src/runtime/mixed_boundary/inspection.zig");
    _ = @import("src/runtime/mixed_boundary/descriptor.zig");
    _ = @import("src/runtime/mixed_boundary/package.zig");
    _ = @import("src/runtime/mixed_boundary/n4_package.zig");
    _ = @import("src/runtime/mixed_boundary/witness_audit.zig");
}
