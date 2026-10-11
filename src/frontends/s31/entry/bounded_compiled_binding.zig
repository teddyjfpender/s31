//! Focused compiled-endpoint, native-handle and experimental V4 wire tests.
test {
    _ = @import("src/runtime/bounded_compiled_binding.zig");
    _ = @import("src/runtime/many_native_package.zig");
    _ = @import("src/runtime/experimental_mixed_admission.zig");
    _ = @import("src/runtime/mixed_boundary/package.zig");
}
