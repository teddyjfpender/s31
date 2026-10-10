//! Focused compiled-endpoint, native-handle and experimental V4 wire tests.
test {
    _ = @import("src/runtime/bounded_compiled_binding.zig");
    _ = @import("src/runtime/many_native_package.zig");
}
