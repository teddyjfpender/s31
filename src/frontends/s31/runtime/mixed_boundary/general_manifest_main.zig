//! Witness-free JSON audit view of the exact selected mixed 1..8 profile.
const std = @import("std");
const circuit = @import("stwo_circuit_frontend");
const package = @import("general_package.zig");
const mixed = @import("inspection.zig");
const registry = @import("registry.zig");
const registry_manifest = @import("registry_manifest.zig");

const SlotReport = struct {
    source_kind: mixed.SourceKind,
    registry_key: registry.Key,
    registry_id: u32,
    registry_version: u32,
    registry_role: registry.Role,
    call_id: ?u32,
    proof_index: u32,
    claimed_sum_index: u32,
    trace_log_size: u32,
    evaluation_log_size: u32,
    main_offset: u32,
    main_columns: u32,
    interaction_offset: u32,
    interaction_columns: u32,
    constraint_offset: u32,
    n_constraints: u32,
    preprocessed_indices: []const u32,
    relation_ids: []const u32,
    air_source_sha256: [64]u8,
    program_binding_sha256: [64]u8,
};

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    const check_only = args.len == 2 and std.mem.eql(u8, args[1], "--check");
    if (args.len != 1 and !check_only) return error.UnexpectedManifestInspectorArguments;
    const inspected = try package.inspectProfile(
        allocator,
        @embedFile("s31_program_source"),
        @embedFile("s31_air_programs"),
    );
    if (check_only) return;
    const schedule = &inspected.schedule;
    const generated = try registry_manifest.fromSchedule(schedule);
    if (!std.meta.eql(generated.digest, inspected.registry_manifest_sha256))
        return error.InvalidMixedRegistryManifest;
    const geometry = schedule.native_geometry.?;
    var slots: [registry.max_components]SlotReport = undefined;
    for (slots[0..schedule.slot_count], 0..) |*out, index| {
        const slot = &schedule.slots[index];
        const entry = &generated.entries[index];
        out.* = .{
            .source_kind = slot.source_kind,
            .registry_key = entry.registry_key,
            .registry_id = entry.registry_id,
            .registry_version = entry.registry_version,
            .registry_role = entry.role,
            .call_id = slot.call_id,
            .proof_index = slot.proof_index,
            .claimed_sum_index = slot.claimed_sum_index,
            .trace_log_size = slot.trace_log_size,
            .evaluation_log_size = slot.evaluation_log_size,
            .main_offset = slot.main_offset,
            .main_columns = slot.main_columns,
            .interaction_offset = slot.interaction_offset,
            .interaction_columns = slot.interaction_columns,
            .constraint_offset = slot.constraint_offset,
            .n_constraints = slot.n_constraints,
            .preprocessed_indices = entry.preprocessed_indices[0..entry.preprocessed_count],
            .relation_ids = entry.relation_ids[0..entry.relation_count],
            .air_source_sha256 = std.fmt.bytesToHex(slot.air_source_sha256, .lower),
            .program_binding_sha256 = std.fmt.bytesToHex(slot.program_binding_sha256, .lower),
        };
    }
    const report = .{
        .schema = "s31-mixed-component-inspection-general-v3",
        .profile = "experimental-direct-mixed-general",
        .source_sha256 = std.fmt.bytesToHex(schedule.source_sha256, .lower),
        .canonical_ir_sha256 = std.fmt.bytesToHex(schedule.canonical_ir_sha256, .lower),
        .v4_audit_manifest_sha256 = std.fmt.bytesToHex(schedule.source_manifest_sha256, .lower),
        .manifest_sha256 = std.fmt.bytesToHex(schedule.digest, .lower),
        .registry_manifest_version = generated.schema_version,
        .registry_version = generated.registry_version,
        .registry_manifest_sha256 = std.fmt.bytesToHex(generated.digest, .lower),
        .descriptor_sha256 = std.fmt.bytesToHex(generated.descriptor_sha256, .lower),
        .circuit_identity_sha256 = std.fmt.bytesToHex(inspected.circuit_identity_sha256, .lower),
        .fixed_root = std.fmt.bytesToHex(schedule.fixed_root, .lower),
        .call_count = schedule.call_count,
        .calls = schedule.calls[0..schedule.call_count],
        .slot_count = schedule.slot_count,
        .slots = slots[0..schedule.slot_count],
        .main_columns = schedule.main_columns,
        .interaction_columns = schedule.interaction_columns,
        .total_constraints = schedule.total_constraints,
        // Diagnostic algebraic term only; this is not total proof security.
        .conditional_lookup_budget = schedule.lookup_envelope.?,
        .tree_columns = geometry.tree_columns,
        .max_column_log_size = geometry.max_column_log_size,
        .composition_log_size = geometry.composition_log_size,
        .composition_split = geometry.composition_split,
        .pcs = geometry.pcs,
        .interaction_pow_bits = circuit.common.component_list.INTERACTION_POW_BITS,
    };
    const json = try std.json.Stringify.valueAlloc(allocator, report, .{});
    defer allocator.free(json);
    var buffer: [4096]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.writeAll(json);
    try stdout.interface.writeByte('\n');
    try stdout.interface.flush();
}
