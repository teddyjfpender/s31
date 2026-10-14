//! S31's native proof format and independent host STARK verifier.
//! The verifier checks the circuit AIR directly; it does not execute the
//! recursive verifier circuit on the host.
const std = @import("std");
const core = @import("stwo_core");
const cairo = @import("stwo_cairo_frontend");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("interop_postcard");
const direct_component_preflight = @import("direct_component_preflight.zig");
const deep_capture_admission = @import("deep_capture_admission.zig");
const fri_capture_admission = @import("fri_capture_admission.zig");
const fri_merkle_admission = @import("fri_merkle_admission.zig");
const pcs_lifted_capture_admission = @import("pcs_lifted_capture_admission.zig");
const pcs_mode_binding = @import("pcs_mode_binding.zig");

const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;
const RawMC = cpu.prove.profiles.Blake2sMerkleChannel;
comptime {
    if (H != MC.MerkleHasher or H != RawMC.MerkleHasher)
        @compileError("gate channel profiles must share the committed fixed-root hasher");
}
const PerComponent = circuit.common.component_list.PerComponent;
const N_COMPONENTS = circuit.common.component_list.N_COMPONENTS;
const MAGIC = "S31NAT1\x00";
const RAW_GATE_MAGIC = "S31NAT8R";
const HEADER_LEN = MAGIC.len + 8 + N_COMPONENTS * 16;
const HYBRID_MAGIC = "S31NAT2\x00";
const HYBRID_HEADER_LEN = HYBRID_MAGIC.len + 8 + (N_COMPONENTS + 1) * 16;
const chip = cpu.repeated_step_chip;
const M31 = core.fields.m31.M31;

pub const HybridSpec = struct {
    source_digest: [32]u8,
    rounds: u32,
    constant: M31,
};

pub fn serialize(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    if (proof.chip_claimed_sum != null) return error.WrongProofProfile;
    return serializeProfile(allocator, proof, false, false);
}

pub fn serializeRawGate(allocator: std.mem.Allocator, proof: *const cpu.Root.CircuitProof) ![]u8 {
    if (proof.chip_claimed_sum != null or proof.bridge_claimed_sum != null) return error.WrongProofProfile;
    return serializeProfile(allocator, proof, false, true);
}

pub fn serializeHybrid(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    if (proof.chip_claimed_sum == null) return error.WrongProofProfile;
    return serializeProfile(allocator, proof, true, false);
}

fn serializeProfile(allocator: std.mem.Allocator, proof: anytype, hybrid: bool, raw_gate: bool) ![]u8 {
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, if (hybrid) HYBRID_MAGIC else if (raw_gate) RAW_GATE_MAGIC else MAGIC);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    for (proof.claimed_sums.toArray()) |sum| {
        for (sum.toM31Array()) |limb| {
            var encoded: [4]u8 = undefined;
            std.mem.writeInt(u32, &encoded, limb.v, .little);
            try bytes.appendSlice(allocator, &encoded);
        }
    }
    if (hybrid) {
        for (proof.chip_claimed_sum.?.toM31Array()) |limb| {
            var encoded: [4]u8 = undefined;
            std.mem.writeInt(u32, &encoded, limb.v, .little);
            try bytes.appendSlice(allocator, &encoded);
        }
    }
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

pub fn verify(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.preprocessed.ColumnLayout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    return verifyProfile(MC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);
}

pub fn verifyRawGate(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.preprocessed.ColumnLayout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    return verifyProfile(RawMC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);
}

/// Authenticate a full gate-profile proof and retain the verifier's expanded
/// Merkle/FRI openings for the recursive circuit. No prover-side aux tree is
/// needed; conversion only runs after the native verifier accepts the proof.
pub fn verifyAndCapture(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.preprocessed.ColumnLayout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
) !cpu.verifier_proof.VerifierProof {
    var converted: cpu.verifier_proof.VerifierProof = undefined;
    try verifyProfile(MC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, &converted);
    return converted;
}

pub fn verifyHybrid(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.preprocessed.ColumnLayout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    spec: HybridSpec,
) !void {
    return verifyProfile(MC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, spec, null);
}

fn verifyProfile(
    comptime Profile: type,
    allocator: std.mem.Allocator,
    layout: *const circuit.common.preprocessed.ColumnLayout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    spec: ?HybridSpec,
    converted_out: ?*cpu.verifier_proof.VerifierProof,
) !void {
    if (Profile == RawMC and (spec != null or converted_out != null))
        return error.UnsupportedRecursiveProfile;
    const hybrid = spec != null;
    const magic = if (hybrid) HYBRID_MAGIC else if (Profile == RawMC) RAW_GATE_MAGIC else MAGIC;
    const header_len = if (hybrid) HYBRID_HEADER_LEN else HEADER_LEN;
    if (raw.len < header_len or raw.len > (16 << 20) or !std.mem.eql(u8, raw[0..magic.len], magic))
        return error.InvalidNativeProof;
    const nonce = std.mem.readInt(u64, raw[magic.len..][0..8], .little);
    var sums: [N_COMPONENTS]QM31 = undefined;
    for (&sums, 0..) |*sum, index| {
        const start = magic.len + 8 + index * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, raw[start + j * 4 ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    var chip_sum = QM31.zero();
    if (hybrid) {
        const start = magic.len + 8 + N_COMPONENTS * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, raw[start + j * 4 ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;
        }
        chip_sum = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    // Decode with a hard allocation ceiling. Length prefixes in an external
    // postcard proof cannot request arbitrary amounts of host memory.
    const proof_bytes = raw[header_len..];
    try pcs_mode_binding.requireLegacyPostcard(proof_bytes);
    const decode_memory = try allocator.alloc(u8, 64 << 20);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(proof_bytes);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != proof_bytes.len or stark.commitment_scheme_proof.commitments.items.len != 4)
        return error.InvalidNativeProof;
    if (!std.meta.eql(stark.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))
        return error.InvalidProofConfig;
    const roots = stark.commitment_scheme_proof.commitments.items;
    if (!std.mem.eql(u8, &preprocessed_root, &roots[0])) return error.InvalidPreprocessedRoot;

    var outputs: [8]QM31 = undefined;
    for (public_words, &outputs) |word, *output|
        output.* = QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0);

    var channel = Profile.Channel{};
    if (spec) |item| chip.mixProfile(&channel, item.source_digest, item.rounds, item.constant);
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(H, Profile).init(allocator, pcs);
    defer scheme.deinit(allocator);
    var pp_logs: [circuit.common.preprocessed.N_PREPROCESSED_COLUMNS]u32 = undefined;
    for (layout.entries, &pp_logs) |entry, *log| log.* = entry.log_size;
    try scheme.commit(allocator, roots[0], &pp_logs, &channel);
    Profile.mixRoot(&channel, circuit_hash);
    channel.mixFelts(&outputs);

    const component_logs = try circuit.common.component_list.circuitComponentLogSizes(layout);
    const log_array = component_logs.toArray();
    const widths = circuit.witness.trace.traceWidths();
    const interaction_widths = circuit.witness.trace.interactionWidths();
    const main_logs = try logsFor(allocator, log_array, widths, if (spec) |item| try chip.validateRounds(item.rounds) else null, chip.main_width);
    defer allocator.free(main_logs);
    const interaction_logs = try logsFor(allocator, log_array, interaction_widths, if (spec) |item| try chip.validateRounds(item.rounds) else null, chip.interaction_width);
    defer allocator.free(interaction_logs);
    try scheme.commit(allocator, roots[1], main_logs, &channel);
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return error.InvalidInteractionNonce;
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    if (!(try circuit.witness.trace.lookupSum(&outputs, PerComponent(QM31).fromArray(sums), lookup.z, lookup.alpha)).isZero())
        return error.InvalidLookupSum;
    var hybrid_sums: [N_COMPONENTS + 1]QM31 = undefined;
    @memcpy(hybrid_sums[0..N_COMPONENTS], &sums);
    hybrid_sums[N_COMPONENTS] = chip_sum;
    if (spec) |item| {
        var initial: [4]M31 = undefined;
        var final: [4]M31 = undefined;
        for (0..4) |i| {
            if (public_words[i] >= core.fields.m31.Modulus or
                public_words[4 + i] >= core.fields.m31.Modulus)
                return error.InvalidPublicStatement;
            initial[i] = M31.fromCanonical(public_words[i]);
            final[i] = M31.fromCanonical(public_words[4 + i]);
        }
        if (!(try chip.endpointSum(chip_sum, .init(lookup.z, lookup.alpha), item.rounds, initial, final)).isZero())
            return error.InvalidChipLookupSum;
        core.channel.lookup_transcript.mixInteractionClaim(&channel, &hybrid_sums);
    } else core.channel.lookup_transcript.mixInteractionClaim(&channel, &sums);
    try scheme.commit(allocator, roots[2], interaction_logs, &channel);

    var bound = try cpu.air.bind(allocator, template, component_logs, layout);
    defer bound.deinit();
    const lifting_bound = pcs.trace_lifting_log_size - pcs.fri_config.log_blowup_factor + 1;
    var captured: [N_COMPONENTS]cairo.proving.air.component.Component = undefined;
    var handles: [N_COMPONENTS + 1]core.air.components.Component = undefined;
    for (bound.components, &captured, handles[0..N_COMPONENTS], sums) |*source, *runtime, *handle, claimed| {
        runtime.* = .init(allocator, source, &pp_logs, lifting_bound, lookup.z, lookup.alpha, claimed);
        handle.* = runtime.asVerifierComponent();
    }
    var chip_component: chip.Component = undefined;
    var component_count: usize = N_COMPONENTS;
    if (spec) |item| {
        var main_offset: usize = 0;
        var interaction_offset: usize = 0;
        for (widths) |width| main_offset += width;
        for (interaction_widths) |width| interaction_offset += width;
        chip_component = .{
            .log_size = try chip.validateRounds(item.rounds),
            .constant = item.constant,
            .main_offset = main_offset,
            .interaction_offset = interaction_offset,
            .elements = .init(lookup.z, lookup.alpha),
            .claimed_sum = chip_sum,
        };
        handles[N_COMPONENTS] = chip_component.asVerifierComponent();
        component_count += 1;
    }
    var capture: core.verifier.ProofCapture(H) = undefined;
    try core.verifier.verifyBorrowedExWithProofCapture(
        H,
        Profile,
        allocator,
        handles[0..component_count],
        &channel,
        &scheme,
        &stark,
        true,
        &capture,
    );
    defer capture.deinit(allocator);
    try deep_capture_admission.validate(allocator, pcs.trace_lifting_log_size, capture.queries.raw, capture.column_log_sizes, capture.sampled_points, capture.sampled_values, capture.queried_values, capture.deep_answers, capture.deep_randomness);
    try fri_capture_admission.validate(
        H,
        allocator,
        pcs.fri_config.folding(),
        capture.queries.raw,
        capture.deep_answers,
        capture.fri,
        capture.last_layer_coefficients,
    );
    try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);
    try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);
    if (converted_out) |out| {
        if (spec != null) return error.UnsupportedRecursiveProfile;
        const config = try cpu.verifier_proof.proofConfig(stark.commitment_scheme_proof.sampled_values.items[0].len, pcs);
        out.* = try cpu.verifier_proof.fromVerifiedCapture(allocator, &stark, &capture, config, &sums, nonce, 0);
    }
}

fn logsFor(
    allocator: std.mem.Allocator,
    sizes: [N_COMPONENTS]u32,
    widths: [N_COMPONENTS]usize,
    chip_log: ?u32,
    chip_width: usize,
) ![]u32 {
    var count: usize = 0;
    for (widths) |width| count += width;
    const logs = try allocator.alloc(u32, count + if (chip_log != null) chip_width else @as(usize, 0));
    var cursor: usize = 0;
    for (sizes, widths) |log, width| {
        @memset(logs[cursor..][0..width], log);
        cursor += width;
    }
    if (chip_log) |log| @memset(logs[cursor..], log);
    return logs;
}

const SPARSE_GATE_MAGIC = "S31NAT3G";
const SPARSE_CHIP_MAGIC = "S31NAT3C";

/// Experimental P05 geometry recorded only after the complete sparse native
/// verification and its capture admission checks succeed. The paired track
/// counts are requirements for a future original/own-quotient protocol, not
/// tracks tested by this production verifier. These physical counts are not
/// the S-two paper's padded batch width M.
pub const SparseP05Shape = struct {
    pub const Height = struct {
        extended_log_size: u32,
        committed_input_log_size: u32,
        source_columns: usize,
        required_original_tracks_if_paired: usize,
        required_own_quotient_tracks_if_paired: usize,
        ood_claims: usize,
        composition_columns: usize,
        root_columns: [4]usize,
        root_ood_claims: [4]usize,
    };
    pub const Column = struct {
        root_index: usize,
        column_index: usize,
        extended_log_size: u32,
        ood_claims: usize,
        first_claim_index: usize,
        proposed_original_slot_at_height: usize,
        proposed_first_own_quotient_slot_at_height: usize,
        /// Value authenticated for the first raw lifted query, in the same
        /// tree/column order as `capture.queried_values`.
        source_value_at_first_raw_query: u32,
    };
    pub const Claim = struct {
        root_index: usize,
        column_index: usize,
        sample_index: usize,
        extended_log_size: u32,
        point_x_limbs: [4]u32,
        point_y_limbs: [4]u32,
        value_limbs: [4]u32,
    };

    root_columns: [4]usize = .{ 0, 0, 0, 0 },
    root_ood_claims: [4]usize = .{ 0, 0, 0, 0 },
    composition_log_degree_bound: u32 = 0,
    composition_log_split: u32 = 0,
    height_count: usize = 0,
    heights: [32]Height = undefined,
    column_count: usize = 0,
    columns: [128]Column = undefined,
    claim_count: usize = 0,
    claims: [256]Claim = undefined,
    oods_seed_limbs: [4]u32 = undefined,
    trace_lifting_log_size: u32 = 0,
    first_raw_lifted_query_position: usize = 0,
    oods_point_x_limbs: [4]u32 = undefined,
    oods_point_y_limbs: [4]u32 = undefined,
};

fn p05Limbs(value: QM31) [4]u32 {
    const words = value.toM31Array();
    return .{ words[0].v, words[1].v, words[2].v, words[3].v };
}

pub fn serializeSparse(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof, has_chip: bool) ![]u8 {
    if ((proof.chip_claimed_sum != null) != has_chip) return error.WrongProofProfile;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, if (has_chip) SPARSE_CHIP_MAGIC else SPARSE_GATE_MAGIC);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    const all_sums = proof.claimed_sums.toArray();
    for (circuit.common.sparse_arithmetic.active_component_indices) |index|
        try appendSum(allocator, &bytes, all_sums[index]);
    if (has_chip) try appendSum(allocator, &bytes, proof.chip_claimed_sum.?);
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

fn appendSum(allocator: std.mem.Allocator, bytes: *std.ArrayList(u8), sum: QM31) !void {
    for (sum.toM31Array()) |limb| {
        var encoded: [4]u8 = undefined;
        std.mem.writeInt(u32, &encoded, limb.v, .little);
        try bytes.appendSlice(allocator, &encoded);
    }
}

pub fn verifySparse(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.sparse_arithmetic.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
    chip_spec: ?HybridSpec,
    p05_shape_out: ?*SparseP05Shape,
) !void {
    const has_chip = chip_spec != null;
    const magic = if (has_chip) SPARSE_CHIP_MAGIC else SPARSE_GATE_MAGIC;
    const sum_count: usize = if (has_chip) 4 else 3;
    const header_len = magic.len + 8 + sum_count * 16;
    if (raw.len < header_len or raw.len > (16 << 20) or !std.mem.eql(u8, raw[0..magic.len], magic))
        return error.InvalidNativeProof;
    const nonce = std.mem.readInt(u64, raw[magic.len..][0..8], .little);
    var sums: [4]QM31 = undefined;
    for (sums[0..sum_count], 0..) |*sum, index| {
        const start = magic.len + 8 + index * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, raw[start + 4 * j ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    try pcs_mode_binding.requireLegacyPostcard(raw[header_len..]);
    const decode_memory = try allocator.alloc(u8, 64 << 20);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(raw[header_len..]);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != raw.len - header_len or
        stark.commitment_scheme_proof.commitments.items.len != 4)
        return error.InvalidNativeProof;
    if (!std.meta.eql(stark.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))
        return error.InvalidProofConfig;
    const roots = stark.commitment_scheme_proof.commitments.items;
    if (!std.mem.eql(u8, &preprocessed_root, &roots[0]))
        return error.InvalidPreprocessedRoot;

    var outputs: [8]QM31 = undefined;
    for (public_words, &outputs) |word, *output|
        output.* = QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0);
    var initial: [4]M31 = undefined;
    var final: [4]M31 = undefined;
    if (has_chip) for (0..4) |i| {
        if (public_words[i] >= core.fields.m31.Modulus or
            public_words[4 + i] >= core.fields.m31.Modulus)
            return error.InvalidPublicStatement;
        initial[i] = M31.fromCanonical(public_words[i]);
        final[i] = M31.fromCanonical(public_words[4 + i]);
    };
    const chip_request: ?cpu.prove.ChipRequest = if (chip_spec) |item| .{
        .source_digest = source_digest,
        .rounds = item.rounds,
        .constant = item.constant,
        .initial = initial,
        .final = final,
    } else null;
    const logs = [3]u32{
        layout.logSize("qm31_ops_in0_address") orelse return error.InvalidSparseLayout,
        layout.logSize("m31_to_u32_input_addr") orelse return error.InvalidSparseLayout,
        16,
    };
    const expected_hash = cpu.sparse_arithmetic.identityHash(
        source_digest,
        preprocessed_root,
        logs,
        pcs.fri_config.log_blowup_factor,
        chip_request,
    );
    if (!std.mem.eql(u8, &expected_hash, &circuit_hash))
        return error.InvalidCircuitHash;
    var channel = MC.Channel{};
    cpu.sparse_arithmetic.mixProfile(&channel, .{
        .source_digest = source_digest,
        .chip_request = chip_request,
    });
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(H, MC).init(allocator, pcs);
    defer scheme.deinit(allocator);
    var pp_logs: [circuit.common.sparse_arithmetic.N_COLUMNS]u32 = undefined;
    for (layout.entries, &pp_logs) |entry, *log| log.* = entry.log_size;
    try scheme.commit(allocator, roots[0], &pp_logs, &channel);
    MC.mixRoot(&channel, circuit_hash);
    channel.mixFelts(&outputs);
    const chip_log: ?u32 = if (chip_spec) |item| try chip.validateRounds(item.rounds) else null;
    const main_logs = try sparseLogs(allocator, logs, .{ 12, 4, 1 }, chip_log, chip.main_width);
    defer allocator.free(main_logs);
    const interaction_logs = try sparseLogs(allocator, logs, .{ 8, 12, 4 }, chip_log, chip.interaction_width);
    defer allocator.free(interaction_logs);
    try scheme.commit(allocator, roots[1], main_logs, &channel);
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return error.InvalidInteractionNonce;
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    if (!(try circuit.witness.sparse_arithmetic.lookupSum(&outputs, .{ sums[0], sums[1], sums[2] }, lookup.z, lookup.alpha)).isZero())
        return error.InvalidLookupSum;
    if (chip_spec) |item| if (!(try chip.endpointSum(
        sums[3],
        .init(lookup.z, lookup.alpha),
        item.rounds,
        initial,
        final,
    )).isZero()) return error.InvalidChipLookupSum;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..sum_count]);
    try scheme.commit(allocator, roots[2], interaction_logs, &channel);
    var bound = try cpu.air.bindSparseArithmetic(allocator, template, logs, layout);
    defer bound.deinit();
    const lifting_bound = pcs.trace_lifting_log_size - pcs.fri_config.log_blowup_factor + 1;
    var captured: [3]cairo.proving.air.component.Component = undefined;
    var handles: [4]core.air.components.Component = undefined;
    for (bound.components, &captured, handles[0..3], sums[0..3]) |*source, *runtime, *handle, claimed| {
        runtime.* = .init(allocator, source, &pp_logs, lifting_bound, lookup.z, lookup.alpha, claimed);
        handle.* = runtime.asVerifierComponent();
    }
    var chip_component: chip.Component = undefined;
    var component_count: usize = 3;
    if (chip_spec) |item| {
        chip_component = .{
            .log_size = try chip.validateRounds(item.rounds),
            .constant = item.constant,
            .main_offset = circuit.witness.sparse_arithmetic.main_width,
            .interaction_offset = circuit.witness.sparse_arithmetic.interaction_width,
            .elements = .init(lookup.z, lookup.alpha),
            .claimed_sum = sums[3],
        };
        handles[3] = chip_component.asVerifierComponent();
        component_count = 4;
    }
    var capture: core.verifier.ProofCapture(H) = undefined;
    try core.verifier.verifyBorrowedExWithProofCapture(
        H,
        MC,
        allocator,
        handles[0..component_count],
        &channel,
        &scheme,
        &stark,
        true,
        &capture,
    );
    defer capture.deinit(allocator);
    try deep_capture_admission.validate(allocator, pcs.trace_lifting_log_size, capture.queries.raw, capture.column_log_sizes, capture.sampled_points, capture.sampled_values, capture.queried_values, capture.deep_answers, capture.deep_randomness);
    try fri_capture_admission.validate(
        H,
        allocator,
        pcs.fri_config.folding(),
        capture.queries.raw,
        capture.deep_answers,
        capture.fri,
        capture.last_layer_coefficients,
    );
    try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);
    try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);
    if (p05_shape_out) |out| {
        if (capture.queries.raw.len == 0) return error.InvalidP05SparseShape;
        const components = core.air.components.Components{
            .components = handles[0..component_count],
            .n_preprocessed_columns = pp_logs.len,
        };
        const split = try components.compositionLogSplit();
        const composition_log = components.compositionLogDegreeBound();
        const component_mask_log = core.verifier_types.compositionMaskLogSize(
            composition_log,
            split,
        ) orelse return error.InvalidP05SparseShape;
        const lifted_mask_log = std.math.sub(u32, pcs.trace_lifting_log_size, pcs.fri_config.log_blowup_factor) catch return error.InvalidP05SparseShape;
        const oods_point = core.circle.secureFieldPointFromRandomSeedChecked(
            capture.oods_seed,
        ) catch return error.InvalidP05SparseShape;
        var expected_masks = try components.maskPoints(
            allocator,
            oods_point,
            @max(component_mask_log, lifted_mask_log),
            true,
        );
        defer expected_masks.deinitDeep(allocator);
        if (expected_masks.items.len != 3) return error.InvalidP05SparseShape;
        out.* = .{
            .composition_log_degree_bound = composition_log,
            .composition_log_split = split,
            .oods_seed_limbs = p05Limbs(capture.oods_seed),
            .trace_lifting_log_size = pcs.trace_lifting_log_size,
            .first_raw_lifted_query_position = capture.queries.raw[0],
            .oods_point_x_limbs = p05Limbs(oods_point.x),
            .oods_point_y_limbs = p05Limbs(oods_point.y),
        };
        const accepted_values = stark.commitment_scheme_proof.sampled_values.items;
        if (capture.column_log_sizes.len != 4 or capture.sampled_points.len != 4 or
            accepted_values.len != 4)
            return error.InvalidP05SparseShape;
        var queried_column_at: usize = 0;
        for (capture.column_log_sizes, capture.sampled_points, accepted_values, 0..) |logs_by_tree, points_by_tree, values_by_tree, tree| {
            if (logs_by_tree.len != points_by_tree.len or
                logs_by_tree.len != values_by_tree.len or
                (tree < 3 and expected_masks.items[tree].len != logs_by_tree.len))
                return error.InvalidP05SparseShape;
            out.root_columns[tree] = logs_by_tree.len;
            for (logs_by_tree, points_by_tree, values_by_tree, 0..) |log_size, points, values, column| {
                const queried_value_offset = std.math.mul(usize, queried_column_at, capture.queries.raw.len) catch
                    return error.InvalidP05SparseShape;
                if (queried_value_offset >= capture.queried_values.len) return error.InvalidP05SparseShape;
                const source_value = capture.queried_values[queried_value_offset];
                queried_column_at += 1;
                if (log_size >= out.heights.len or points.len == 0 or
                    points.len != values.len)
                    return error.InvalidP05SparseShape;
                const want: []const core.circle.CirclePointQM31 = if (tree < 3)
                    expected_masks.items[tree][column]
                else
                    &[_]core.circle.CirclePointQM31{oods_point};
                if (want.len != points.len) return error.InvalidP05SparseShape;
                for (points, values, want, 0..) |point, value, expected, sample| {
                    if (!point.eql(expected) or out.claim_count == out.claims.len or
                        out.claim_count >= capture.sampled_values.len or
                        !value.eql(capture.sampled_values[out.claim_count]))
                        return error.InvalidP05SparseShape;
                    out.claims[out.claim_count] = .{
                        .root_index = tree,
                        .column_index = column,
                        .sample_index = sample,
                        .extended_log_size = log_size,
                        .point_x_limbs = p05Limbs(point.x),
                        .point_y_limbs = p05Limbs(point.y),
                        .value_limbs = p05Limbs(value),
                    };
                    out.claim_count += 1;
                }
                const input_log = std.math.sub(u32, log_size, pcs.fri_config.log_blowup_factor) catch
                    return error.InvalidP05SparseShape;
                var at: usize = 0;
                while (at < out.height_count and out.heights[at].extended_log_size != log_size) : (at += 1) {}
                if (at == out.height_count) {
                    out.heights[at] = .{
                        .extended_log_size = log_size,
                        .committed_input_log_size = input_log,
                        .source_columns = 0,
                        .required_original_tracks_if_paired = 0,
                        .required_own_quotient_tracks_if_paired = 0,
                        .ood_claims = 0,
                        .composition_columns = 0,
                        .root_columns = .{ 0, 0, 0, 0 },
                        .root_ood_claims = .{ 0, 0, 0, 0 },
                    };
                    out.height_count += 1;
                }
                const height = &out.heights[at];
                if (height.committed_input_log_size != input_log) return error.InvalidP05SparseShape;
                if (out.column_count == out.columns.len) return error.InvalidP05SparseShape;
                out.columns[out.column_count] = .{
                    .root_index = tree,
                    .column_index = column,
                    .extended_log_size = log_size,
                    .ood_claims = points.len,
                    .first_claim_index = out.claim_count - points.len,
                    .proposed_original_slot_at_height = height.required_original_tracks_if_paired,
                    .proposed_first_own_quotient_slot_at_height = height.required_own_quotient_tracks_if_paired,
                    .source_value_at_first_raw_query = source_value.v,
                };
                out.column_count += 1;
                height.source_columns += 1;
                height.required_original_tracks_if_paired += 1;
                height.required_own_quotient_tracks_if_paired += points.len;
                height.ood_claims += points.len;
                if (tree == 3) height.composition_columns += 1;
                height.root_columns[tree] += 1;
                height.root_ood_claims[tree] += points.len;
                out.root_ood_claims[tree] += points.len;
            }
        }
        if (out.claim_count != capture.sampled_values.len)
            return error.InvalidP05SparseShape;
        const expected_queried_values = std.math.mul(usize, queried_column_at, capture.queries.raw.len) catch
            return error.InvalidP05SparseShape;
        if (expected_queried_values != capture.queried_values.len) return error.InvalidP05SparseShape;
        std.sort.heap(SparseP05Shape.Height, out.heights[0..out.height_count], {}, struct {
            fn less(_: void, a: SparseP05Shape.Height, b: SparseP05Shape.Height) bool {
                return a.extended_log_size > b.extended_log_size;
            }
        }.less);
    }
}

const SPARSE_WIDE_MAGIC = "S31NAT5W";

pub fn serializeSparseWide(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    if (proof.chip_claimed_sum != null) return error.WrongProofProfile;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, SPARSE_WIDE_MAGIC);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    const all_sums = proof.claimed_sums.toArray();
    for (circuit.common.sparse_wide.active_component_indices) |index|
        try appendSum(allocator, &bytes, all_sums[index]);
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

pub fn verifySparseWide(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.sparse_wide.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
) !void {
    return verifySparseWideInternal(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, null);
}

/// Convert only after authenticating the entire native STARK, including its
/// sparse-wide profile prefix, lookup closure, Merkle openings, and FRI.
pub fn verifySparseWideAndCapture(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.sparse_wide.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
) !cpu.verifier_proof.VerifierProof {
    var converted: cpu.verifier_proof.VerifierProof = undefined;
    try verifySparseWideInternal(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, &converted);
    return converted;
}

fn verifySparseWideInternal(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.sparse_wide.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
    converted_out: ?*cpu.verifier_proof.VerifierProof,
) !void {
    const header_len = SPARSE_WIDE_MAGIC.len + 8 + 4 * 16;
    if (raw.len < header_len or raw.len > (16 << 20) or !std.mem.eql(u8, raw[0..SPARSE_WIDE_MAGIC.len], SPARSE_WIDE_MAGIC))
        return error.InvalidNativeProof;
    const nonce = std.mem.readInt(u64, raw[SPARSE_WIDE_MAGIC.len..][0..8], .little);
    var sums: [4]QM31 = undefined;
    for (&sums, 0..) |*sum, index| {
        const start = SPARSE_WIDE_MAGIC.len + 8 + index * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, raw[start + 4 * j ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    try pcs_mode_binding.requireLegacyPostcard(raw[header_len..]);
    const decode_memory = try allocator.alloc(u8, 64 << 20);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(raw[header_len..]);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != raw.len - header_len or stark.commitment_scheme_proof.commitments.items.len != 4)
        return error.InvalidNativeProof;
    if (!std.meta.eql(stark.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))
        return error.InvalidProofConfig;
    const roots = stark.commitment_scheme_proof.commitments.items;
    if (!std.mem.eql(u8, &preprocessed_root, &roots[0])) return error.InvalidPreprocessedRoot;

    var outputs: [8]QM31 = undefined;
    for (public_words, &outputs) |word, *output|
        output.* = QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0);
    const logs = [4]u32{
        layout.logSize("eq_in0_address") orelse return error.InvalidSparseLayout,
        layout.logSize("qm31_ops_in0_address") orelse return error.InvalidSparseLayout,
        layout.logSize("m31_to_u32_input_addr") orelse return error.InvalidSparseLayout,
        16,
    };
    const expected_hash = cpu.sparse_wide.identityHash(source_digest, preprocessed_root, logs, pcs.fri_config.log_blowup_factor);
    if (!std.mem.eql(u8, &expected_hash, &circuit_hash)) return error.InvalidCircuitHash;
    var channel = MC.Channel{};
    cpu.sparse_wide.mixProfile(&channel, .{ .source_digest = source_digest });
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(H, MC).init(allocator, pcs);
    defer scheme.deinit(allocator);
    var pp_logs: [circuit.common.sparse_wide.N_COLUMNS]u32 = undefined;
    for (layout.entries, &pp_logs) |entry, *log| log.* = entry.log_size;
    try scheme.commit(allocator, roots[0], &pp_logs, &channel);
    MC.mixRoot(&channel, circuit_hash);
    channel.mixFelts(&outputs);
    const main_logs = try sparseLogs(allocator, logs, .{ 4, 12, 4, 1 }, null, 0);
    defer allocator.free(main_logs);
    const interaction_logs = try sparseLogs(allocator, logs, .{ 4, 8, 12, 4 }, null, 0);
    defer allocator.free(interaction_logs);
    try scheme.commit(allocator, roots[1], main_logs, &channel);
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return error.InvalidInteractionNonce;
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    if (!(try circuit.witness.sparse_wide.lookupSum(&outputs, sums, lookup.z, lookup.alpha)).isZero())
        return error.InvalidLookupSum;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, &sums);
    try scheme.commit(allocator, roots[2], interaction_logs, &channel);
    var bound = try cpu.air.bindSparseWide(allocator, template, logs, layout);
    defer bound.deinit();
    const lifting_bound = pcs.trace_lifting_log_size - pcs.fri_config.log_blowup_factor + 1;
    var captured: [4]cairo.proving.air.component.Component = undefined;
    var handles: [4]core.air.components.Component = undefined;
    for (bound.components, &captured, &handles, sums) |*source, *runtime, *handle, claimed| {
        runtime.* = .init(allocator, source, &pp_logs, lifting_bound, lookup.z, lookup.alpha, claimed);
        handle.* = runtime.asVerifierComponent();
    }
    var capture: core.verifier.ProofCapture(H) = undefined;
    try core.verifier.verifyBorrowedExWithProofCapture(H, MC, allocator, &handles, &channel, &scheme, &stark, true, &capture);
    defer capture.deinit(allocator);
    try deep_capture_admission.validate(allocator, pcs.trace_lifting_log_size, capture.queries.raw, capture.column_log_sizes, capture.sampled_points, capture.sampled_values, capture.queried_values, capture.deep_answers, capture.deep_randomness);
    try fri_capture_admission.validate(
        H,
        allocator,
        pcs.fri_config.folding(),
        capture.queries.raw,
        capture.deep_answers,
        capture.fri,
        capture.last_layer_coefficients,
    );
    try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);
    try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);
    if (converted_out) |out| {
        const trace_log = std.math.sub(u32, pcs.trace_lifting_log_size, pcs.fri_config.log_blowup_factor) catch
            return error.InvalidProofConfig;
        const config: @import("stwo_circuit_recursion_wire").circuit_serialize.ProofConfig = .{
            .n_preprocessed_columns = layout.entries.len,
            .component_shapes = &circuit.statements.sparse_wide_statement.shapes,
            .log_trace_size = trace_log,
            .fri = pcs.fri_config,
        };
        out.* = try cpu.verifier_proof.fromVerifiedCapture(allocator, &stark, &capture, config, &sums, nonce, 0);
    }
}

const DIRECT_GATE_MAGIC = "S31NAT4G";
const DIRECT_CHIP_MAGIC = "S31NAT4C";
const DIRECT_PRIVATE_MAGIC = "S31NAT5P";
const DIRECT_CHIP_BOUND_MAGIC = "S31NAT6C";
const DIRECT_PRIVATE_BOUND_MAGIC = "S31NAT6P";
const DIRECT_GATE_BOUND_MAGIC = "S31NAT7G";

pub fn serializeDirect(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof, has_chip: bool) ![]u8 {
    return serializeDirectVersion(allocator, proof, has_chip, false);
}

pub fn serializeDirectBound(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    return serializeDirectVersion(allocator, proof, true, true);
}

pub fn serializeDirectGateBound(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    return serializeDirectVersion(allocator, proof, false, true);
}

fn serializeDirectVersion(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof, has_chip: bool, bound: bool) ![]u8 {
    if ((proof.chip_claimed_sum != null) != has_chip or proof.bridge_claimed_sum != null) return error.WrongProofProfile;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, if (bound)
        (if (has_chip) DIRECT_CHIP_BOUND_MAGIC else DIRECT_GATE_BOUND_MAGIC)
    else if (has_chip) DIRECT_CHIP_MAGIC else DIRECT_GATE_MAGIC);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    try appendSum(allocator, &bytes, proof.claimed_sums.toArray()[1]);
    if (has_chip) try appendSum(allocator, &bytes, proof.chip_claimed_sum.?);
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

pub fn serializeDirectPrivate(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    return serializeDirectPrivateVersion(allocator, proof, false);
}

pub fn serializeDirectPrivateBound(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof) ![]u8 {
    return serializeDirectPrivateVersion(allocator, proof, true);
}

fn serializeDirectPrivateVersion(allocator: std.mem.Allocator, proof: *const cpu.Internal.CircuitProof, bound: bool) ![]u8 {
    if (proof.chip_claimed_sum == null or proof.bridge_claimed_sum == null) return error.WrongProofProfile;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, if (bound) DIRECT_PRIVATE_BOUND_MAGIC else DIRECT_PRIVATE_MAGIC);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    try appendSum(allocator, &bytes, proof.claimed_sums.toArray()[1]);
    try appendSum(allocator, &bytes, proof.chip_claimed_sum.?);
    try appendSum(allocator, &bytes, proof.bridge_claimed_sum.?);
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

pub fn verifyDirect(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.direct_arithmetic.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
    chip_spec: ?HybridSpec,
) !void {
    return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, chip_spec, null, false);
}

pub fn verifyDirectBound(allocator: std.mem.Allocator, layout: *const circuit.common.direct_arithmetic.Layout, template: *const cpu.air.Bundle, pcs: core.pcs.config_v2.PcsConfigV2, preprocessed_root: H.Hash, circuit_hash: H.Hash, public_words: [8]u32, raw: []const u8, source_digest: [32]u8, chip_spec: HybridSpec) !void {
    return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, chip_spec, null, true);
}

pub fn verifyDirectGateBound(allocator: std.mem.Allocator, layout: *const circuit.common.direct_arithmetic.Layout, template: *const cpu.air.Bundle, pcs: core.pcs.config_v2.PcsConfigV2, preprocessed_root: H.Hash, circuit_hash: H.Hash, public_words: [8]u32, raw: []const u8, source_digest: [32]u8) !void {
    return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, null, null, true);
}

pub fn verifyDirectPrivate(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.direct_arithmetic.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
    chip_spec: HybridSpec,
    boundary: cpu.private_boundary_bridge.Boundary,
) !void {
    return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, chip_spec, boundary, false);
}

pub fn verifyDirectPrivateBound(allocator: std.mem.Allocator, layout: *const circuit.common.direct_arithmetic.Layout, template: *const cpu.air.Bundle, pcs: core.pcs.config_v2.PcsConfigV2, preprocessed_root: H.Hash, circuit_hash: H.Hash, public_words: [8]u32, raw: []const u8, source_digest: [32]u8, chip_spec: HybridSpec, boundary: cpu.private_boundary_bridge.Boundary) !void {
    return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, chip_spec, boundary, true);
}

fn verifyDirectProfile(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.direct_arithmetic.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    preprocessed_root: H.Hash,
    circuit_hash: H.Hash,
    public_words: [8]u32,
    raw: []const u8,
    source_digest: [32]u8,
    chip_spec: ?HybridSpec,
    private_boundary: ?cpu.private_boundary_bridge.Boundary,
    manifest_bound: bool,
) !void {
    const has_chip = chip_spec != null;
    if (private_boundary != null and !has_chip) return error.WrongProofProfile;
    if (private_boundary != null) {
        if (!std.mem.eql(u8, &chip_spec.?.source_digest, &source_digest)) return error.InvalidChipSource;
        try private_boundary.?.validate(core.fields.m31.Modulus);
    }
    const magic = if (manifest_bound)
        (if (private_boundary != null) DIRECT_PRIVATE_BOUND_MAGIC else if (has_chip) DIRECT_CHIP_BOUND_MAGIC else DIRECT_GATE_BOUND_MAGIC)
    else if (private_boundary != null) DIRECT_PRIVATE_MAGIC else if (has_chip) DIRECT_CHIP_MAGIC else DIRECT_GATE_MAGIC;
    const sum_count: usize = if (private_boundary != null) 3 else if (has_chip) 2 else 1;
    const header_len = magic.len + 8 + sum_count * 16;
    if (raw.len < header_len or raw.len > (16 << 20) or !std.mem.eql(u8, raw[0..magic.len], magic))
        return error.InvalidNativeProof;
    // Keep this owner in place: every handle points into it. The predecode
    // geometry check and the final core verifier consume this exact roster.
    var direct_handles: direct_component_preflight.DirectHandles = undefined;
    try direct_handles.init(
        allocator,
        layout,
        template,
        pcs,
        if (chip_spec) |item| .{ .rounds = item.rounds, .constant = item.constant } else null,
        private_boundary,
    );
    defer direct_handles.deinit();
    // Inspect the actual verifier handles and bounded proof shape before
    // allocating for postcard decoding. The source-pinned key was checked by
    // mvp_runtime before this entrypoint is called.
    if (manifest_bound and has_chip) {
        const live = try direct_component_preflight.inspectHandles(allocator, layout, pcs, &direct_handles);
        if (live.count != sum_count) return error.InvalidDirectHandleRoster;
        try postcard.proof_preflight.validateFor(4, raw[header_len..], .{
            .config = .{
                .pow_bits = pcs.fri_config.pow_bits,
                .log_blowup_factor = pcs.fri_config.log_blowup_factor,
                .n_queries = pcs.fri_config.n_queries,
                .log_last_layer_degree_bound = pcs.fri_config.log_last_layer_degree_bound,
                .fold_step = pcs.fri_config.fold_step,
                .lifting_log_size = null,
            },
            .tree_columns = live.tree_columns,
            .max_column_log_size = live.max_column_log_size,
            .sample_width_limits = live.sample_width_limits,
            .hash_size = @sizeOf(H.Hash),
            .max_wire_bytes = (16 << 20) - header_len,
        });
    }
    const nonce = std.mem.readInt(u64, raw[magic.len..][0..8], .little);
    var sums: [3]QM31 = undefined;
    for (sums[0..sum_count], 0..) |*sum, index| {
        const start = magic.len + 8 + index * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, raw[start + 4 * j ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    try pcs_mode_binding.requireLegacyPostcard(raw[header_len..]);
    const decode_memory = try allocator.alloc(u8, 64 << 20);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(raw[header_len..]);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != raw.len - header_len or
        stark.commitment_scheme_proof.commitments.items.len != 4)
        return error.InvalidNativeProof;
    if (!std.meta.eql(stark.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))
        return error.InvalidProofConfig;
    const roots = stark.commitment_scheme_proof.commitments.items;
    if (!std.mem.eql(u8, &preprocessed_root, &roots[0])) return error.InvalidPreprocessedRoot;
    var outputs: [8]QM31 = undefined;
    for (public_words, &outputs) |word, *output| {
        if (word >= core.fields.m31.Modulus) return error.InvalidPublicStatement;
        output.* = QM31.fromBase(M31.fromCanonical(word));
    }
    var initial = [_]M31{M31.zero()} ** 4;
    var final = [_]M31{M31.zero()} ** 4;
    if (has_chip and private_boundary == null) for (0..4) |i| {
        initial[i] = M31.fromCanonical(public_words[i]);
        final[i] = M31.fromCanonical(public_words[4 + i]);
    };
    const chip_request: ?cpu.prove.ChipRequest = if (chip_spec) |item| .{
        .source_digest = source_digest,
        .rounds = item.rounds,
        .constant = item.constant,
        .initial = initial,
        .final = final,
    } else null;
    const log_size = layout.traceLogSize();
    const expected_hash = cpu.direct_arithmetic.identityHashWithPrivateBoundary(
        source_digest,
        preprocessed_root,
        log_size,
        pcs.fri_config.log_blowup_factor,
        chip_request,
        private_boundary,
    );
    if (!std.mem.eql(u8, &expected_hash, &circuit_hash)) return error.InvalidCircuitHash;
    var channel = MC.Channel{};
    cpu.direct_arithmetic.mixProfile(&channel, .{
        .source_digest = source_digest,
        .chip_request = chip_request,
        .private_boundary = private_boundary,
    });
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(H, MC).init(allocator, pcs);
    defer scheme.deinit(allocator);
    var component_logs = try direct_handles.components().columnLogSizes(allocator);
    defer component_logs.deinitDeep(allocator);
    if (component_logs.items.len != 3) return error.InvalidDirectHandleTree;
    try scheme.commit(allocator, roots[0], component_logs.items[0], &channel);
    MC.mixRoot(&channel, circuit_hash);
    channel.mixFelts(&outputs);
    try scheme.commit(allocator, roots[1], component_logs.items[1], &channel);
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return error.InvalidInteractionNonce;
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    const circuit_sum = try circuit.witness.direct_arithmetic.lookupSum(&outputs, sums[0], lookup.z, lookup.alpha);
    if (private_boundary) |_| {
        if (!circuit_sum.add(sums[1]).add(sums[2]).isZero()) return error.InvalidPrivateBoundaryLookupSum;
    } else if (!circuit_sum.isZero()) return error.InvalidLookupSum;
    if (private_boundary == null) if (chip_spec) |item| if (!(try chip.endpointSum(
        sums[1],
        .init(lookup.z, lookup.alpha),
        item.rounds,
        initial,
        final,
    )).isZero()) return error.InvalidChipLookupSum;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..sum_count]);
    try scheme.commit(allocator, roots[2], component_logs.items[2], &channel);
    try direct_handles.setClaims(lookup.z, lookup.alpha, sums[0..sum_count]);
    var capture: core.verifier.ProofCapture(H) = undefined;
    try core.verifier.verifyBorrowedExWithProofCapture(
        H,
        MC,
        allocator,
        direct_handles.slice(),
        &channel,
        &scheme,
        &stark,
        true,
        &capture,
    );
    defer capture.deinit(allocator);
    try deep_capture_admission.validate(allocator, pcs.trace_lifting_log_size, capture.queries.raw, capture.column_log_sizes, capture.sampled_points, capture.sampled_values, capture.queried_values, capture.deep_answers, capture.deep_randomness);
    try fri_capture_admission.validate(
        H,
        allocator,
        pcs.fri_config.folding(),
        capture.queries.raw,
        capture.deep_answers,
        capture.fri,
        capture.last_layer_coefficients,
    );
    try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);
    try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);
}

fn sparseLogs(
    allocator: std.mem.Allocator,
    sizes: anytype,
    widths: anytype,
    chip_log: ?u32,
    chip_width: usize,
) ![]u32 {
    var count: usize = 0;
    inline for (widths) |width| count += width;
    const out = try allocator.alloc(u32, count + if (chip_log != null) chip_width else @as(usize, 0));
    var at: usize = 0;
    inline for (widths, 0..) |width, index| {
        @memset(out[at..][0..width], sizes[index]);
        at += width;
    }
    if (chip_log) |size| @memset(out[at..], size);
    return out;
}
