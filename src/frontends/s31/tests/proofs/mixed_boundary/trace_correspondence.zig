//! Concrete N=1/N=8 source-to-native-circuit and base-trace fixture.
//!
//! These are the same base writers called by general_package.proveSealed via
//! direct_mixed_general_arithmetic.proveSourceBound. It checks the emitted
//! pack, public arithmetic, unpack and output-copy Gate rows as well as the
//! bridge/chip base rows. The fixture also proves and verifies the exact
//! pinned sources, then changes proof-envelope fields.
//! It does not establish a general compiler correspondence theorem.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("interop_postcard");
const relation = @import("../../../language/relation.zig");
const binding = @import("../../../runtime/bounded_compiled_binding.zig");
const mixed = @import("../../../runtime/mixed_boundary/inspection.zig");
const family = @import("../../../runtime/mixed_boundary/test_source.zig");
const package = @import("../../../runtime/mixed_boundary/general_package.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const BinaryGate = circuit.builder.circuit.BinaryGate;
const p = core.fields.m31.Modulus;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;

fn pinnedSource(comptime count: usize) []const u8 {
    const original = family.forCount(count);
    const old = "\"name\":\"mixed_descriptor_matrix\"";
    const at = comptime std.mem.indexOf(u8, original, old) orelse @compileError("missing fixture name");
    return original[0..at] ++
        std.fmt.comptimePrint("\"name\":\"mixed_general_{d}\"", .{count}) ++
        original[at + old.len ..];
}

fn step(words: *[4]u32, constant: u32) void {
    for (words) |*word|
        word.* = @intCast((@as(u64, word.*) * word.* + constant) % p);
}

fn wordsAt(values: []const QM31, addresses: [4]u32) ![4]u32 {
    var result: [4]u32 = undefined;
    for (addresses, &result) |address, *word| {
        if (address >= values.len) return error.InvalidFixtureEndpoint;
        word.* = (try values[address].tryIntoM31()).toU32();
    }
    return result;
}

fn packWords(words: [4]u32) QM31 {
    return QM31.fromU32Unchecked(words[0], words[1], words[2], words[3]);
}

fn gateAt(gates: []const BinaryGate, output: u32) !BinaryGate {
    var found: ?BinaryGate = null;
    for (gates) |gate| {
        if (gate.out != output) continue;
        if (found != null) return error.DuplicateFixtureGateOutput;
        found = gate;
    }
    return found orelse error.MissingFixtureGate;
}

fn checkPackRows(view: circuit.common.preprocessed.CircuitView, values: []const QM31, scalar: [4]u32, output: u32, words: [4]u32) !void {
    if (output < 5 or output >= values.len) return error.WrongFixturePackedAddress;
    const terms = [3]u32{ output - 5, output - 3, output - 1 };
    const units = [4]QM31{
        QM31.fromU32Unchecked(1, 0, 0, 0),
        QM31.fromU32Unchecked(0, 1, 0, 0),
        QM31.fromU32Unchecked(0, 0, 1, 0),
        QM31.fromU32Unchecked(0, 0, 0, 1),
    };
    for (scalar, words) |address, word| {
        if (address >= values.len or
            !values[address].eql(QM31.fromBase(M31.fromCanonical(word))))
            return error.WrongFixturePackScalar;
    }
    for (terms, 1..) |term, lane| {
        const gate = try gateAt(view.mul, term);
        if (gate.in1 != scalar[lane] or gate.in0 >= values.len or
            !values[gate.in0].eql(units[lane]) or
            !values[term].eql(units[lane].mul(values[scalar[lane]])))
            return error.WrongFixturePackTerm;
    }
    const additions = [3]BinaryGate{
        .{ .in0 = scalar[0], .in1 = terms[0], .out = output - 4 },
        .{ .in0 = output - 4, .in1 = terms[1], .out = output - 2 },
        .{ .in0 = output - 2, .in1 = terms[2], .out = output },
    };
    for (additions) |expected| {
        const gate = try gateAt(view.add, expected.out);
        if (!std.meta.eql(gate, expected) or
            !values[gate.out].eql(values[gate.in0].add(values[gate.in1])))
            return error.WrongFixturePackAdd;
    }
    if (!values[output].eql(packWords(words))) return error.WrongFixturePackedValue;
}

fn checkPublicTail(view: circuit.common.preprocessed.CircuitView, values: []const QM31, count: usize, initial: [4]u32, final: [4]u32, sums: [4]u32, products: [4]u32) !void {
    const first: u32 = 22;
    const last: u32 = @intCast(22 + 10 * count);
    const first_scalars = [4]u32{ 11, 12, 13, 14 };
    const last_scalars = [4]u32{ last - 9, last - 8, last - 7, last - 6 };
    try checkPackRows(view, values, first_scalars, first, initial);
    try checkPackRows(view, values, last_scalars, last, final);
    const add = try gateAt(view.add, last + 1);
    const mul = try gateAt(view.pointwise_mul, last + 2);
    if (add.in0 != first or add.in1 != last or
        mul.in0 != first or mul.in1 != last or
        !values[add.out].eql(values[first].add(values[last])) or
        !values[mul.out].eql(core.fields.qm31_pointwise.pointwiseMul(values[first], values[last])) or
        !values[add.out].eql(packWords(sums)) or !values[mul.out].eql(packWords(products)))
        return error.WrongFixturePackedArithmetic;
    const units = [4]QM31{
        QM31.fromU32Unchecked(1, 0, 0, 0),
        QM31.fromU32Unchecked(0, 1, 0, 0),
        QM31.fromU32Unchecked(0, 0, 1, 0),
        QM31.fromU32Unchecked(0, 0, 0, 1),
    };
    for (0..8) |slot| {
        const lane = slot % 4;
        const source: u32 = last + if (slot < 4) @as(u32, 1) else @as(u32, 2);
        const public: u32 = @intCast(3 + slot);
        const copy = try gateAt(view.add, public);
        if (copy.in1 != 0 or copy.in0 >= values.len or
            !values[public].eql(values[copy.in0]))
            return error.WrongFixturePublicCopy;
        const mask_address = if (lane == 0) copy.in0 else blk: {
            const inverse = try gateAt(view.mul, copy.in0);
            if (inverse.in1 >= values.len or
                !values[inverse.in1].eql(try units[lane].inv()) or
                !values[copy.in0].eql(values[inverse.in0].mul(values[inverse.in1])))
                return error.WrongFixtureUnpackInverse;
            break :blk inverse.in0;
        };
        const mask = try gateAt(view.pointwise_mul, mask_address);
        if (mask.in0 != source or mask.in1 >= values.len or
            !values[mask.in1].eql(units[lane]) or
            !values[mask.out].eql(core.fields.qm31_pointwise.pointwiseMul(values[source], values[mask.in1])))
            return error.WrongFixtureUnpackMask;
        const want = if (slot < 4) sums[lane] else products[lane];
        if ((try values[public].tryIntoM31()).toU32() != want)
            return error.WrongFixturePublicWord;
    }
    // The circuit also marks its fixed extension-basis variable 2 as an
    // output. The eight source public words occupy the following slots.
    if (view.output.len != 9 or view.output[0] != 2) return error.WrongFixturePublicWidth;
    for (view.output, 0..) |address, slot|
        if (address != 2 + slot) return error.WrongFixturePublicAddress;
}

fn checkBridge(columns: anytype, addresses: [8]u32, expected: [8]u32) !void {
    if (columns.len != 8) return error.WrongFixtureBridgeWidth;
    for (columns, addresses, expected) |column, address, word| {
        if (column.log_size != 4 or column.values.len != 16)
            return error.WrongFixtureBridgeRows;
        // The committed bridge has one constant column per endpoint; its
        // Gate event gets the address from the source-derived call plan.
        const native_gate = cpu.private_many_boundary.gateTuple(address, M31.fromCanonical(column.values[0].toU32()));
        if (native_gate[0].toU32() != circuit.common.component_list.GATE_RELATION_ID or
            native_gate[1].toU32() != address or native_gate[2].toU32() != word)
            return error.WrongFixtureGateTuple;
        for (native_gate[3..]) |zero| if (!zero.isZero()) return error.WrongFixtureGateTuple;
        for (column.values) |value|
            if (value.toU32() != word) return error.WrongFixtureBridgeWord;
    }
}

fn rejectChangedBridgeRow(columns: anytype, addresses: [8]u32, expected: [8]u32) !void {
    const mutable = @constCast(columns[0].values);
    const original = mutable[1];
    defer mutable[1] = original;
    mutable[1] = M31.fromCanonical((expected[0] + 1) % p);
    try std.testing.expectError(error.WrongFixtureBridgeWord, checkBridge(columns, addresses, expected));
}

fn fixture(comptime count: usize) !void {
    const allocator = std.testing.allocator;
    // These compile-time bytes are also the embedded verifier authority below.
    const source = comptime pinnedSource(count);
    const expected_source_sha256 = if (count == 1)
        "8c5296ef964e3be770e442cd28b66eed3051e210bdd6a97e265a4cd2c5962f75"
    else
        "08b5c20367e910261a194658bc3753038037fb85bc8f16dbc7f9191c7d1f45ff";
    var source_hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(source, &source_hash, .{});
    const source_hash_hex = std.fmt.bytesToHex(source_hash, .lower);
    if (!std.mem.eql(u8, &source_hash_hex, expected_source_sha256))
        return error.WrongFixtureSourceBytes;
    const air_bytes = @embedFile("s31_air_programs");
    const initial = [4]u32{ 1, 2, 3, 4 };
    var final = initial;
    for (0..count) |id| for (0..16) |_| step(&final, @intCast(13 + id));
    var sum: [4]u32 = undefined;
    var product: [4]u32 = undefined;
    for (final, initial, &sum, &product) |a, b, *s, *m| {
        s.* = @intCast((@as(u64, a) + b) % p);
        m.* = @intCast((@as(u64, a) * b) % p);
    }
    const assignment_json = try std.json.Stringify.valueAlloc(allocator, .{
        .public_inputs = struct {}{},
        .private_inputs = .{ .x = initial },
        .public_outputs = .{ .sum = sum, .product = product },
    }, .{});
    defer allocator.free(assignment_json);
    var assignment = try relation.parseAssignment(allocator, assignment_json);
    defer assignment.deinit();
    const selected = try mixed.inspectSource(allocator, source, air_bytes);
    const topology = try binding.compileSourceTopology(allocator, source);
    if (selected.call_count != count or topology.call_count != count or
        !std.meta.eql(selected.source_sha256, topology.source_sha256) or
        !std.meta.eql(selected.fixed_root, topology.fixed_root))
        return error.WrongFixtureSource;
    var witness = try binding.compileManyWitness(allocator, source, assignment.value, topology);
    defer witness.deinit();
    const values = witness.values();
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit);
    // This bounded source has no permutation scratch rows, so the native
    // source-variable producer check covers every emitted arithmetic output.
    if (view.nPermutations() != 0) return error.UnexpectedFixturePermutation;
    try view.validateUniqueProducers(allocator);
    try checkPublicTail(view, values, count, initial, final, sum, product);
    var plan: cpu.private_many_boundary.Plan = .{ .count = count };
    for (selected.calls[0..count], plan.calls[0..count], 0..) |call, *slot, id| {
        if (call.call_id != id or call.rounds != 16 or call.constant != 13 + id or
            !std.meta.eql(call.input, topology.calls[id].input) or
            !std.meta.eql(call.output, topology.calls[id].output))
            return error.WrongFixtureCall;
        // Independently pinned allocation for this exact source family:
        // initial scalar guesses 11..14, first result 23..26, then +10/call.
        for (0..4) |lane| {
            const want_input: u32 = if (id == 0) @intCast(11 + lane) else @intCast(23 + 10 * (id - 1) + lane);
            const want_output: u32 = @intCast(23 + 10 * id + lane);
            if (call.input[lane] != want_input or call.output[lane] != want_output)
                return error.WrongFixtureAddress;
        }
        slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    if (!std.meta.eql(try pp.preprocessedRoot(allocator, 1), selected.fixed_root))
        return error.WrongFixtureFixedRoot;
    var circuit_base = try circuit.witness.direct_arithmetic.writeBase(allocator, values, &pp);
    defer circuit_base.deinit();
    if (circuit_base.output_values.len != 8) return error.WrongFixturePublicWidth;
    for (sum ++ product, circuit_base.output_values) |word, actual|
        if ((try actual.tryIntoM31()).toU32() != word) return error.WrongFixturePublicWord;

    var state = initial;
    for (selected.calls[0..count], 0..) |call, id| {
        const input = state;
        if (!std.meta.eql(try wordsAt(values, call.input), input)) return error.WrongFixtureInput;
        var native_input: [4]M31 = undefined;
        for (input, &native_input) |word, *out| out.* = M31.fromCanonical(word);
        var chip_base = if (id < 2)
            try cpu.tagged_pair_chip.writeBase(allocator, native_input, M31.fromCanonical(call.constant), call.rounds)
        else
            try cpu.tagged_many_chip.writeBase(allocator, native_input, M31.fromCanonical(call.constant), call.rounds);
        defer chip_base.deinit();
        if (chip_base.columns.len != 9) return error.WrongFixtureChipWidth;
        for (0..16) |step_id| {
            const row = cpu.repeated_step_chip.storageIndex(step_id, 4);
            if (chip_base.columns[0].values[row].toU32() != step_id)
                return error.WrongFixtureChipStep;
            for (state, 0..) |word, lane|
                if (chip_base.columns[1 + lane].values[row].toU32() != word)
                    return error.WrongFixtureChipInput;
            step(&state, call.constant);
            for (state, 0..) |word, lane|
                if (chip_base.columns[5 + lane].values[row].toU32() != word)
                    return error.WrongFixtureChipOutput;
        }
        if (!std.meta.eql(try wordsAt(values, call.output), state))
            return error.WrongFixtureOutput;
        for (chip_base.final, state) |actual, word|
            if (actual.toU32() != word) return error.WrongFixtureChipFinal;
        // The seven-field chip tuples contain the same endpoints as the
        // source-shaped typed Boundary.start and Boundary.finish events.
        const start = cpu.private_many_boundary.chipTuple(call.call_id, 0, native_input);
        var native_final: [4]M31 = undefined;
        for (state, &native_final) |word, *out| out.* = M31.fromCanonical(word);
        const finish = cpu.private_many_boundary.chipTuple(call.call_id, call.rounds, native_final);
        if (start[0].toU32() != cpu.private_many_boundary.relation_id or
            start[1].toU32() != id or start[2].toU32() != 0 or
            finish[0].toU32() != cpu.private_many_boundary.relation_id or
            finish[1].toU32() != id or finish[2].toU32() != 16)
            return error.WrongFixtureChipTuple;
        for (0..4) |lane| if (start[3 + lane].toU32() != input[lane] or
            finish[3 + lane].toU32() != state[lane]) return error.WrongFixtureChipTuple;

        const native_call = plan.calls[id];
        const addresses = native_call.input ++ native_call.output;
        const expected = input ++ state;
        if (id < 2) {
            var bridge = try cpu.tagged_pair_bridge.writeBase(allocator, values, native_call);
            defer bridge.deinit();
            try checkBridge(bridge.columns, addresses, expected);
            if (id == 0) try rejectChangedBridgeRow(bridge.columns, addresses, expected);
        } else {
            var bridge = try cpu.tagged_many_bridge.writeBase(allocator, values, native_call);
            defer bridge.deinit();
            try checkBridge(bridge.columns, addresses, expected);
            if (id == 2) try rejectChangedBridgeRow(bridge.columns, addresses, expected);
        }
    }
    if (!std.meta.eql(state, final)) return error.WrongFixtureFinal;

    // Prove through the production package after checking the exact base
    // writers. Its engine consumes the same compiler witness and source-bound
    // plan; the native verifier rebuilds the plan and manifest from `source`.
    const proof_allocator = std.heap.smp_allocator;
    const sealed = try package.proveSealedAndInspect(proof_allocator, source, air_bytes, assignment.value);
    defer proof_allocator.free(sealed.bytes);
    if (!std.meta.eql(selected, sealed.inspection.schedule)) return error.WrongProofSchedule;
    const words = sum ++ product;
    const verified = try package.verifyEmbeddedAndInspect(source, air_bytes, proof_allocator, words, sealed.bytes);
    if (!std.meta.eql(verified.schedule, selected) or
        !std.meta.eql(verified.registry_manifest_sha256, sealed.inspection.registry_manifest_sha256) or
        !std.meta.eql(verified.circuit_identity_sha256, sealed.inspection.circuit_identity_sha256))
        return error.WrongVerifiedSchedule;

    const magic = "S31MIX07";
    const source_at = magic.len + 4;
    const manifest_at = source_at + 32;
    const identity_at = manifest_at + 32;
    const nonce_at = identity_at + 32;
    const sums_at = nonce_at + 8;
    const proof_at = sums_at + 16 * selected.slot_count;
    if (sealed.bytes.len <= proof_at or
        !std.mem.eql(u8, sealed.bytes[0..magic.len], magic) or
        sealed.bytes[magic.len] != count or
        sealed.bytes[magic.len + 1] != selected.slot_count or
        !std.mem.eql(u8, sealed.bytes[source_at..manifest_at], &selected.source_sha256) or
        !std.mem.eql(u8, sealed.bytes[manifest_at..identity_at], &verified.registry_manifest_sha256) or
        !std.mem.eql(u8, sealed.bytes[identity_at..nonce_at], &verified.circuit_identity_sha256))
        return error.WrongProofEnvelope;

    // Every mutation must fail native verification under the same embedded
    // source and public statement. The proof-body flip exercises decoding or
    // cryptographic verification, rather than only the envelope preflight.
    for ([_]usize{ source_at, manifest_at, identity_at, nonce_at, sums_at, sealed.bytes.len - 1 }) |at| {
        const changed = try proof_allocator.dupe(u8, sealed.bytes);
        defer proof_allocator.free(changed);
        changed[at] ^= 1;
        if (package.verifyEmbedded(source, air_bytes, proof_allocator, words, changed)) |_| {
            return error.AcceptedChangedProofByte;
        } else |_| {}
    }
    // Change the main Merkle root inside a decoded proof and serialize it
    // again. This is a well-formed proof body with unchanged envelope and
    // shape, so rejection exercises transcript/commitment verification rather
    // than a malformed postcard or an envelope digest mismatch.
    var stream = std.io.fixedBufferStream(sealed.bytes[proof_at..]);
    var stark = try postcard.deserializeProof(H, proof_allocator, stream.reader());
    defer stark.deinit(proof_allocator);
    if (stream.pos != sealed.bytes.len - proof_at or
        stark.commitment_scheme_proof.commitments.items.len != 4)
        return error.WrongDecodedProof;
    const original_main_root = stark.commitment_scheme_proof.commitments.items[1];
    stark.commitment_scheme_proof.commitments.items[1][0] ^= 1;
    if (std.meta.eql(original_main_root, stark.commitment_scheme_proof.commitments.items[1]))
        return error.UnchangedMainCommitment;
    var changed_commitment: std.ArrayList(u8) = .empty;
    defer changed_commitment.deinit(proof_allocator);
    try changed_commitment.appendSlice(proof_allocator, sealed.bytes[0..proof_at]);
    try postcard.serializeProof(H, changed_commitment.writer(proof_allocator), stark);
    if (changed_commitment.items.len != sealed.bytes.len or
        std.mem.eql(u8, changed_commitment.items, sealed.bytes))
        return error.WrongChangedCommitmentEncoding;
    const geometry = selected.native_geometry orelse return error.MissingFixtureGeometry;
    const pcs = geometry.pcs;
    var sample_width_limits: [4]u32 = .{ 0, 0, 0, 1 };
    for (geometry.tree_columns[0..3], 0..) |width, tree| {
        for (geometry.columns[tree][0..width]) |column|
            sample_width_limits[tree] = @max(sample_width_limits[tree], column.mask_width);
    }
    try postcard.proof_preflight.validateFor(4, changed_commitment.items[proof_at..], .{
        .config = .{
            .pow_bits = pcs.fri_config.pow_bits,
            .log_blowup_factor = pcs.fri_config.log_blowup_factor,
            .n_queries = pcs.fri_config.n_queries,
            .log_last_layer_degree_bound = pcs.fri_config.log_last_layer_degree_bound,
            .fold_step = pcs.fri_config.fold_step,
            .lifting_log_size = null,
        },
        .tree_columns = geometry.tree_columns,
        .max_column_log_size = geometry.max_column_log_size,
        .sample_width_limits = sample_width_limits,
        .hash_size = @sizeOf(H.Hash),
        .max_wire_bytes = (16 << 20) - proof_at,
    });
    if (package.verifyEmbedded(source, air_bytes, proof_allocator, words, changed_commitment.items)) |_| {
        return error.AcceptedChangedMainCommitment;
    } else |_| {}
    var changed_words = words;
    changed_words[0] = (changed_words[0] + 1) % p;
    if (package.verifyEmbedded(source, air_bytes, proof_allocator, changed_words, sealed.bytes)) |_| {
        return error.AcceptedChangedPublicWord;
    } else |_| {}
    // A different embedded source with the same recurrence still has a
    // different source digest, manifest, and verifier circuit identity.
    if (package.verifyEmbedded(family.forCount(count), air_bytes, proof_allocator, words, sealed.bytes)) |_| {
        return error.AcceptedChangedEmbeddedSource;
    } else |_| {}
}

test "mixed N1 and N8 source base rows and proof envelope match native verification" {
    try fixture(1);
    try fixture(8);
}
