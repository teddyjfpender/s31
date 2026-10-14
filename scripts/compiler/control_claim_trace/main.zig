//! Test-only reconstruction of one transparent control proof's Gate-producing
//! trace. The executable prints counts and commitment matches, never cells.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const prover = @import("stwo_prover_engine");
const postcard = @import("interop_postcard");
const s31 = @import("stwo_s31_prototype");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Engine = cpu.Internal.Engine;
const Channel = cpu.Internal.Channel;
const ColumnEvaluation = prover.pcs.ColumnEvaluation;
const PP = circuit.common.preprocessed.PreprocessedCircuit;
const component = circuit.witness.components;
const trace = circuit.witness.trace;
const n_components = circuit.common.component_list.N_COMPONENTS;
const magic = "S31NAT1\x00";
const header_len = magic.len + 8 + n_components * 16;

fn fail(reason: []const u8) error{AuditMismatch} {
    std.debug.print("control claim trace: {s}\n", .{reason});
    return error.AuditMismatch;
}

fn cloneColumns(allocator: std.mem.Allocator, source: []const ColumnEvaluation) ![]ColumnEvaluation {
    const owned = try allocator.alloc(ColumnEvaluation, source.len);
    var ready: usize = 0;
    errdefer {
        for (owned[0..ready]) |entry| allocator.free(entry.values);
        allocator.free(owned);
    }
    for (source, owned) |entry, *slot| {
        slot.* = .{ .log_size = entry.log_size, .values = try allocator.dupe(M31, entry.values) };
        ready += 1;
    }
    return owned;
}

fn sameTopology(a: *const circuit.builder.Circuit, b: *const circuit.builder.Circuit) bool {
    if (a.n_vars != b.n_vars) return false;
    inline for (.{ "add", "sub", "mul", "pointwise_mul", "eq", "triple_xor", "m31_to_u32", "blake_g_gate", "output" }) |field| {
        const left = @field(a, field).items;
        const right = @field(b, field).items;
        if (left.len != right.len) return false;
        for (left, right) |x, y| if (!std.meta.eql(x, y)) return false;
    }
    return std.mem.eql(u32, a.permutation.ends.items, b.permutation.ends.items) and
        std.mem.eql(u32, a.permutation.inputs.items, b.permutation.inputs.items) and
        std.mem.eql(u32, a.permutation.outputs.items, b.permutation.outputs.items);
}

fn gateYield(lookup: component.Lookup, address: M31, multiplicity: M31, expected: []const M31) bool {
    if (lookup.relation() != circuit.common.component_list.GATE_RELATION_ID or
        !lookup.numerator.eql(multiplicity.neg()) or
        lookup.len != expected.len + 2 or
        lookup.tuple[1].toU32() != address.toU32()) return false;
    for (expected, lookup.tuple[2..lookup.len]) |a, b| if (!a.eql(b)) return false;
    return true;
}

/// All four Gate-producing components are enumerated. The table components
/// have no Gate yields. A zero multiplicity is not an active producer.
fn producerCounts(pp: *const PP, columns: []const ColumnEvaluation) ![4]usize {
    var seen = std.AutoHashMap(u32, void).init(std.heap.page_allocator);
    defer seen.deinit();
    const widths = trace.traceWidths();
    var offsets: [n_components]usize = undefined;
    var offset: usize = 0;
    for (widths, &offsets) |width, *slot| { slot.* = offset; offset += width; }
    if (columns.len != offset) return fail("base component width changed");
    const groups = .{
        .{ component.qm31_ops, 1, circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, 6, 7, 8, 12, 2 },
        .{ component.triple_xor, 2, circuit.common.preprocessed.TRIPLE_XOR_COLUMN_IDS, 3, 4, 6, 8, 11 },
        .{ component.m31_to_u32, 3, circuit.common.preprocessed.M31_TO_U32_COLUMN_IDS, 1, 2, 1, 3, 4 },
        .{ component.blake_g_gate, 4, circuit.common.preprocessed.BLAKE_G_GATE_COLUMN_IDS, 6, 10, 12, 20, 25 },
    };
    var counts: [4]usize = @splat(0);
    inline for (groups, 0..) |group, group_index| {
        const K = group[0];
        const component_index = group[1];
        const ids = group[2];
        const out_col = pp.columnValues(ids[group[3]]) orelse return fail("missing fixed output address");
        const mult_col = pp.columnValues(ids[group[4]]) orelse return fail("missing fixed output multiplicity");
        const width = K.n_columns;
        const start = offsets[component_index];
        const rows = columns[start].values.len;
        if (out_col.len != rows or mult_col.len != rows) return fail("producer component row count changed");
        for (0..rows) |r| {
            const mult = mult_col[r].toU32();
            if (mult == 0) continue;
            var words: [width]M31 = undefined;
            for (&words, columns[start..][0..width]) |*word, col| word.* = col.values[r];
            // This checks the concrete base cells and fixed cells used by the
            // installed lookup tuple. The row's AIR residuals are separate.
            const output = words[group[5]..group[6]];
            if (group_index == 0) {
                const lookups = K.lookups(&words, .{
                    .in0 = (pp.columnValues(ids[4]) orelse unreachable)[r],
                    .in1 = (pp.columnValues(ids[5]) orelse unreachable)[r],
                    .out = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("QM31 producer tuple differs from base cells");
            } else if (group_index == 1) {
                const lookups = K.lookups(&words, .{
                    .in0 = (pp.columnValues(ids[0]) orelse unreachable)[r],
                    .in1 = (pp.columnValues(ids[1]) orelse unreachable)[r],
                    .in2 = (pp.columnValues(ids[2]) orelse unreachable)[r],
                    .out = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("triple XOR producer tuple differs from base cells");
            } else if (group_index == 2) {
                const lookups = K.lookups(&words, .{
                    .input = (pp.columnValues(ids[0]) orelse unreachable)[r],
                    .output = out_col[r], .mults = mult_col[r],
                });
                if (!gateYield(lookups[group[7]], out_col[r], mult_col[r], output)) return fail("conversion producer tuple differs from base cells");
            } else {
                var inputs: [6]M31 = undefined;
                var outputs: [4]M31 = undefined;
                inline for (0..6) |i| inputs[i] = (pp.columnValues(ids[i]) orelse unreachable)[r];
                inline for (0..4) |i| outputs[i] = (pp.columnValues(ids[6 + i]) orelse unreachable)[r];
                const lookups = K.lookups(&words, .{ .inputs = inputs, .outputs = outputs, .mults = mult_col[r] });
                // Four output tuples, each encoded by two base limbs.
                for (0..4) |i| {
                    if (!gateYield(lookups[22 + i], outputs[i], mult_col[r], words[12 + i * 2 ..][0..2]))
                        return fail("Blake G producer tuple differs from base cells");
                    const entry = try seen.getOrPut(outputs[i].toU32());
                    if (entry.found_existing) return fail("two active Gate components own one address");
                }
            }
            if (group_index != 3) {
                const entry = try seen.getOrPut(out_col[r].toU32());
                if (entry.found_existing) return fail("two active Gate components own one address");
            }
            counts[group_index] += if (group_index == 3) 4 else 1;
        }
    }
    return counts;
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 5) return fail("usage: native-control-claim-trace source.s31.json assignment.json proof statement.json");
    const source_bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(source_bytes);
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 1 << 20);
    defer allocator.free(assignment_bytes);
    const proof_bytes = try std.fs.cwd().readFileAlloc(allocator, args[3], 16 << 20);
    defer allocator.free(proof_bytes);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[4], 1 << 20);
    defer allocator.free(statement_bytes);
    var program = try s31.relation.parseProgram(allocator, source_bytes);
    defer program.deinit();
    var assignment = try s31.relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    var statement = try s31.relation.parseAssignment(allocator, statement_bytes);
    defer statement.deinit();
    if (program.value.proof_mode != .transparent) return fail("only deterministic transparent Gate profile is audited");
    const words = try s31.relation.claimedWords(allocator, program.value, statement.value);
    const witness_words = try s31.relation.claimedWords(allocator, program.value, assignment.value);
    if (!std.meta.eql(words, witness_words)) return fail("assignment and public statement differ");
    var value_ctx = try s31.relation_compiler.compile(QM31, allocator, program.value, assignment.value);
    defer value_ctx.deinit();
    var topology_ctx = try s31.relation_compiler.compile(circuit.builder.NoValue, allocator, program.value, null);
    defer topology_ctx.deinit();
    if (!sameTopology(&value_ctx.circuit, &topology_ctx.circuit)) return fail("value-dependent compiler topology");
    try circuit.common.finalize.padContext(QM31, &value_ctx);
    try circuit.common.finalize.padContext(circuit.builder.NoValue, &topology_ctx);
    if (!sameTopology(&value_ctx.circuit, &topology_ctx.circuit) or !(try value_ctx.isCircuitValid()))
        return fail("padded compiler topology or witness invalid");
    var pp = try PP.fromBuilderCircuit(allocator, &topology_ctx.circuit);
    defer pp.deinit(allocator);
    var base = try trace.writeTrace(allocator, value_ctx.values(), &pp);
    defer base.deinit();
    if (base.output_values.len != 8) return fail("public output count changed");
    for (words, base.output_values) |word, output| {
        if (!output.eql(QM31.fromU32Unchecked(word & 0xffff, word >> 16, 0, 0)))
            return fail("public claim differs from base output cells");
    }
    const counts = try producerCounts(&pp, base.columns);
    if (proof_bytes.len < header_len or !std.mem.eql(u8, proof_bytes[0..magic.len], magic))
        return fail("proof envelope changed");
    const nonce = std.mem.readInt(u64, proof_bytes[magic.len..][0..8], .little);
    var sums: [n_components]QM31 = undefined;
    for (&sums, 0..) |*sum, i| {
        const offset = magic.len + 8 + i * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, j| {
            limb.* = std.mem.readInt(u32, proof_bytes[offset + j * 4 ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return fail("noncanonical interaction claim");
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    var stream = std.io.fixedBufferStream(proof_bytes[header_len..]);
    var stark = try postcard.deserializeProof(H, allocator, stream.reader());
    defer stark.deinit(allocator);
    if (stream.pos != proof_bytes.len - header_len or stark.commitment_scheme_proof.commitments.items.len != 4)
        return fail("proof commitment shape changed");
    const roots = stark.commitment_scheme_proof.commitments.items;
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndTraceSize(
        try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1), pp.traceLogSize());
    var fixed = try cpu.prove.PreprocessedCommitment.build(allocator, &pp, pcs, .{});
    defer fixed.deinit(allocator);
    if (!std.meta.eql(fixed.root(), roots[0])) return fail("fixed proof root changed");
    var channel = Channel{};
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var scheme = try Engine.initRevision(allocator, pcs);
    defer Engine.deinit(&scheme, allocator);
    scheme.setStorePolynomialsCoefficients();
    {
        var lease = fixed.tree.retainShared();
        errdefer lease.deinit(allocator);
        try scheme.appendCommittedTree(allocator, lease, &channel);
    }
    const hash = try circuit.common.circuit_hash.hostCircuitHash(base.log_sizes, pcs.fri_config.log_blowup_factor, roots[0]);
    cpu.prove.profiles.Blake2sM31MerkleChannel.mixRoot(&channel, hash);
    channel.mixFelts(base.output_values);
    try Engine.commit(&scheme, allocator, try cloneColumns(allocator, base.columns), null, &channel);
    try Engine.flushPendingCommit(&scheme, allocator, &channel);
    if (!std.meta.eql(scheme.trees.items[1].commitment.root(), roots[1]))
        return fail("reconstructed base cells differ from committed main root");
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))
        return fail("interaction nonce changed");
    channel.mixU64(nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    var interaction = try trace.writeInteractionTrace(allocator, base.columns, base.log_sizes, &pp, lookup.z, lookup.alpha);
    defer interaction.deinit();
    for (interaction.claimed_sums.toArray(), sums) |actual, claimed| {
        if (!actual.eql(claimed)) return fail("interaction claim differs from committed base-cell lookup reconstruction");
    }
    if (!(try trace.lookupSum(base.output_values, interaction.claimed_sums, lookup.z, lookup.alpha)).isZero())
        return fail("reconstructed public Gate interaction does not close");
    core.channel.lookup_transcript.mixInteractionClaim(&channel, &sums);
    try Engine.commit(&scheme, allocator, try cloneColumns(allocator, interaction.columns), null, &channel);
    try Engine.flushPendingCommit(&scheme, allocator, &channel);
    if (!std.meta.eql(scheme.trees.items[2].commitment.root(), roots[2]))
        return fail("reconstructed interaction cells differ from committed interaction root");
    std.debug.print("{{\"schema\":\"s31-control-claim-trace-v1\",\"base_root_match\":true,\"interaction_root_match\":true,\"all_component_claims_match\":true,\"producer_counts\":[{d},{d},{d},{d}]}}\n", .{ counts[0], counts[1], counts[2], counts[3] });
}
