//! Experimental Gate P05 source ensemble extracted from an accepted native
//! verifier capture. This is an integration contract, not a proof verifier.
//! In particular it cannot turn the four challenge-separated source roots
//! into CAS09's one pre-OOD source root.
const std = @import("std");
const core = @import("stwo_core");
const roster = @import("s31_p05_roster");

const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const QM31 = core.fields.qm31.QM31;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;

pub const version: u8 = 1;
pub const RootEpoch = enum(u2) { fixed, main, interaction, composition };

pub const Epoch = struct {
    kind: RootEpoch,
    root: H.Hash,
    first_column: usize,
    column_count: usize,
};

pub const SourceColumn = struct {
    epoch: RootEpoch,
    tree_index: usize,
    column_index: usize,
    source_log_size: u32,
    /// Log size supplied to native PCS commit before FRI blowup. A future
    /// protocol must independently test the original and own quotient at the
    /// appropriate degree; this metadata does not perform that test.
    committed_input_log_size: u32,
    /// Independent original track within this source-height batch.
    original_slot: usize,
    /// One own-quotient track for each verifier-owned OOD claim. The source
    /// column itself appears only once in the original track.
    first_own_quotient_slot: usize,
    first_claim: usize,
    claim_count: usize,
};

pub const HeightBucket = struct {
    source_log_size: u32,
    source_columns: usize,
    original_tracks: usize,
    own_quotient_tracks: usize,
    composition_columns: usize,
    ood_claims: usize,
};

pub const Plan = struct {
    epochs: [4]Epoch,
    columns: []SourceColumn,
    claims: []roster.Claim,
    /// Descending source-height order; empty heights are deliberately absent.
    heights: []HeightBucket,
    composition_randomness: QM31,
    oods_seed: QM31,
    native_deep_randomness: QM31,
    /// The paper's maximum *weighted ensemble* width has not been mapped to
    /// this sparse native roster. Physical 319-column width is not M.
    theorem_batch_width_M: ?usize = null,

    pub fn deinit(self: *Plan, allocator: std.mem.Allocator) void {
        allocator.free(self.heights);
        allocator.free(self.claims);
        allocator.free(self.columns);
        self.* = undefined;
    }

    /// CAS09 authenticates one source root before OOD. Gate commits four
    /// roots across distinct challenge epochs, so a silent flattening would
    /// change the Fiat-Shamir transcript even if roots happened to coincide.
    pub fn requireSinglePreOodRoot(_: *const Plan) error{RequiresMultiEpochProtocol}!void {
        return error.RequiresMultiEpochProtocol;
    }
};

/// Derive a versioned Gate source contract only from the same scheme, AIR
/// handles, sampled values, and capture as an *already successful* native
/// verification. The caller must establish that accepted-object identity.
/// This checks all four roots, all committed columns, all verifier-generated
/// OOD points/values, and precisely eight split-one composition columns.
/// No field here certifies independent whole-oracle degree or soundness bits.
pub fn derive(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    scheme: anytype,
    handles: []const core.air.components.Component,
    accepted_values: core.pcs.TreeVec([][]QM31),
    capture: *const core.verifier.ProofCapture(H),
) !Plan {
    const claims = try roster.derive(H, allocator, pcs, scheme, handles, accepted_values, capture, true);
    errdefer allocator.free(claims);
    if (capture.column_log_sizes[3].len != 8)
        return error.InvalidP05GatePlan;

    var column_count: usize = 0;
    for (capture.column_log_sizes) |logs| {
        column_count = std.math.add(usize, column_count, logs.len) catch
            return error.InvalidP05GatePlan;
    }
    const columns = try allocator.alloc(SourceColumn, column_count);
    errdefer allocator.free(columns);
    const buckets = try allocator.alloc(HeightBucket, column_count);
    errdefer allocator.free(buckets);
    var bucket_count: usize = 0;
    var column_at: usize = 0;
    var claim_at: usize = 0;
    var epochs: [4]Epoch = undefined;
    for (capture.column_log_sizes, 0..) |logs, tree_index| {
        const kind: RootEpoch = @enumFromInt(@as(u2, @intCast(tree_index)));
        epochs[tree_index] = .{
            .kind = kind,
            .root = capture.commitments[tree_index],
            .first_column = column_at,
            .column_count = logs.len,
        };
        for (logs, 0..) |log, index| {
            // `CommitmentSchemeVerifier.commit` adds FRI blowup before storing
            // `tree.column_log_sizes`; `columnLogSizes` copies those stored
            // logs and `verifyValuesImpl` copies them into ProofCapture.
            // This subtraction recovers the input log, not a tested degree.
            const input_log = std.math.sub(u32, log, pcs.fri_config.log_blowup_factor) catch
                return error.InvalidP05GatePlan;
            if (log > pcs.trace_lifting_log_size)
                return error.InvalidP05GatePlan;
            const first_claim = claim_at;
            while (claim_at < claims.len and
                claims[claim_at].tree_index == tree_index and
                claims[claim_at].column_index == index) : (claim_at += 1)
            {
                if (claims[claim_at].source_log_size != log or
                    claims[claim_at].sample_index != claim_at - first_claim)
                    return error.InvalidP05GatePlan;
            }
            if (claim_at == first_claim) return error.InvalidP05GatePlan;
            var bucket_at: usize = 0;
            while (bucket_at < bucket_count and
                buckets[bucket_at].source_log_size != log) : (bucket_at += 1)
            {}
            if (bucket_at == bucket_count) {
                buckets[bucket_count] = .{
                    .source_log_size = log,
                    .source_columns = 0,
                    .original_tracks = 0,
                    .own_quotient_tracks = 0,
                    .composition_columns = 0,
                    .ood_claims = 0,
                };
                bucket_count += 1;
            }
            columns[column_at] = .{
                .epoch = kind,
                .tree_index = tree_index,
                .column_index = index,
                .source_log_size = log,
                .committed_input_log_size = input_log,
                .original_slot = buckets[bucket_at].original_tracks,
                .first_own_quotient_slot = buckets[bucket_at].own_quotient_tracks,
                .first_claim = first_claim,
                .claim_count = claim_at - first_claim,
            };
            column_at += 1;
            buckets[bucket_at].source_columns += 1;
            buckets[bucket_at].original_tracks += 1;
            buckets[bucket_at].own_quotient_tracks += claim_at - first_claim;
            if (kind == .composition)
                buckets[bucket_at].composition_columns += 1;
            buckets[bucket_at].ood_claims += claim_at - first_claim;
        }
    }
    if (column_at != column_count or claim_at != claims.len)
        return error.InvalidP05GatePlan;
    // The multi-domain insertion schedule descends by source height. The
    // order within one height remains fixed/main/interaction/composition.
    std.sort.heap(HeightBucket, buckets[0..bucket_count], {}, struct {
        fn less(_: void, a: HeightBucket, b: HeightBucket) bool {
            return a.source_log_size > b.source_log_size;
        }
    }.less);
    const heights = try allocator.dupe(HeightBucket, buckets[0..bucket_count]);
    allocator.free(buckets);
    return .{
        .epochs = epochs,
        .columns = columns,
        .claims = claims,
        .heights = heights,
        .composition_randomness = capture.composition_randomness,
        .oods_seed = capture.oods_seed,
        .native_deep_randomness = capture.deep_randomness,
    };
}
