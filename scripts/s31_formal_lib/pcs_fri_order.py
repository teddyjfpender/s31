"""Reviewable source guard for the pinned native PCS/FRI transcript path.

This detects accidental reordering or removal of selected verifier barriers.
It is deliberately a source contract, not a cryptographic soundness proof.
The corresponding Lean model proves query-set and pre-hash-input properties.
"""
from __future__ import annotations

from pathlib import Path


def region(source: str, start: str, end: str) -> str:
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError(f"PCS/FRI source region changed: {start!r} / {end!r}")
    first = source.index(start)
    last = source.index(end)
    if first >= last:
        raise ValueError(f"PCS/FRI source region reversed: {start!r} / {end!r}")
    return source[first:last]


def ordered_once(source: str, label: str, *stages: str) -> None:
    positions = []
    for stage in stages:
        if source.count(stage) != 1:
            raise ValueError(f"{label}: stage count changed: {stage!r}")
        positions.append(source.index(stage))
    if positions != sorted(positions):
        raise ValueError(f"{label}: transcript stages reordered")


def check_sources(pcs: str, fri: str, queries: str, channel: str, merkle_channel: str) -> None:
    pcs_impl = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    ordered_once(
        pcs_impl, "PCS DEEP and query barriers",
        "if (proof.commitments.items.len != self.trees.items.len)",
        "for (self.trees.items, proof.commitments.items) |tree, commitment|",
        "if (!std.meta.eql(tree.root, commitment))",
        "channel.mixFelts(sampled_values_flat);",
        "const deep_randomness = channel.drawSecureFelt();",
        "FriVerifier.commit(",
        "channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)",
        "channel.mixU64(proof.proof_of_work);",
        "fri_verifier.sampleQueryPositionsWithRaw(",
        "tree.verifyWithPathCapture(",
        "tree.verify(",
        "const fri_answers = try quotients.friAnswers(",
        "fri_verifier.decommitWithQueryCapture(",
        "fri_verifier.decommit(allocator, fri_answers)",
    )
    fri_commit = region(fri, "pub fn commit(", "pub fn sampleQueryPositions(")
    if fri_commit.count("channel.drawSecureFelt()") != 2:
        raise ValueError("FRI commitment and challenge barriers: challenge draw count changed")
    ordered_once(
        fri_commit, "FRI commitment and challenge barriers",
        "if (config.fold_step == 0 or column_bound.logDegreeBound() < config.fold_step)",
        "proof_in.inner_layers.len != config_mod.nFoldSteps(",
        "MC.mixRoot(channel, proof_in.first_layer.commitment);",
        ".folding_alpha = channel.drawSecureFelt(),\n                .proof =",
        "MC.mixRoot(channel, inner_proof.commitment);",
        ".folding_alpha = channel.drawSecureFelt(),\n                    .layer_index = i,",
        "if (last_layer_poly.len() >",
        "channel.mixFelts(last_layer_poly.coefficients());",
    )
    fri_query = region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit(")
    ordered_once(
        fri_query, "FRI raw query ownership",
        "const raw = try queries_mod.drawQueries(",
        "self.queries = try queries_mod.Queries.init(",
        ".raw = raw,",
        ".unique = try allocator.dupe(usize, self.queries.?.positions),",
    )
    normalize = region(queries, "pub fn sortedUniquePositions(", "pub fn isStrictlyIncreasing(")
    ordered_once(
        normalize, "query normalization",
        "std.sort.heap(usize, out, {}, lessThanUsize);",
        "out[unique_len - 1] != position",
        "return allocator.realloc(out, unique_len);",
    )
    fold = region(queries, "pub fn fold(self: Queries,", "fn lessThanUsize(")
    ordered_once(
        fold, "FRI query fold",
        "const folded = q >> @intCast(n_folds);",
        "tmp[unique_len - 1] != folded",
        "@memcpy(positions, tmp[0..unique_len]);",
    )
    draw = region(channel, "pub fn drawU32s(self: *Self)", "pub fn drawSecureFelt(")
    ordered_once(
        draw, "Blake2s query draw input",
        "@memcpy(hash_input[0..32], self.digest[0..]);",
        "const counter = u32ToBytesLe(self.n_draws);",
        "@memcpy(hash_input[32..36], counter[0..]);",
        "hash_input[36] = 0;",
        "const hash = hashBytes(hash_input[0..]);",
    )
    root = region(merkle_channel, "pub fn Blake2sMerkleChannelGeneric(", "pub const Blake2sMerkleChannel =")
    ordered_once(
        root, "Blake2s root absorption",
        "const digest = channel.digestBytes();",
        "channel.updateDigest(",
        "blake2_hash.Blake2sHasherGeneric(is_m31_output).concatAndHash(digest, root)",
    )


def check_pcs_fri_order(root: Path) -> None:
    engine = root / "deps/stwo-zig/src/core"
    check_sources(
        (engine / "pcs/verifier.zig").read_text(),
        (engine / "fri.zig").read_text(),
        (engine / "queries.zig").read_text(),
        (engine / "channel/blake2s.zig").read_text(),
        (engine / "vcs_lifted/blake2_merkle.zig").read_text(),
    )
