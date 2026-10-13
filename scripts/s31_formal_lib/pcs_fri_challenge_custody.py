"""Source-pinned custody of native PCS/FRI challenges in successful captures.

This is a fail-closed source-shape check. It does not model Zig execution,
establish random-oracle independence, or prove the Fiat--Shamir reduction.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(pcs: str, fri: str) -> None:
    verify = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    if verify.count("channel.drawSecureFelt()") != 1:
        raise ValueError("PCS DEEP custody: draw count changed")
    ordered_once(
        verify, "PCS DEEP custody",
        "channel.mixFelts(sampled_values_flat);",
        "const deep_randomness = channel.drawSecureFelt();",
        "const fri_answers = try quotients.friAnswers(",
        "                deep_randomness,\n",
        "fri_verifier.decommitWithQueryCapture(",
        "if (proof_capture_out) |destination| {",
        "destination.* = .{\n                    .queries = query_capture,",
        ".deep_randomness = deep_randomness,",
    )
    ordered_once(
        verify, "PCS verified nonce custody",
        "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {\n"
        "                return verifier_types.VerificationError.ProofOfWork;\n"
        "            }",
        "channel.mixU64(proof.proof_of_work);",
        "fri_verifier.sampleQueryPositionsWithRaw(",
        "fri_verifier.decommitWithQueryCapture(",
        ".proof_of_work = proof.proof_of_work,",
    )
    if verify.count(".deep_randomness = deep_randomness,") != 1 or verify.count(
        ".proof_of_work = proof.proof_of_work,") != 1:
        raise ValueError("PCS capture: challenge or nonce assignment changed")

    commit = region(fri, "pub fn commit(", "pub fn sampleQueryPositions(")
    if commit.count(".folding_alpha = channel.drawSecureFelt(),") != 2:
        raise ValueError("FRI challenge custody: draw count changed")
    ordered_once(
        commit, "FRI first challenge custody",
        "MC.mixRoot(channel, proof_in.first_layer.commitment);",
        ".folding_alpha = channel.drawSecureFelt(),\n                .proof = try cloneLayerProof(H, allocator, proof_in.first_layer),",
        "for (proof_in.inner_layers, 0..) |inner_proof, i| {",
    )
    ordered_once(
        commit, "FRI inner challenge custody",
        "MC.mixRoot(channel, inner_proof.commitment);",
        ".folding_alpha = channel.drawSecureFelt(),\n                    .layer_index = i,",
        "channel.mixFelts(last_layer_poly.coefficients());",
    )
    clone = region(fri, "fn cloneLayerProof(", "fn FriFirstLayerVerifier(")
    if clone.count(".commitment = proof.commitment,") != 1:
        raise ValueError("FRI challenge custody: committed root copy changed")

    decommit = region(fri, "fn decommitImpl(", "fn decommitLastLayer(")
    ordered_once(
        decommit, "FRI first alpha use and capture",
        "var first_layer_sparse_eval = try self.first_layer.verifyImpl(",
        "if (capture_layers) |layers| {\n                layers[0] = first_layer_capture;",
        "self.first_layer.folding_alpha,",
        "for (self.inner_layers, 0..) |layer, layer_index| {",
        "try self.decommitLastLayer(allocator, layer_queries, layer_query_evals);",
        "if (capture_out) |destination| {",
        "destination.* = .{ .layers = capture_layers.? };",
    )
    ordered_once(
        decommit, "FRI inner alpha use and capture",
        "const folded = try layer.verifyAndFoldImpl(",
        "layers[layer_index + 1] = layer_capture;",
        "try self.decommitLastLayer(allocator, layer_queries, layer_query_evals);",
        "destination.* = .{ .layers = capture_layers.? };",
    )

    first = region(fri, "fn FriFirstLayerVerifier(", "fn FriInnerLayerVerifier(")
    inner = region(fri, "fn FriInnerLayerVerifier(", "fn buildFriLayerQueryCapture(")
    for name, source, fold in (
        ("first", first, None),
        ("inner", inner, "self.folding_alpha,\n                self.domain,"),
    ):
        ordered_once(
            source, f"FRI {name} captured alpha and root",
            "merkle_verifier.verifyWithPathCapture(",
            "destination.* = try buildFriLayerQueryCapture(",
            "self.proof.commitment,\n                    self.folding_alpha,",
        )
        if fold is not None:
            ordered_once(source, "FRI inner alpha fold", "destination.* = try buildFriLayerQueryCapture(", fold)
    builder = region(fri, "fn buildFriLayerQueryCapture(", "pub fn FriLayerProofAux(")
    ordered_once(
        builder, "FRI captured root and alpha fields",
        "commitment: H.Hash,\n    folding_alpha: QM31,",
        ".commitment = commitment,\n        .folding_alpha = folding_alpha,",
    )


def check_pcs_fri_challenge_custody(root: Path) -> None:
    engine = root / "deps/stwo-zig/src/core"
    check_sources((engine / "pcs/verifier.zig").read_text(), (engine / "fri.zig").read_text())
