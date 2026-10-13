"""Source contract for the pinned FRI layer acceptance chain.

The matching native regression executes an honest two-layer proof and hostile
changes. This guard binds its verifier path; it does not prove Zig semantics,
Merkle collision resistance, or FRI proximity.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(fri: str, folding: str, line: str) -> None:
    commit = region(fri, "pub fn commit(", "pub fn sampleQueryPositions(")
    ordered_once(
        commit, "FRI layer schedule and terminal degree",
        "proof_in.inner_layers.len != config_mod.nFoldSteps(",
        "const this_fold_step: u32 = config_mod.foldStepAt(",
        "layer_bound = layer_bound.fold(this_fold_step)",
        "if (layer_bound.logDegreeBound() != config.log_last_layer_degree_bound)",
        "if (last_layer_poly.len() > (@as(usize, 1) << @intCast(config.log_last_layer_degree_bound)))",
        "channel.mixFelts(last_layer_poly.coefficients());",
    )

    verify = region(fri, "fn decommitImpl(", "fn decommitLastLayer(")
    ordered_once(
        verify, "FRI accepted layer chain",
        "const queries = self.queries orelse",
        "self.first_layer.verifyImpl(",
        "var layer_queries = try queries.fold(allocator, self.config.fold_step);",
        "first_layer_sparse_eval.foldCircleSubsets(",
        "for (self.inner_layers, 0..) |layer, layer_index|",
        "layer.verifyAndFoldImpl(",
        "layer_queries = folded.queries;",
        "layer_query_evals = folded.evals;",
        "try self.decommitLastLayer(allocator, layer_queries, layer_query_evals);",
        "destination.* = .{ .layers = capture_layers.? };",
    )

    first = region(fri, "fn verifyImpl(", "fn FriInnerLayerVerifier(")
    ordered_once(
        first, "FRI first layer reconstruction and authentication",
        "if (queries.log_domain_size != self.column_commitment_domain.logSize())",
        "var rebuilt = computeDecommitmentPositionsAndRebuildEvals(",
        "queries,\n                column_query_evals,\n                self.proof.fri_witness,",
        "if (rebuilt.consumed_witness != self.proof.fri_witness.len)",
        "buildMerkleVerificationInputs(",
        "merkle_verifier.verifyWithPathCapture(",
        "merkle_verifier.verify(",
        "return rebuilt.sparse_evaluation;",
    )

    inner = region(fri, "fn verifyAndFoldImpl(", "const FoldedLayerState")
    ordered_once(
        inner, "FRI inner layer current-to-next link",
        "if (queries.log_domain_size != self.domain.logSize())",
        "var rebuilt = computeDecommitmentPositionsAndRebuildEvals(",
        "queries,\n                evals_at_queries,\n                self.proof.fri_witness,",
        "if (rebuilt.consumed_witness != self.proof.fri_witness.len)",
        "buildMerkleVerificationInputs(",
        "merkle_verifier.verifyWithPathCapture(",
        "merkle_verifier.verify(",
        "var folded_queries = try queries.fold(allocator, self.fold_step);",
        "const folded_evals = try rebuilt.sparse_evaluation.foldLineSubsetsN(",
        ".queries = folded_queries,",
        ".evals = folded_evals,",
    )

    terminal = region(fri, "fn decommitLastLayer(", "fn cloneLayerProof(")
    ordered_once(
        terminal, "FRI terminal polynomial evaluation",
        "if (queries.positions.len != query_evals.len)",
        "for (queries.positions, query_evals) |query, query_eval|",
        "core_utils.bitReverseIndex(",
        "self.last_layer_domain.logSize(),",
        "self.last_layer_poly.evalAtPoint(allocator, QM31.fromBase(x))",
        "if (!query_eval.eql(expected))",
    )

    reconstruct = region(folding, "pub fn computeDecommitmentPositionsAndRebuildEvals(",
                         "pub const FoldLineResult")
    ordered_once(
        reconstruct, "FRI queried value and witness reconstruction",
        "if (query_evals.len != queries.positions.len)",
        "const subset_group = queries.positions[query_idx] >> @intCast(fold_step);",
        "const absolute_pos = subset_start + subset_pos;",
        "queries.positions[subset_query_idx] == absolute_pos",
        "subset[subset_pos] = query_evals[subset_query_idx];",
        "if (witness_idx >= witness_evals.len)",
        "subset[subset_pos] = witness_evals[witness_idx];",
        "witness_idx += 1;",
        "core_utils.bitReverseIndex(subset_start, queries.log_domain_size)",
        ".consumed_witness = witness_idx,",
    )

    polynomial = region(line, "pub fn evalAtPoint(", "pub fn len(")
    ordered_once(
        polynomial, "FRI terminal polynomial evaluation basis",
        "doublings_stack[i] = cur;\n                cur = circle.CirclePoint(QM31).doubleX(cur);",
        "return poly_utils.fold(QM31, self.coeffs, doublings_stack[0..self.log_size]);",
    )


def check_pcs_fri_layer(root: Path) -> None:
    engine = root / "deps/stwo-zig/src/core"
    check_sources(
        (engine / "fri.zig").read_text(),
        (engine / "fri/folding.zig").read_text(),
        (engine / "poly/line.zig").read_text(),
    )
