"""Source contract for the pinned verifier's algebraic FRI fold path.

The native regression independently evaluates the same field formula.  This
guard ties that regression to the verifier call sites and coordinate/challenge
selection.  It is not a Zig semantics or FRI proximity proof.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(fft: str, folding: str, fri: str) -> None:
    butterfly = region(fft, "pub fn ibutterfly(", "fn addF(")
    ordered_once(
        butterfly, "FRI inverse butterfly algebra",
        "const tmp = v0.*;",
        "v0.* = addF(F, tmp, v1.*);",
        "v1.* = mulByBase(F, subF(F, tmp, v1.*), itwid);",
    )

    line = region(folding, "pub fn foldLineSingleStep(", "/// Performs `n_folds`")
    ordered_once(
        line, "FRI line fold formula",
        "fillBitReversedCosetCoordinate(x_values, domain.coset(), .x);",
        "try fields.batchInverseInPlace(M31, x_values, inv_x_values);",
        "const inv_x = inv_x_values[i];",
        "fft.ibutterfly(QM31, &f0, &f1, inv_x);",
        "folded_values[i] = f0.add(alpha.mul(f1));",
    )

    many = region(folding, "pub fn foldLineNWithWorkspace(", "pub fn foldLineWithWorkspace(")
    ordered_once(
        many, "FRI successive challenge powers",
        "var current_alpha = alpha;",
        "foldLineSingleStep(allocator, eval, domain, current_alpha, workspace);",
        "const prev_domain = result.domain;",
        "current_alpha = current_alpha.square();",
        "foldLineSingleStep(allocator, prev_values, prev_domain, current_alpha, workspace);",
    )

    circle = region(folding, "pub fn foldCircleIntoLineWithWorkspace(",
                    "pub fn foldCircleColumnsIntoLineWithWorkspace(")
    ordered_once(
        circle, "FRI circle fold formula",
        "const alpha_sq = alpha.square();",
        "fillBitReversedCosetCoordinate(py_values, src_domain.half_coset, .y);",
        "try fields.batchInverseInPlace(M31, py_values, inv_py_values);",
        "const inv_py = inv_py_values[i];",
        "fft.ibutterfly(QM31, &f0_px, &f1_px, inv_py);",
        "const f_prime = alpha.mul(f1_px).add(f0_px);",
        "dst[i] = dst[i].mul(alpha_sq).add(f_prime);",
    )

    sparse_line = region(folding, "pub fn foldLineSubsetsN(", "pub fn foldCircleSubsets(")
    ordered_once(
        sparse_line, "FRI sparse line fold helper call",
        "pub fn foldLineSubsetsN(",
        "const folded = try foldLineNWithWorkspace(",
    )
    sparse_circle = region(folding, "pub fn foldCircleSubsets(", "pub const ComputeDecommitmentResult")
    ordered_once(
        sparse_circle, "FRI sparse circle fold helper calls",
        "pub fn foldCircleSubsets(",
        "try foldCircleIntoLineWithWorkspace(",
        "fold_alpha.square(),",
    )

    verifier = region(fri, "fn decommitImpl(", "pub const FoldLineWorkspace")
    ordered_once(
        verifier, "FRI verifier fold call sites",
        "first_layer_sparse_eval.foldCircleSubsets(\n                allocator,\n                self.first_layer.folding_alpha,",
        "layer.verifyAndFoldImpl(",
        "rebuilt.sparse_evaluation.foldLineSubsetsN(\n                allocator,\n                self.folding_alpha,",
    )


def check_pcs_fri_fold(root: Path) -> None:
    engine = root / "deps/stwo-zig/src/core"
    check_sources(
        (engine / "fft.zig").read_text(),
        (engine / "fri/folding.zig").read_text(),
        (engine / "fri.zig").read_text(),
    )
