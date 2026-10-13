"""Fail-closed source contract for the native DEEP row-quotient arithmetic.

The Lean algebra models these expressions. This guard identifies the pinned
Zig call sites; it is not a Zig operational-semantics proof or a degree bound.
"""

from pathlib import Path


def function(source: str, signature: str) -> str:
    if source.count(signature) != 1:
        raise ValueError(f"native quotient function changed: {signature}")
    tail = source.split(signature, 1)[1]
    end = tail.find("\n}")
    if end < 0:
        raise ValueError(f"native quotient function is incomplete: {signature}")
    return tail[:end]


def require(body: str, label: str, *ordered: str) -> None:
    positions = []
    for token in ordered:
        if body.count(token) != 1:
            raise ValueError(f"{label} changed: {token}")
        positions.append(body.index(token))
    if positions != sorted(positions):
        raise ValueError(f"{label} reordered")


def check_sources(constraints: str, rows: str, answers: str,
                  field_batch: str, cm31: str) -> None:
    require(function(constraints, "pub fn complexConjugateLineCoeffs("),
            "conjugate line",
            "if (point.y.eql(point.y.complexConjugate())) return error.DegenerateLine;",
            "const a = value.complexConjugate().sub(value);",
            "const c = point.complexConjugate().y.sub(point.y);",
            "const b = value.mul(c).sub(a.mul(point.y));",
            ".a = alpha.mul(a),", ".b = alpha.mul(b),", ".c = alpha.mul(c),")
    require(function(rows, "fn denominatorInversesInto("),
            "circle denominator",
            "denominators[i] = prx.sub(domain_x).mul(piy).sub(pry.sub(domain_y).mul(pix));",
            "try batchInverseIntoCM31(denominators, denominator_inverses);")
    require(function(rows, "inline fn denominatorValue("),
            "workspace circle denominator",
            "sample.determinant",
            ".sub(sample.piy.mulM31(domain_point.x))",
            ".add(sample.pix.mulM31(domain_point.y));")
    require(function(rows, "fn batchInverseIntoCM31("),
            "zero denominator rejection",
            "fields.batchInverseInPlace(CM31, values, out) catch return error.DivisionByZero;")
    require(function(rows, "pub fn columnLineCoeffs("),
            "sampled weighted line wiring",
            "constraints.complexConjugateLineCoeffs(",
            "batch.point,", "sample_data.sample_value,",
            "sample_data.random_coeff,")
    require(function(rows, "pub fn quotientConstants("),
            "batch coefficient sums",
            "const line_coeffs = try columnLineCoeffs(allocator, sample_batches);",
            "sum_a = sum_a.add(coeff.a);",
            "sum_b = sum_b.add(coeff.b);",
            ".sum_a = sum_a,", ".sum_b = sum_b,")
    require(function(rows, "inline fn evalAt(self: BatchLinearTerm, domain_y: M31) QM31 {"),
            "batch line evaluation",
            "return self.sum_a.mulM31(domain_y).add(self.sum_b);")
    require(function(rows, "pub fn finalizeRowQuotients("),
            "row quotient finalization",
            "const numerator = numerator_sum.sub(linear_term.evalAt(domain_y));",
            "row_accumulator = row_accumulator.add(numerator.mulCM31(denominator_inverse));")
    require(function(answers, "fn buildColumnContributionPlan("),
            "column contribution plan",
            ".batch_index = batch_idx,", ".value_coeff = line_coeffs[coeff_idx].c,")
    require(function(answers, "pub fn friAnswers("),
            "FRI row quotient",
            "const base_value = QM31.fromBase(column_queries[row_idx]);",
            "workspace.batch_numerators[contribution.batch_index].add(",
            "base_value.mul(contribution.value_coeff),",
            "out[row_idx] = try row_evaluation.finalizeRowQuotients(")
    require(function(field_batch, "pub fn batchInverseInPlace("),
            "CM31 batch inverse dispatch",
            "if (comptime F == cm31.CM31 and builtin.cpu.arch == .aarch64",
            "return batchInverseCM31Packed(column, dst, 32);",
            "return batchInverseCM31Packed(column, dst, 16);",
            "return batchInverseCM31Packed(column, dst, 8);",
            "return batchInverseStriped(F, column, dst, 8);",
            "return batchInverseStriped(F, column, dst, 4);",
            "return batchInverseClassic(F, column, dst);")
    require(function(field_batch, "fn batchInverseCM31Packed("),
            "packed CM31 inverse tail",
            "try batchInverseClassic(cm31.CM31, &tail_products, &tail_inverses);")
    require(function(field_batch, "fn batchInverseStriped("),
            "striped inverse tail",
            "try batchInverseClassic(F, dst[n - width .. n], tail_inverses[0..]);")
    require(function(field_batch, "fn batchInverseClassic("),
            "scalar inverse failure",
            "var curr_inverse = try dst[n - 1].inv();")
    require(function(cm31, "pub fn inv(self: CM31) Error!CM31 {"),
            "CM31 zero inverse failure",
            "if (self.isZero()) return Error.DivisionByZero;",
            "return self.invUncheckedNonZero();")


def check_pcs_fri_quotient_algebra(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources((core / "constraints.zig").read_text(),
                  (core / "pcs/quotients/row_evaluation.zig").read_text(),
                  (core / "pcs/quotients/fri_answers.zig").read_text(),
                  (core / "fields/mod.zig").read_text(),
                  (core / "fields/cm31.zig").read_text())
