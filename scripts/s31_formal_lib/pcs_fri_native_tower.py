"""Fail-closed source guard for the tower formulas modeled in Lean.

This pins call sites and operation order; it is not a Zig semantics proof.
"""

from pathlib import Path

from .pcs_fri_quotient_algebra import require


def function(source: str, signature: str) -> str:
    if source.count(signature) != 1:
        raise ValueError(f"native tower function changed: {signature}")
    start = source.index(signature) + len(signature)
    depth = 1
    for i in range(start, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return source[start:i]
    raise ValueError(f"native tower function is incomplete: {signature}")


def check_sources(cm31: str, qm31: str, circle: str) -> None:
    require(function(cm31, "pub inline fn mul(lhs: CM31, rhs: CM31) CM31 {"),
            "CM31 Karatsuba",
            "const ac = lhs.a.mul(rhs.a);",
            "const bd = lhs.b.mul(rhs.b);",
            "const cross = lhs_sum.mul(rhs_sum);",
            "imaginary = cross.sub(ac);",
            "imaginary = imaginary.sub(bd);",
            ".a = ac.sub(bd),",
            ".b = imaginary,")
    require(function(cm31, "pub inline fn square(self: CM31) CM31 {"),
            "CM31 square",
            "const a2 = self.a.square();",
            "const b2 = self.b.square();",
            "const ab = self.a.mul(self.b);",
            ".a = a2.sub(b2),",
            ".b = ab.add(ab),")
    require(function(qm31, "fn mulByR(value: CM31) CM31 {"),
            "QM31 tower parameter",
            "const two_a = value.a.add(value.a);",
            "const two_b = value.b.add(value.b);",
            ".a = two_a.sub(value.b),",
            ".b = value.a.add(two_b),")
    require(function(qm31, "pub inline fn fromBase(x: M31) QM31 {"),
            "QM31 base embedding",
            ".c0 = CM31.fromBase(x),", ".c1 = CM31.zero()")
    require(function(qm31, "pub inline fn isBase(self: QM31) bool {"),
            "QM31 base fast-path guard",
            "return self.c0.b.isZero() and self.c1.isZero();")
    require(function(qm31, "pub inline fn square(self: QM31) QM31 {"),
            "QM31 square",
            "if (self.isBase()) return QM31.fromBase(self.c0.a.square());",
            "const a2 = self.c0.square();",
            "const b2 = self.c1.square();",
            "const ab = self.c0.mul(self.c1);",
            ".c0 = a2.add(mulByR(b2)),",
            ".c1 = ab.add(ab),")
    require(function(circle, "pub inline fn isOnCircle(self: Self) bool {"),
            "native circle relation",
            "const lhs = self.x.square().add(self.y.square());",
            "return lhs.eql(F.one());")
    require(function(circle, "pub fn secureFieldPointFromRandomSeedChecked(t: QM31) QM31.Error!CirclePointQM31 {"),
            "native OOD rational map",
            "const t_square = t.square();",
            "const one_plus_t_square_inv = try t_square.add(QM31.one()).inv();",
            "const x = QM31.one().sub(t_square).mul(one_plus_t_square_inv);",
            "const y = t.add(t).mul(one_plus_t_square_inv);",
            "return .{ .x = x, .y = y };")


def check_pcs_fri_native_tower(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources((core / "fields/cm31.zig").read_text(),
                  (core / "fields/qm31.zig").read_text(),
                  (core / "circle.zig").read_text())
