#!/usr/bin/env python3
"""Exact necessary arithmetic for a *hypothetical* published Circle FRI bound.

The output is deliberately never a native S31 security certificate. Circle
STARKs, Appendix B, Theorem 6 bounds the query error by alpha**s with
alpha = (1 + 1/(2m)) sqrt((N+1)/(N*B)). Remark 26 gives a convenient
commitment-error envelope. Both require a protocol-to-theorem reduction before
they can be used to certify the pinned Zig verifier.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


PAPER = "https://eprint.iacr.org/2024/278.pdf"
M31 = (1 << 31) - 1


@dataclass(frozen=True)
class Candidate:
    trace_rows: int
    blowup: int
    raw_queries: int
    multiplicity: int
    batch_width: int
    fold_step: int = 1
    target_bits: int = 96

    def validate(self) -> None:
        if self.trace_rows < 8 or self.trace_rows & (self.trace_rows - 1):
            raise ValueError("trace_rows must be a power of two at least 8")
        if self.blowup < 2 or self.blowup & (self.blowup - 1):
            raise ValueError("blowup must be a power of two at least 2")
        if self.trace_rows * self.blowup**2 > 1 << 30:
            raise ValueError("S-two circle-domain precondition N*B^2 <= 2^30 fails")
        if not 3 <= self.multiplicity <= self.trace_rows // 2:
            raise ValueError("Circle STARKs Theorem 7 needs 3 <= m <= N/2")
        if self.raw_queries < 1 or self.batch_width < 1 or self.target_bits < 1:
            raise ValueError("queries, batch width, and target bits must be positive")
        if self.fold_step != 1:
            raise ValueError("published single-fold Theorem 6 cannot cover fold_step != 1")
        if alpha_squared(self) >= 1:
            raise ValueError("Johnson agreement parameter alpha must be below 1")


def alpha_squared(c: Candidate) -> Fraction:
    m, n, b = c.multiplicity, c.trace_rows, c.blowup
    return Fraction((2 * m + 1) ** 2 * (n + 1), 4 * m * m * n * b)


def query_meets(c: Candidate, bits: int, queries: int) -> bool:
    """Compare alpha**queries <= 2**-bits using integers, without sqrt/float."""
    a = alpha_squared(c)
    return a.numerator**queries * (1 << (2 * bits)) <= a.denominator**queries


def minimum_queries(c: Candidate) -> int:
    """Exact smallest raw-query count for the *ungrinded* Theorem 6 term."""
    high = 1
    while not query_meets(c, c.target_bits, high):
        high *= 2
    low = high // 2
    while low + 1 < high:
        mid = (low + high) // 2
        if query_meets(c, c.target_bits, mid):
            high = mid
        else:
            low = mid
    return high


def remark26_leading_interval(c: Candidate) -> tuple[Fraction, Fraction]:
    """Outward rational interval for Remark 26's leading envelope term.

    B*sqrt(B) is the only irrational factor. Integer square-root floors and
    ceilings make both endpoints exact. This is one term of a *particular
    upper-bound expression*, not a lower bound on adversarial success.
    """
    n, b, m, width = c.trace_rows, c.blowup, c.multiplicity, c.batch_width
    coefficient = (Fraction(width, 1) - Fraction(2, 3)) * \
        Fraction(2 * m + 1, 2)**7 / 3
    rational = coefficient * b * (n * b)**2 / M31**4
    floor = isqrt(b)
    ceil = floor if floor * floor == b else floor + 1
    return rational * floor, rational * ceil


def assess(c: Candidate) -> dict[str, object]:
    c.validate()
    alpha2 = alpha_squared(c)
    lower, upper = remark26_leading_interval(c)
    target = Fraction(1, 1 << c.target_bits)
    needed = minimum_queries(c)
    return {
        "schema": "s31-pcs-fri-published-preflight-v1",
        "paper": PAPER,
        "profile": vars(c),
        "alpha_squared": f"{alpha2.numerator}/{alpha2.denominator}",
        "ungrinded_query_term_meets_target": query_meets(c, c.target_bits, c.raw_queries),
        "minimum_ungrinded_queries_for_target": needed,
        "remark26_leading_envelope_interval": [
            f"{lower.numerator}/{lower.denominator}",
            f"{upper.numerator}/{upper.denominator}",
        ],
        "remark26_leading_envelope_alone_exceeds_target": lower > target,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "missing": [
            "exact emitted AIR geometry and all published error terms",
            "native lifted PCS/FRI and fold schedule refinement to the paper's IOP",
            "native Merkle encoding/binding and transcript Fiat-Shamir reduction",
            "per-program composition, OODS, and lookup/interaction bounds",
            "adversary budget and theorem-correct proof-of-work accounting",
        ],
        "note": "Necessary paper arithmetic only; no native verifier theorem is claimed.",
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--trace-rows", type=int, default=512)
    p.add_argument("--blowup", type=int, default=2)
    p.add_argument("--raw-queries", type=int, default=70)
    p.add_argument("--multiplicity", type=int, default=3)
    p.add_argument("--batch-width", type=int, default=1)
    p.add_argument("--fold-step", type=int, default=1)
    p.add_argument("--target-bits", type=int, default=96)
    p.add_argument("--require-proven", action="store_true",
                   help="fail closed until native-to-paper obligations are discharged")
    args = p.parse_args(argv)
    try:
        report = assess(Candidate(args.trace_rows, args.blowup, args.raw_queries,
                                  args.multiplicity, args.batch_width,
                                  args.fold_step, args.target_bits))
    except ValueError as exc:
        p.error(str(exc))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
