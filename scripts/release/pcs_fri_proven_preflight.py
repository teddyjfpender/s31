#!/usr/bin/env python3
"""Exact necessary arithmetic for a *hypothetical* published Circle FRI bound.

The output is deliberately never a native S31 security certificate. Circle
STARKs, Appendix B, Theorem 6 bounds the query error by alpha**s with
alpha = (1 + 1/(2m)) sqrt((N+1)/(N*B)). Remark 26 gives a convenient
commitment-error envelope. The native M31 channel reduces each 32-bit hash
word modulo 2**31-1 before the query sampler masks its low bits. We separately
bound that small ideal-oracle sampling bias. All terms still require a
protocol-to-theorem reduction before certifying the pinned Zig verifier.
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


def masked_m31_max_set_bias(log_domain_size: int) -> Fraction:
    """Exact largest excess over uniform for any set of masked query indices.

    A uniform u32 reduced modulo p=2**31-1 has three preimages for residues
    0 and 1 and two for every other residue. For k>=2, masking to 2**k
    positions adds one preimage each at indices 0 and 1, removes two at the
    last index, and leaves the rest at their uniform baseline. At k=1 the
    positive excess is one preimage; at k=0 there is only one position.
    The bound is conditional on independent uniform 256-bit hash outputs.
    """
    if not 0 <= log_domain_size <= 31:
        raise ValueError("M31-masked query domain must have 0..31 bits")
    if log_domain_size == 0:
        return Fraction(0)
    return Fraction(1 if log_domain_size == 1 else 2, 1 << 32)


def sqrt_upper(value: Fraction, precision: int = 192) -> Fraction:
    """Outward dyadic upper endpoint, computed with integer square root."""
    if value < 0 or precision < 1:
        raise ValueError("square-root interval needs nonnegative input")
    scale = 1 << precision
    floor = isqrt((value.numerator * scale * scale) // value.denominator)
    lower = Fraction(floor, scale)
    return lower if lower * lower == value else Fraction(floor + 1, scale)


def ideal_m31_masked_query_upper(c: Candidate) -> Fraction:
    """Conservative one-query agreement under the ideal native M31 channel.

    The paper's alpha bounds the density of a fixed good set under uniform
    positions. Any set's mass under the native reduced-and-masked draw is at
    most its uniform density plus the exact positive variation below. This
    is not a Fiat-Shamir or implementation-security bound.
    """
    domain_log = (c.trace_rows * c.blowup).bit_length() - 1
    return sqrt_upper(alpha_squared(c)) + masked_m31_max_set_bias(domain_log)


def minimum_ideal_m31_masked_queries(c: Candidate) -> int:
    """Sufficient count for the bias-adjusted ideal query term only."""
    upper = ideal_m31_masked_query_upper(c)
    if upper >= 1:
        raise ValueError("bias-adjusted agreement bound must be below one")

    def meets(queries: int) -> bool:
        return upper.numerator**queries * (1 << c.target_bits) <= \
            upper.denominator**queries

    high = 1
    while not meets(high):
        high *= 2
    low = high // 2
    while low + 1 < high:
        mid = (low + high) // 2
        if meets(mid):
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
    masked_upper = ideal_m31_masked_query_upper(c)
    masked_needed = minimum_ideal_m31_masked_queries(c)
    masked_bias = masked_m31_max_set_bias((c.trace_rows * c.blowup).bit_length() - 1)
    return {
        "schema": "s31-pcs-fri-published-preflight-v1",
        "paper": PAPER,
        "profile": vars(c),
        "alpha_squared": f"{alpha2.numerator}/{alpha2.denominator}",
        "ungrinded_query_term_meets_target": query_meets(c, c.target_bits, c.raw_queries),
        "minimum_ungrinded_queries_for_target": needed,
        "ideal_m31_masked_max_set_bias": f"{masked_bias.numerator}/{masked_bias.denominator}",
        "ideal_m31_masked_agreement_upper": f"{masked_upper.numerator}/{masked_upper.denominator}",
        "minimum_ideal_m31_masked_queries_for_target": masked_needed,
        "ideal_m31_masked_query_term_meets_target": c.raw_queries >= masked_needed,
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
