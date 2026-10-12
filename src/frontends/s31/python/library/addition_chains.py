"""Deterministic, bounded multiplication schedules for static field powers.

A chain starts at exponent one. Each next exponent adds the previous maximum
and an earlier exponent, so its multiplication uses two already built circuit
values. Search is optional: the binary schedule is always a valid fallback.
"""

from __future__ import annotations

from functools import lru_cache

MAX_SEARCH_EXPONENT = 255
MAX_SEARCH_STATES = 50_000
MAX_REUSED_FACTOR = 31


def binary_chain(exponent: int) -> tuple[int, ...]:
    """The old left-to-right binary schedule, retained as the cost ceiling."""
    if exponent < 1:
        raise ValueError("addition chains require a positive exponent")
    chain = [1]
    for bit in bin(exponent)[3:]:
        chain.append(chain[-1] * 2)
        if bit == "1":
            chain.append(chain[-1] + 1)
    return tuple(chain)


@lru_cache(maxsize=32)
def _mersenne_chain(bits: int) -> tuple[int, ...]:
    """Build `2**bits - 1` by reusing a shorter all-ones power.

    For even `bits = 2*m`, let `a = 2**m - 1`. Starting with `x**a`,
    square `m` times and multiply by the saved `x**a` to obtain
    `x**(a*2**m + a) = x**(2**(2*m) - 1)`. Odd lengths append a square
    and a multiply by `x`. Every step remains a star-chain step, so the
    ordinary `pow_static` lowering can use it without a new circuit op.
    """
    if bits < 1:
        raise ValueError("Mersenne chain needs at least one bit")
    if bits == 1:
        return (1,)
    if bits & 1:
        chain = _mersenne_chain(bits - 1)
        return (*chain, chain[-1] * 2, chain[-1] * 2 + 1)
    half = bits // 2
    chain = list(_mersenne_chain(half))
    saved = chain[-1]
    for _ in range(half):
        chain.append(chain[-1] * 2)
    chain.append(chain[-1] + saved)
    return tuple(chain)


def _large_mersenne_candidate(exponent: int) -> tuple[int, ...] | None:
    """Handle `(2**k - 1) * 2**shift` above the bounded optimal search."""
    odd = exponent
    shift = 0
    while odd > 1 and odd & 1 == 0:
        odd >>= 1
        shift += 1
    if odd <= 1 or odd & (odd + 1):
        return None
    chain = list(_mersenne_chain(odd.bit_length()))
    for _ in range(shift):
        chain.append(chain[-1] * 2)
    return tuple(chain)


def _factor_candidate(exponent: int, factor: int) -> tuple[int, ...]:
    """Compute ``x**factor`` once, then run a quotient chain on that value.

    Scaling every quotient exponent by ``factor`` preserves the star-chain
    invariant: each step uses the previous result and one saved power. Keep
    the large quotient search bounded to binary and the Mersenne construction;
    recursively factoring quotients would make compiler time input-dependent
    on the number of divisors.
    """
    quotient = exponent // factor
    prefix = exponent_chain(factor)
    suffix = (exponent_chain(quotient) if quotient <= MAX_SEARCH_EXPONENT
              else binary_chain(quotient))
    if quotient > MAX_SEARCH_EXPONENT:
        mersenne = _large_mersenne_candidate(quotient)
        if mersenne is not None and len(mersenne) < len(suffix):
            suffix = mersenne
    return (*prefix, *(factor * power for power in suffix[1:]))


@lru_cache(maxsize=256)
def exponent_chain(exponent: int) -> tuple[int, ...]:
    """Find a shorter star chain under fixed search limits, or use binary.

    Star-chain step `e -> e + prior` uses the current result and an earlier
    cached power. Iterative deepening checks fewer multiplications first.
    The state cap bounds compiler work and never changes field semantics.
    """
    baseline = binary_chain(exponent)
    if exponent > MAX_SEARCH_EXPONENT:
        best = baseline
        candidate = _large_mersenne_candidate(exponent)
        if candidate is not None and len(candidate) < len(best):
            best = candidate
        for factor in range(3, MAX_REUSED_FACTOR + 1, 2):
            if exponent % factor == 0:
                candidate = _factor_candidate(exponent, factor)
                if len(candidate) < len(best):
                    best = candidate
        return best
    if len(baseline) <= 2:
        return baseline

    visited = 0
    exhausted = False

    def search(chain: tuple[int, ...], remaining: int) -> tuple[int, ...] | None:
        nonlocal visited, exhausted
        if exhausted:
            return None
        visited += 1
        if visited > MAX_SEARCH_STATES:
            exhausted = True
            return None
        current = chain[-1]
        if current == exponent:
            return chain
        if remaining == 0 or current << remaining < exponent:
            return None
        for prior in reversed(chain):
            next_power = current + prior
            if next_power > exponent:
                continue
            found = search(chain + (next_power,), remaining - 1)
            if found is not None:
                return found
            if exhausted:
                break
        return None

    minimum_steps = (exponent - 1).bit_length()
    for steps in range(minimum_steps, len(baseline) - 1):
        shorter = search((1,), steps)
        if shorter is not None:
            return shorter
        if exhausted:
            break
    return baseline
