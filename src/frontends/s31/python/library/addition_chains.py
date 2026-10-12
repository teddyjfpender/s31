"""Deterministic, bounded multiplication schedules for static field powers.

A chain starts at exponent one. Each next exponent adds the previous maximum
and an earlier exponent, so its multiplication uses two already built circuit
values. Search is optional: the binary schedule is always a valid fallback.
"""

from __future__ import annotations

from functools import lru_cache

MAX_SEARCH_EXPONENT = 255
MAX_SEARCH_STATES = 50_000


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


@lru_cache(maxsize=256)
def exponent_chain(exponent: int) -> tuple[int, ...]:
    """Find a shorter star chain under fixed search limits, or use binary.

    Star-chain step `e -> e + prior` uses the current result and an earlier
    cached power. Iterative deepening checks fewer multiplications first.
    The state cap bounds compiler work and never changes field semantics.
    """
    baseline = binary_chain(exponent)
    if exponent > MAX_SEARCH_EXPONENT or len(baseline) <= 2:
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
