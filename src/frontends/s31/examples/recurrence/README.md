# Functional recurrence with no chip cost

[`functional_step16.s31`](functional_step16.s31) passes the named step
function as a static `Fn` value to a higher-order helper that calls
`iterate<16>`.
The [explicit form](functional_step16_manual.s31) calls `iterate` directly.
[`captured_step16.s31`](captured_step16.s31) instead passes a closure that
captures the compile-time constant 7; its
[explicit form](captured_step16_manual.s31) uses a named step.
Each functional source must normalize to the same single `repeat` node as its
explicit counterpart, select the same
four-lane repeated-step chip under `direct-chip`, and have exactly the same
AIR geometry and FRI settings. The verified
[assignment](functional_step16.valid.json)
starts at `[0, 1, 2, 7]`; each lane applies `v ↦ v²+7 mod (2³¹−1)` sixteen
times.

The [functional acceptance gate](../../tests/acceptance/acceptance_functional_core.py)
builds each source and its explicit form, compares canonical IR and cost
components, generates native proofs for both functional sources, and checks
that changed public results are rejected. The
[worked explanation](../../docs/functional-language.md) includes the first
two rounds by hand and states the constraint on each lane.
