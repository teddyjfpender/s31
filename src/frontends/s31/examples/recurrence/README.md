# Functional recurrence with no chip cost

[`functional_step16.s31`](functional_step16.s31) passes a closure through a
higher-order helper. Its body calls the fixed 16-round recurrence `step`.
The [explicit form](functional_step16_manual.s31) calls `iterate` directly.
Both sources must normalize to the same single `repeat` node, select the same
four-lane repeated-step chip under `direct-chip`, and have exactly the same
AIR geometry and FRI settings. The verified [assignment](functional_step16.valid.json)
starts at `[0, 1, 2, 7]`; each lane applies `v ↦ v²+7 mod (2³¹−1)` sixteen
times.

The [functional acceptance gate](../../tests/acceptance/acceptance_functional_core.py)
builds both packages, compares canonical IR and cost components, generates a
native proof for the functional source, and checks that a changed public
result is rejected.
