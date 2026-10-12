# Functional recurrence with no chip cost

[`functional_step16.s31`](functional_step16.s31) passes the named step
function as a static `Fn` value to a higher-order helper that calls
`iterate<16>`.
The [explicit form](functional_step16_manual.s31) calls `iterate` directly.
[`captured_step16.s31`](captured_step16.s31) instead passes a closure that
captures the compile-time constant 7; its
[explicit form](captured_step16_manual.s31) uses a named step.
[`returned_mix4_3.s31`](returned_mix4_3.s31) returns a coupled-lane `mix4`
step from a factory and applies it for three rounds; its
[explicit form](returned_mix4_3_manual.s31) names the step directly.
Both square-step sources must normalize to the same single `repeat` node as their
explicit counterpart, select the same
four-lane repeated-step chip under `direct-chip`, and have exactly the same
AIR geometry and FRI settings. The verified
[assignment](functional_step16.valid.json)
starts at `[0, 1, 2, 7]`; each lane applies `v ↦ v²+7 mod (2³¹−1)` sixteen
times.
The returned `mix4` source must likewise normalize to the same relation as
its direct form; its four lanes interact because each step adds their sum.

The [functional acceptance gate](../../tests/acceptance/acceptance_functional_core.py)
builds both square-step sources and their explicit forms, compares canonical
IR and cost components, generates native proofs, and checks that changed
public results are rejected. The
[functional library gate](../../tests/acceptance/functional/library.py)
proves the returned `mix4` source against its direct form with 344 raw and
512 padded QM31 operation rows. The
[worked explanation](../../docs/functional-language.md) includes the first
two square rounds and three mixed rounds by hand, with their constraints.
