# Static field powers

[`pow15.s31`](pow15.s31) calls `std::math::pow<15>` on four independent M31
lanes. [`pow15_manual.s31`](pow15_manual.s31) spells out its five multiplication
gates. [`pow15_binary.s31`](pow15_binary.s31) records the earlier six-gate
binary schedule for cost comparison. The checked-in
[`pow15.valid.json`](pow15.valid.json) supplies private inputs and public
results, independently calculated modulo `2^31 - 1`.

The [math-library walkthrough](../../../docs/library.md#static-powers-become-multiplication-circuits)
shows each gate equation, concrete lane values, and the native AIR cost.
The [acceptance gate](../../../tests/acceptance/functional/README.md)
compares the library and handwritten circuits, verifies a proof, and rejects
an altered public result.

[`pow65535_chain4.s31`](pow65535_chain4.s31) applies `pow<65535>` four times
to an eight-lane private array. The compiler saves `x^255`, squares it eight
times, then multiplies by the saved value to obtain `x^65535`. That takes
**19** multiplications per call; the explicit
[`pow65535_binary4.s31`](pow65535_binary4.s31) uses **30** per call. Both
circuits compute `x^(65535^4)` in every lane over `Fₚ`, including `x=0`.
The [assignment](pow65535_chain4.valid.json) includes zero, `p−1`, and
ordinary field values.

| Eight-lane `direct-gate` circuit | Multiplication nodes | Raw QM31 rows | Padded QM31 rows | Preprocessed cells |
| --- | ---: | ---: | ---: | ---: |
| Saved-power chain | 76 | 471 | 512 | 4,096 |
| Explicit binary schedule | 120 | 559 | 1,024 | 8,192 |

The [native acceptance](../../../tests/acceptance/math/power_chain.py)
symbolically derives the output exponent from every emitted multiplication,
recomputes all eight output values independently, proves both circuits,
checks each generated verifier, and rejects a changed public result. It pins
the AIR geometry above. The [Lean chain certificate](../../../../../../formal/s31/S31/Gadgets/Functional/PowerChains.lean)
proves the arithmetic meaning of each star-chain step, and a source test
checks its 19 reference pairs against the compiler's schedule. A single local
run produced 58,843 and 69,354 proof bytes respectively; those byte counts and
proving times are observations, not
portable performance guarantees.

[`pow196605_factor4.s31`](pow196605_factor4.s31) applies $K=3\cdot65535$
four times to the same eight-lane shape. Each call first computes $y=x^3$
using two gates, then reuses the 19-step $y^{65535}$ schedule. The comparison
[native acceptance](../../../tests/acceptance/math/factor_power.py) generates
an explicit left-to-right binary circuit without calling the power library.
It checks every emitted multiplication symbolically, calculates all eight
outputs independently, verifies both native proofs, and rejects changed
public claims. The [assignment](pow196605_factor4.valid.json) includes zero,
one, and $p-1$.

| Four-call eight-lane circuit | Multiplication nodes | Raw QM31 rows | Padded QM31 rows | Preprocessed cells |
| --- | ---: | ---: | ---: | ---: |
| Factor reuse | 84 | 487 | 512 | 4,096 |
| Explicit binary | 128 | 575 | 1,024 | 8,192 |

The first local run produced 56,111 and 70,402 proof bytes respectively.
These are proof-size observations for the pinned source and compiler. The
[Lean schedule certificate](../../../../../../formal/s31/S31/Gadgets/Functional/PowerChains.lean)
proves that the 21-step factor chain reaches $x^{196605}$ for every M31 input.

The [functional version](pow196605_functional4.s31) defines `power(v)` and
`twice(v)`, then calls `twice(twice(x))`. Its four calls specialize into the
same 84 multiplication gates, with identical input and public-output
boundaries, as the direct source. The [source test](../../../tests/python/functional/test_power_chains.py)
compares every gate's operation and predecessor indices after erasing source
names and checks the example's eight independent output values. Function
calls themselves add no circuit gate.
