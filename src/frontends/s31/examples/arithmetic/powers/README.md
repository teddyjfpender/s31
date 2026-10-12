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
the AIR geometry above. A single local run produced 58,843 and 69,354 proof
bytes respectively; those byte counts and proving times are observations, not
portable performance guarantees.
