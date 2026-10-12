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
