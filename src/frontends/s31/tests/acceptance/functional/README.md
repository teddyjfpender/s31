# Functional native acceptance

`library.py` builds functional and explicitly first-order forms of the
[worked quadratic](../../../examples/arithmetic/functional_poly4.s31), the
[curried sum](../../../examples/arithmetic/curried_sum.s31), one generated
matrix program and a three-Poseidon2 hash tree. It compares normalized relation
IR and the native compiler's circuit/AIR cost report, then proves one concrete
input for each functional form. The independent arithmetic and Poseidon2
reference calculate expected public results; changing a result must fail
native verification. The exact geometry baselines detect unexpected cost
changes, while the direct-form comparison tests zero overhead from closures.

These are representative executable release gates, not a proof of compiler
correctness for all source programs. The larger generated source corpus lives
in [`../../python/generated/`](../../python/generated/README.md).

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/functional/library.py
```
