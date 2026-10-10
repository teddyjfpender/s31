# Functional native acceptance

`library.py` builds functional and explicitly first-order forms of the
[worked quadratic](../../../examples/arithmetic/functional_poly4.s31), the
[curried sum](../../../examples/arithmetic/curried_sum.s31), one generated
matrix program, a [static tuple](../../../examples/arithmetic/tuple_square_sum.s31),
the [five-gate static power](../../../examples/arithmetic/powers/pow15.s31),
and a three-Poseidon2 hash tree. It compares normalized relation
IR and the native compiler's circuit/AIR cost report, then proves one concrete
input for each functional form. The independent arithmetic and Poseidon2
reference calculate expected public results; changing a result must fail
native verification. The exact geometry baselines detect unexpected cost
changes, while the direct-form comparison tests zero overhead from closures
and tuple structure.
The static-power case compares the compiler's addition chain to an explicit
five-multiply circuit and pins the raw and padded AIR geometry. It accepts a
native proof and rejects a changed public power value.
The gate also reads the sealed standard-library lock and semantic-equation
report, checking that every compiler library source is hashed and every
normalized node appears in the report.

These are representative executable release gates, not a proof of compiler
correctness for all source programs. The larger generated source corpus lives
in [`../../python/generated/`](../../python/generated/README.md).

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/functional/library.py
```

`product_control.py` separately builds the nested
[`record_choice.s31`](../../../examples/control/record_choice.s31) and its
fieldwise form under `direct-gate`. It requires identical relation IR and
complete AIR geometry, then proves both selector values through the typed
public record ABI and checks independent values and changed-claim rejection:

```sh
python3 src/frontends/s31/tests/acceptance/functional/product_control.py
```
