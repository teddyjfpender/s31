# Fixed-width division examples

`std::int::div_rem(a, b)` produces a statically shaped pair of circuit values.
The normalized relation has one `int_div_rem` node whose first half is the
quotient and second half is the remainder. Using both values does not create
a second division gadget. The operation accepts equally typed `u8` through
`u128` and `i8` through `i128` operands.
`std::int::div_checked(a, b)` and `std::int::rem_checked(a, b)` expose one
result each. Use `div_rem` when both values are needed so the division relation
is emitted once.

| Source | Hand calculation | Public result |
| --- | --- | --- |
| [`u8_div_rem.s31`](u8_div_rem.s31) | `201 = 14·14 + 5` | `[14, 5]` |
| [`u16_div_rem.s31`](u16_div_rem.s31) | `60000 = 233·257 + 119` | `[233, 119]` |
| [`u32_div_rem.s31`](u32_div_rem.s31) | `123456 = 411·300 + 156` | `[411, 0, 156, 0]` |
| [`u64_div_rem.s31`](u64_div_rem.s31) | `0x123456789abcdef0 = 0x123444445678·0x10001 + 0x8878` | four quotient limbs followed by four remainder limbs |
| [`i8_div_rem.s31`](i8_div_rem.s31) | `-7 = (-2)·3 + (-1)` | `[254, 255]`, two's-complement bytes |
| [`i16_div_rem.s31`](i16_div_rem.s31) | `-32768 = (-10922)·3 - 2` | `[54614, 65534]`, two's-complement words |
| [`u128_div_quotient.s31`](u128_div_quotient.s31) | `(2^128-1)/(2^64+1) = 2^64-1` | the quotient's eight limbs |
| [`i128_div_quotient.s31`](i128_div_quotient.s31) | `MIN / 2 = -2^126` | the quotient's eight limbs |

The current public ABI allows eight words. A 128-bit quotient and remainder
occupy sixteen words together, so the last example exposes only the quotient;
the internal remainder and its constraints still exist in the proof.
Division by zero and signed `MIN / -1` make the circuit unsatisfiable.

The 8- and 16-bit examples, plus unsigned `u32`, `u64`, and `u128`, use `--lowering direct-gate`. This profile proves
each input and intermediate bound with Boolean bits and emits arithmetic-only
AIR gates; it does not require the 65,536-cell range table. Signed `i32`, `i64`, and `i128`
currently use `--lowering sparse-wide-gate`, whose limb and carry checks use lookup and
equality components. See the [worked constraints](../../../docs/fixed-width-integers.md#division-and-remainder-by-hand)
for the equations each profile proves.
