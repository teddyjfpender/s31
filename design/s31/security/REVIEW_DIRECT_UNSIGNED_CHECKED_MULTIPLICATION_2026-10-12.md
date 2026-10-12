# Independent review: direct unsigned checked multiplication

Date: 2026-10-12. Scope: the arithmetic-only `checkedUnsignedArithmetic`
shortcut in [`integer_multiply.zig`](../../../src/frontends/s31/language/gadgets/integer_multiply.zig)
and its call site, input bit provenance, result bit cache, and direct topology
check in [`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig).
This is a source and integer-bound review. It is not a proof of the entire
Python-to-AIR compiler, the Stwo PCS/FRI implementation, or cryptographic
soundness of a proof transcript.

## Finding

I found no false witness or honest rejection in the reviewed unsigned checked
lowering. The conclusion is conditional on the compiler supplying Boolean
operand bits that are bound to the input limbs, as its current call site does.
The public gadget API accepts those bits as an assumption; it does not
independently reconstruct the limbs a second time.

Let `W` be 8, 16, 32, 64, or 128, `d` be 8 for `W <= 32` and 13 otherwise,
`B = 2^d`, and `N = ceil(W/d)`. Each input digit is packed from proved Boolean
bits. The final digit has only `W - d(N-1)` bits. For low columns
`k = 0, ..., N-1`, the gadget constrains

```text
C_k + sum_(i+j=k) a_i*b_j = D_k + B*C_(k+1),    C_0 = 0.
```

Each `D_k` has exactly `d` Boolean bits; each outgoing carry has the bounded
Boolean bit count below. The gadget also constrains `C_N = 0`, every bit in
`[W, N*d)` of the low digit canvas to zero, and each omitted source
coefficient `sum_(i+j=k) a_i*b_j = 0` for `k = N, ..., 2N-2`.
The latter coefficients are nonnegative integers below the M31 prime, so
field-zero forces integer-zero. Telescoping the low equations then yields
`A*B = sum_(k<N) D_k*B^k < 2^W`. The returned low limbs pack precisely the
first `W` proved output bits. This covers overflow appearing only in a high
source coefficient, overflow carried from the last low column, and spill
inside a partial 13-bit top digit.

## Bounds checked independently

I evaluated the all-maximum digit recurrence for each supported width. The
maximum column sum includes its incoming carry. The maximum omitted high
coefficient omits carry, matching the separate high-coefficient constraints.

| `W` | `d` | `N` | top digit bits | maximum column sum | maximum carry | carry bits | maximum omitted high coefficient |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 8 | 1 | 8 | 65,025 | 254 | 8 | none |
| 16 | 8 | 2 | 8 | 130,304 | 509 | 9 | 65,025 |
| 32 | 8 | 4 | 8 | 260,864 | 1,019 | 10 | 195,075 |
| 64 | 13 | 5 | 12 | 268,394,496 | 32,763 | 15 | 201,269,252 |
| 128 | 13 | 10 | 11 | 603,897,856 | 73,718 | 17 | 503,181,321 |

The largest column sum and high coefficient are both below
`p = 2,147,483,647`. Even allowing any value representable by the largest
carry bit count, the low-column left side is at most
`10*8191^2 + (2^17-1) = 671,055,881` and its right side at most
`8191 + 8192*(2^17-1) = 1,073,741,823`, also below `p`.
Consequently none of these field equalities can mask a different integer
equation by modular wrap. The declared carry bit counts accommodate every
honest product, including the full and wrapping paths that share the
recurrence.

## Compiler and topology checks

`BitCache.getIntegerArithmetic` either retrieves previously proved bits for
the same word and limb width or calls `decomposeWordArithmetic`, which gives
each fresh bit a Boolean self-product and equates its packed value to the raw
limb. The input admission path similarly decomposes eligible direct u16
inputs; `int_view` retains the raw wire. After multiplication,
`BitCache.remember` records only the gadget's Boolean `low_bits`, which are
packed into the returned result limbs. Reuse in a later integer operation
therefore preserves the word-to-bits relation. The cache key includes the
variable index and limb width.

In `NoValue` mode, witness values read by the gadget are replaced with zero
only for hints. Loop counts, branch choices, constants, and gate operations
depend on `W`, `d`, `N`, and the mode, not on those values. Every Boolean
self-product and zero-assertion self-loop gives its new wire one producing
gate. The direct compiler calls `firstYieldViolation` and rejects a topology
with any variable yielded other than once. This checks the circuit's
single-producer shape; it does not by itself establish the AIR/PCS proof.

## Adversarial cases to keep in the native matrix

The gadget tests already cover a u16 overflow carried out of the last low
column (`255*258`), a u16 overflow entirely in a high coefficient
(`256*256`), and a u64 spill at bit 64 (`2^63*2`). Additional useful cases:

| Case | Expected result | Failure mode targeted |
| --- | --- | --- |
| `u64: 2^52 * 2^13` | reject | Nonzero omitted high coefficient with zero low carry and no low-canvas spill. |
| `u128: 2^117 * 2^13` | reject | Same high-coefficient case at ten 13-bit digits. |
| `u128: 2^127 * 2` | reject | Spill in the partial top digit at the 128-bit boundary. |
| `u128: (2^128-1) * 1` | accept | Honest maximum result and top digit packing. |
| `u64/u128: max * max` in wrapping/full mode | accept modulo width / exact full product | Maximum carry recurrence and final high digit. |

These cases test implementation coverage. They do not replace the bounded
integer argument above or the independent compiler correspondence proof.
