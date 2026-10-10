# Fixed-width division and remainder

Status: implemented in the text frontend, independent oracle, generic circuit
path, and native prover/verifier, 2026-10-10. The Lean model proves the
integer relation and bounded-column theorem; production Zig gate emission is
not yet formally refined to that model.

## Source contract

`std::int::div_rem(a, b)` takes two values of the same nominal integer type
and returns `(quotient, remainder)` of that type. It is one relation operation
with two results, so using both results does not duplicate the expensive
division proof. `std::int::div_checked` and `std::int::rem_checked` select
one result each. Division by zero is unsatisfiable. Unsigned division obeys

$$a=q b+r,\qquad 0\le r<b.$$

Signed division rounds toward zero. The remainder is zero or has the
dividend's sign, and its absolute value is smaller than the divisor's
absolute value. `MIN / -1` is unsatisfiable because its mathematical quotient
is outside the result type. The signed and unsigned contracts apply to all
five widths from 8 through 128 bits; the operation never interprets an M31
field element as an integer.

## Circuit construction

First prove every input, quotient, and remainder limb belongs to its declared
width. The generic wide circuit uses `u16` lookups; its byte scalars also
prove the tighter bound below 256.
Split each 16-bit limb into two bytes, constraining the low byte and using
the bounded limb plus reconstruction to bound the high byte. For a width
`W`, let `K=W/8` be the number of bytes. A direct convolution proves the
entire integer equation, including the high product half:

$$c_j+\sum_{i=0}^{K-1}q_i b_{j-i}+[j<K]r_j
   =[j<K]a_j+256c_{j+1},\qquad 0\le j<2K,$$

where out-of-range digit indices contribute zero, `c_0=0`, and
`c_{2K}=0`. Each carry is range checked. For `K<=16`, even the conservative
upper bound `16*255^2+65535+255=1,106,190` on a column's left side is below
the M31 modulus. The right side is below `255+256*65535=16,776,960`, also
below the modulus. Thus a field equality in each column is an integer
equality; a witness cannot borrow a multiple of the field modulus or discard
high product bytes.

Prove `r<b` with `b-r-1` in bounded base-`2^16` digits, Boolean borrows,
and final borrow zero. This strict inequality alone
excludes `b=0`. Together, the convolution and comparison determine the
unique Euclidean quotient and remainder. A witness generator may calculate
`q` and `r`, but the verifier accepts only the constrained equations.

For signed inputs, prove the sign bits, derive bounded magnitudes, apply the
same unsigned relation to magnitudes, then conditionally negate the quotient
and remainder according to the input signs. A positive quotient must have
its top sign bit clear; this excludes `MIN / -1`. A negative quotient may
reach exactly `MIN`. The sign selection and each conditional negation need
explicit Boolean and limb equations; witness-time branching alone is not a
constraint.

## Direct byte circuit

The `direct-gate` profile can prove the `u8` and `i8` division examples
without an Eq component, 16-bit converter, or `seq_16` range table. Each byte
wire is reconstructed from eight Boolean bits. Each bit is produced by a
single self-product gate `b*b=b`; this is exactly the Boolean equation
`b(b-1)=0` without a separate guessed-bit gate. A zero assertion is an
arithmetic self-loop, `anchor + value = anchor`, with one producing gate for
the anchor. This enforces `value = 0` in the direct arithmetic AIR.

For the unsigned relation, the circuit proves

$$0\le n,d,q,r,\delta<256,\qquad qd+r=n,\qquad d=r+1+\delta.$$

The largest possible left side of the product equation is
`255*255+255=65,280`; the comparison's right side is at most 511. Both are
smaller than the M31 modulus. The field equalities therefore prove exact
integer equalities and `r<d`, including the zero-divisor exclusion. The
compiler admits this profile only when each raw `u16` input flows exclusively
through an 8-bit integer view; the source type and public ABI remain bound in
the canonical relation and verification key.

For signed bytes, the sign comes from the proved high bit. Conditional
two's-complement negation proves a byte output and Boolean carry using
arithmetic gates. The positive-quotient sign check rejects `MIN / -1`.
## Direct 16-bit circuit

The arithmetic-only path also handles `u16` and `i16`. Every source word is
reconstructed from sixteen Boolean bits. The divider splits each bounded
word into two proved bytes, proves `q*d+r=n` over all four base-256 product
columns, and proves `d-r-1>=0` with two bounded borrow columns. Quotient and
remainder words are reconstructed from their two bytes; every carry is
bounded to 16 bits. The terminal product carry and terminal comparison
borrow are constrained to zero.

For `60000 / 257`, the unique pair is `q=233, r=119`. In little-endian
bytes, `n=[96,234]`, `d=[1,1]`, `q=[233,0]`, and `r=[119,0]`:

| Product column | Exact integer equation | Outgoing carry |
| --- | --- | ---: |
| 0 | `233*1 + 119 = 96 + 256*1` | 1 |
| 1 | `1 + 233*1 + 0*1 = 234 + 256*0` | 0 |
| 2 | `0 + 0*1 = 0 + 256*0` | 0 |
| 3 | `0 = 0 + 256*0` | 0 |

The strict comparison proves `257-119-1=137`: the low byte equation is
`1 + 256*1 = 119 + 1 + 137`, and the high byte equation is
`1 + 256*0 = 0 + 1 + 0`. A Boolean borrow enters the high byte and the
terminal borrow is zero. Each product column contains at most two byte
products, one remainder byte, and one 16-bit incoming carry. Its two sides
are well below M31, so the field equations cannot wrap. The
[Lean no-wrap and strict-borrow lemmas](../../../formal/s31/S31/Gadgets/IntegerDivision.lean)
state those obligations explicitly. The source-to-Zig-gate refinement is
still an open proof obligation.

The source assignment decoder rejects a `u16` input of 65,536 before proof
generation. The circuit test also injects that raw field value directly with
`q=255`, `d=257`, and `r=1`, which satisfy `65,536=255·257+1` and `r<d`.
The arithmetic bit range gate alone makes that forged circuit invalid. This
checks that the proof does not depend on the host decoder for the word bound.

The same arithmetic-only convolution proves unsigned `u32` with four
little-endian bytes, eight product columns, four comparison columns, and
two 16-bit source limbs per input. For `123456 / 300`, the circuit's first
three product columns are `155*44+156=64+256*27`,
`27+155*1+1*44=226+256*0`, and `1*1=1+256*0`; the remaining high columns
and terminal carry are zero. A four-byte borrow chain proves `156<300`.
The [paired u32 record](../measurements/language/direct-u32-division-2026-10-10.json)
shows 92,802 median direct proof bytes and 2.38 ms median non-PoW prover
time versus 234,568 bytes and 16.02 ms under sparse-wide for 20 witnesses.
Unsigned `u64` and `u128` use the same direct path with respectively 16 and
32 full-product columns. The 128-bit worst column has no more than sixteen
byte products, so the no-wrap bound above still applies. Both inputs must
flow exclusively through the matching integer view before direct admission.
The [`u64` record](../measurements/language/direct-u64-division-2026-10-10.json)
shows 112,623 median proof bytes and 3.25 ms median non-PoW proving versus
235,466 bytes and 16.35 ms under sparse-wide. The
[`u128` record](../measurements/language/direct-u128-division-2026-10-10.json)
shows 137,388 bytes and 4.55 ms versus 232,517 bytes and 16.69 ms.
Each comparison uses 20 distinct verified witnesses and changed-statement
controls. Signed `i32`, `i64`, and `i128` still use the generic wide circuit.

## Audit and performance gates

The normalized relation and verifier key bind width, signedness, and the
single division operation. A hand-written source example should show the
quotient/remainder pair and the per-byte equations for a small concrete
case. Independent big-integer oracles should cover every width, zero
divisors, exact division, largest operands, signed boundaries, and deliberately
wrong quotient or oversized remainder witnesses. Native proofs must reject
changed public claims and false outputs. The Lean model should prove that
the bounded integer relation is equivalent to Euclidean division and that
signed reconstruction implements truncation toward zero; it must state any
remaining Zig-to-Lean refinement gap explicitly.

Record raw and padded AIR rows, fixed preprocessing, proof size, prover time,
and verifier time separately. Reuse the existing Bitcoin 256-bit division
gadget as a correctness reference. A fused quotient-product-remainder column
avoids a separate full-product output and checked-add circuit, but its
end-to-end benefit must be measured before claiming a speedup.

The [current paired profile record](../measurements/language/direct-fixed-division-2026-10-10.json)
compares the same optimized circuit under `direct-gate` and
`sparse-wide-gate` for 20 distinct witnesses each of `u8`, `i8`, `u16`, and
`i16`, with one warmup per profile. Median direct proof sizes are 40–73 KB,
compared with 227–229 KB under sparse-wide. Median non-PoW prover stages are
0.91–1.86 ms direct and 15.78–16.18 ms sparse-wide on the measured machine.
Full wall times are mixed because proof-of-work search dominates these small
circuits. The record contains all per-assignment times and verification
controls. Matching visible FRI parameters alone does not establish equal
soundness across different AIRs. The [earlier byte record](../measurements/language/byte-direct-division-2026-10-10.json)
documents the circuit before its single-gate Boolean optimization.
