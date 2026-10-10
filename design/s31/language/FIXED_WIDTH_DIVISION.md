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
wire is reconstructed from eight Boolean bits. A zero assertion is an
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
The wide circuit remains the path for 16 through 128 bits.

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

The [paired byte-profile record](../measurements/language/byte-direct-division-2026-10-10.json)
compares the same current circuit under `direct-gate` and `sparse-wide-gate`
for five distinct witnesses per signedness, with one warmup per profile.
Median proof size falls from 223,847 to 54,356 bytes for `u8` and from
223,935 to 72,947 bytes for `i8`; median non-PoW prover stages fall from
15.39 to 1.27 ms and from 15.84 to 1.94 ms respectively on the measured
machine. The record contains all per-assignment times and verification
controls. These are local profile comparisons, not a claim of equal security
from matching visible FRI parameters alone.
