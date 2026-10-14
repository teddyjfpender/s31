# Independent review: direct signed multiplication

Date: 2026-10-12. Scope: checked and wrapping `i8` through `i128` on the
direct arithmetic circuit path, especially the signed high-limb condition in
[`relation_compiler.zig`](../../../../../src/frontends/s31/language/relation_compiler.zig)
and the d8/d13 product recurrence in
[`integer_multiply.zig`](../../../../../src/frontends/s31/language/gadgets/integer_multiply.zig).
This was reviewed independently of the gadget author. It is a local
integer/circuit-source review, not an AIR compiler correspondence proof or a
PCS/FRI security review.

## Result

I found no satisfying false-product or overflow witness on the current
compiler call path. The signed high-limb identity is exact when the operand
bits are Boolean and bound to their limbs, the product recurrence is enforced,
and the recorded arithmetic gates are correctly interpreted by the AIR.
The `BitCache.getIntegerArithmetic` call establishes that operand-bit binding
for the current compiler. The gadget API itself accepts the bit slices as a
precondition and does not rebind them to its `left` and `right` raw limbs.

The independent integer-equation test
[`test_direct_multiply_algebra.py`](../../../../../src/frontends/s31/tests/python/test_direct_multiply_algebra.py)
exhausts all 65,536 signed 8-bit input pairs, checks wide signed boundaries,
and compares the unsigned shortcut conditions against exact products at all
five widths. It completes in about 0.04 seconds locally. It deliberately does
not claim to test emitted AIR or native proof verification.

## Signed checked identity

Let `Q = 2^W`. Interpret the W-bit input patterns `a,b` as signed integers
`A = a - sa*Q`, `B = b - sb*Q`, where `sa,sb` are the proved sign bits. The
full unsigned product has the unique decomposition `a*b = low + Q*high`.
The proved sign bit of `low` is `sr`, so its signed interpretation is
`R = low - sr*Q`. Expanding `A*B = R` gives the necessary and sufficient
condition

```text
high = sa*b + sb*a - sr - sa*sb*Q.
```

The implemented limb recurrence for base `L = 2^8` (`i8`) or `L = 2^16`
(all wider types) is

```text
c_j + sa*b_j + sb*a_j + sr*(L-1) = high_j + L*c_(j+1),
c_0 = 0,   c_final = sa*sb + sr,   c_j in {0,1,2,3}.
```

Multiplying each equation by `L^j` and summing gives
`high + Q*c_final = sa*b + sb*a + sr*(Q-1)`, exactly the condition above.
Each integer side of a limb equation is below `4*65536 < p`, even at the
largest width, so equality in M31 cannot hide a different integer value.
The four-root polynomial has precisely the four stated roots over QM31.

For example, `i8: (-3)*7 = -21` has `a=253`, `b=7`, `low=235`, `high=6`,
`sa=1`, `sb=0`, `sr=1`. The single limb equation is
`0+7+255=6+256*1`, and the terminal carry is `1`. For `MIN*(-1)`, the
unsigned product's high word cannot match the terminal carry, so the
overflowing signed result is rejected. For `(-1)*(-1)`, the high word and
terminal carry do match, yielding `1`.

## Wrapping and unsigned checks

Wrapping uses the first W proved product bits; discarded higher bits do not
enter the claim. The full product path constrains the last carry and every
padding bit above `2W`. The d13 top source digit contains only 12 bits for
W=64 and 11 bits for W=128, so no unconstrained source padding enters.

The unsigned shortcut constrains every low-column radix equation, the low
terminal carry, the spill bits above W in the partial top digit, and each
omitted high source coefficient to zero. The largest such coefficient is
below `10*(2^13-1)^2 < p`. Nonnegative coefficients cannot cancel in the
field. The independently checked shortcut predicate matches `a*b < 2^W`
on deterministic edge and sampled pairs for all widths. The exact bounded
argument is in the existing unsigned review.

## Trust boundary and attempted counterexamples

The gadget's raw `left` and `right` parameters are used for length checks;
the arithmetic circuit is built from `left_bits` and `right_bits`. If an
external caller passed the raw input `7` with bits encoding `3`, it could
obtain a circuit for `3*4=12` while advertising a raw left input of `7`.
This is a **real misuse of the gadget API**, not a counterexample to the
current compiler, which calls `BitCache.getIntegerArithmetic` before the
gadget. A proved-bit wrapper type or an API taking only bound bit vectors
would make this requirement harder to violate in future code.

I also checked the likely overflow boundaries: a nonzero low terminal carry,
an omitted high coefficient with zero low carry, a bit spilling from a partial
d13 top digit, the signed `MIN*(-1)` overflow, and positive/negative signed
products with a nonzero high unsigned word. The source equations reject each
for the reasons above. Existing native ten-width matrices additionally show
honest proof acceptance, changed-public-claim rejection, and checked-overflow
rejection; those empirical controls do not prove the PCS/FRI layer.
