# Direct fixed-width add, subtract, and compare: independent source review

Scope: the in-progress `direct-gate` path for `int_add_checked`,
`int_add_wrapping`, `int_sub_checked`, `int_sub_wrapping`, and `int_le` in
[`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig),
including [`integer_bits.zig`](../../../src/frontends/s31/language/gadgets/integer_bits.zig).
This is a source-level circuit review, not a native proof run or a PCS/FRI
soundness proof. The compiler was being edited during the review; recheck the
final diff before citing these findings for release.

## Constraint argument

For direct lowering, each input and result limb is reconstructed from eight
or sixteen wires satisfying `b*b=b`. Reconstruction is equated to the limb
through an arithmetic zero self-loop. Consequently each limb is a base-field
integer in `[0, 2^w)`, even when the original `u16` input uses a raw QM31
guess instead of the fixed range table. The bit cache is indexed by the
variable address and limb width; the reviewed cache insertion sites either
decompose the word or pack previously constrained Boolean bits. The special
sign-fill insertion repeats a proved sign bit for a word produced by
`sign*(2^w-1)`.

Every outgoing carry or borrow satisfies `c*c=c`. Each radix equation is
enforced by `anchor + residual = anchor` on a fresh, singly produced address.
For addition, `a+b+c_in=d+2^w*c_out`; for subtraction,
`a+2^w*c_out=b+c_in+d`; comparison subtracts `a` from `b` and returns
`1-c_out`. With the range bounds, either side is at most `2^17-1` for a
16-bit limb, below the M31 modulus. Thus field equality cannot hide a false
integer carry. A checked unsigned operation constrains the terminal carry to
zero. A checked signed operation constrains the usual sign-overflow Boolean
formula to zero. Signed comparison chooses the left sign when signs differ
and the unsigned comparison otherwise. These formulas match the relation
evaluator's intended cases.

An independent host-algebra enumeration checked all 65,536 pairs of
8-bit patterns against signed and unsigned integer addition, subtraction,
overflow, and `<=` semantics. It passed; this check does not execute the
compiler, circuit, AIR, or prover.

The direct AIR constructor rejects equality, conversion, XOR, and Blake gates
and requires a power-of-two arithmetic row count. The compiler's
`firstYieldViolation` guard checks that every circuit address has exactly one
producer. These guards are relevant to the self-loop range and zero checks;
their cryptographic enforcement still relies on correct fixed-column binding,
LogUp closure, AIR evaluation, and PCS/FRI soundness.

## Tests required before acceptance

1. For every signed and unsigned width in `{8,16,32,64,128}`, compare the
   direct circuit output with an independent integer oracle at `0`, `1`,
   `MAX`, signed `MIN`, signed `-1`, and values that propagate a carry or
   borrow across **every** limb. Check all five operations, both argument
   orders, and equality for `int_le`.
2. Check rejection of positive and negative signed overflow, unsigned
   addition overflow and subtraction underflow. For `u8`/`i8`, also attempt
   input-wire values `256` and `65535`; for a 16-bit limb attempt `65536`.
   Mutate the value table after building a valid circuit, because the
   assignment parser itself rejects a `u16` value of `65536`. The mutated
   circuit must fail independently of the source evaluator.
3. Build topology and value circuits for the same sources. Require equal
   variable counts, no yield violation, zero unsupported gate counts, and
   acceptance by the direct AIR constructor. Mutate a range bit, a carry,
   and a result digit independently and require `Circuit.check` to reject.
4. Run at least one native honest proof and one changed public-output
   rejection for a multi-limb signed case. Retain exact native geometry,
   proof bytes and wall-time figures before claiming a proving-speed gain;
   source gate counts alone are insufficient.

## Efficiency and admission notes

The path spends roughly one Boolean decomposition per distinct operand and
result word, plus one carry and radix equation per word. The bit cache avoids
repeating decomposition when an existing word is reused. `getArithmetic`
does not currently special-case the zero word, so a constant-zero operand
can pay eight or sixteen redundant Boolean checks on first use; this is an
optimization opportunity, not a soundness issue.

The direct AIR excludes `eq` and `m31_to_u32` gates. The new five operations
use arithmetic-only checks in direct mode, but adjacent `int_view` or other
integer operations can still emit legacy byte-range and equality gates on
some shapes. Direct-profile admission should therefore be tested for whole
programs, not inferred from the five operators in isolation.
