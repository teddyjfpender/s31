# Direct fixed-width multiplication: source-level soundness review

This is a fresh read-through of the implemented d8/d13 arithmetic multiplier
and its direct compiler wiring. It was performed by the gadget author, so it
is **not** an independent third-party audit. The full native width matrix was
still running when this note was written. The detailed recurrence and hand
example are in the [language design note](../language/DIRECT_FIXED_INTEGER_MULTIPLICATION.md).

## Reviewed path and claim

The direct compiler collects little-endian operand bits through
`BitCache.getIntegerArithmetic` in
[`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig),
passes them with the raw limbs to
[`integer_multiply.zig`](../../../src/frontends/s31/language/gadgets/integer_multiply.zig),
and caches the returned low result bits. Wrapping uses the low `W` bits of an
exact product. Signed checked multiplication constructs the complete unsigned
`2W`-bit product and applies a high-limb sign identity. Unsigned checked
multiplication uses only the low radix columns, with zero terminal carry,
zero omitted high convolution coefficients, and zero spill bits. The generic
sparse-wide path is unchanged.

Under the stated API precondition and correct enforcement of the recorded
arithmetic gates, the reviewed direct constraints admit exactly the intended
wrapping product or non-overflowing checked product for widths 8, 16, 32, 64,
and 128, signed or unsigned. This is a local circuit soundness argument, not
a proof of the direct AIR, address-lookup closure, fixed-column binding, or
PCS/FRI verifier.

## Constraint checks

1. **Input provenance.** Each input limb's cached 8 or 16 bits came from an
   arithmetic decomposition that enforces Booleanity and reconstructs the
   limb, or from a compiler operation that packs proved Boolean bits into
   that limb. The cache key includes the wire address and bit width. A raw
   QM31 guess with non-base coordinates cannot satisfy the reconstruction.
   Source `int_view` and the multiplication call both reach this cache path.
2. **Partial top digit.** The d13 path packs only the actual top 12 source
   bits at `W=64` and top 11 at `W=128`. It introduces no free input padding
   bits. All output digit and carry wires are packs of self-product Boolean
   wires. The exact radix equation is asserted by an arithmetic zero
   self-loop for each column.
3. **No field-wrap alias.** The largest d8 left/right column bounds are
   264,195/1,048,575 using even a loose 12-bit carry. The d13 bounds are
   671,055,881/1,073,741,823 using even a loose 17-bit carry. All are below
   the M31 prime 2,147,483,647. Therefore every field equation is an integer
   equation. Bounded digit plus bounded carry gives a unique quotient and
   remainder at each column. The hardcoded narrower carry widths (8, 9, 10,
   15, 17 bits by width) are at least the all-maximum-input carry bounds; an
   underestimate could reject an honest product but cannot admit a false one.
4. **Full-product boundary.** The last carry after column `2N-2` is the final
   high digit. Its bits above digit width are zero-constrained. All bits in
   `[2W, 2Nd)` are also zero-constrained. Low `[0,W)` and high `[W,2W)` are
   packed independently into u16 limbs even when `W` splits a d13 digit.
   Wrapping deliberately leaves the final digit's bits above `W` unasserted:
   they are genuine overflow bits.
5. **Signed checked overflow.** The three sign bits come from proved top
   operand/result bits. The signed high-limb carry polynomial has only roots
   `{0,1,2,3}` in QM31. Each high-limb equation has both integer sides at
   most `4*65536-1`, below M31. With terminal carry `sa*sb+sr`, summing the
   equations is equivalent to
   `(A-sa*2^W)*(B-sb*2^W)=low-sr*2^W`. This rejects positive and negative
   overflow, including `MIN * -1`.
6. **Unsigned checked shortcut.** The low-column recurrence yields the exact
   low-coefficient value plus `base^N` times the terminal carry. The terminal
   carry is constrained to zero. Each omitted high coefficient is a sum of
   nonnegative digit products; its maximum is `10*8191^2 = 670,924,810 < p`,
   so a field-zero check also fixes its integer value to zero. In d13 widths,
   all bits in `[W, Nd)` of the final low digit are constrained to zero. Thus
   the exact product equals the low word and is below `2^W`. The independent
   Lean model in
   [`UnsignedCheckedShortcut.lean`](../../../formal/s31/S31/Gadgets/UnsignedCheckedShortcut.lean)
   proves this arithmetic implication, including a partial-top-digit spill
   lemma. It assumes the field equations were correctly lifted to integers;
   it is not a compiler correspondence theorem.

## API precondition and remaining evidence

`wrappingArithmetic`, `fullProductArithmetic`, and `checkedUnsignedArithmetic`
accept `[]Var` bit slices.
The gadget does not itself rebind those bits to the supplied raw limbs: doing
so would duplicate the compiler's range proofs. A caller that supplied
unproved or mismatched bits could prove a product unrelated to its limb
inputs. Current compiler calls use `BitCache.getIntegerArithmetic`, which
establishes the binding, and compiler-level provenance tests were added.
Treat these gadget functions as internal APIs with this explicit precondition;
an externally callable version should carry a proved-bit type or add limb
rebinding constraints.

Gadget-local value-circuit tests were added for mutated source, product
digit, carry, and result wires, and a 64-bit full product whose low/high
boundary splits a d13 digit. Compiler-level tests were added for input-bit
provenance, an out-of-range u8 input, signed i8 overflow, and a
multiply-then-add cache path. Shortcut tests separately cover a nonzero low
terminal carry, a nonzero omitted high coefficient, and d13 spill bits.
ReleaseSafe Zig and focused/full Lean builds passed on this source head; the
ten-width native proof matrix still needs passing current-head results before
release evidence is claimed.
The focused u8 checked native proof passed with changed public claim and
overflow rejection; its result alone does not establish the other widths or
a proving-speed improvement.
