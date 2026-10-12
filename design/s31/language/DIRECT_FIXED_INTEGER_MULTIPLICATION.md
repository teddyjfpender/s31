# Direct fixed-width multiplication design

This note specifies the arithmetic-only `direct-gate` lowering for wrapping
and checked multiplication of `u8` through `u128` and `i8` through `i128`.
The d8/d13 gadget and compiler dispatch are implemented. Both ten-width
native checked and wrapping matrices passed on compiler fingerprint
`2580b5755d69a429842010aaab9ff2eef434f0a4030fd991a65105123b1eec22`.
This remains a local constraint argument: an independent cryptographic
soundness proof is a separate obligation. The existing
sparse-wide byte gadget remains the reference for relation semantics.

## Digits and the circuit

Treat signed operands as their unsigned `W`-bit patterns during multiplication.
The low `W` product bits are the same for signed and unsigned wrapping
multiplication. Choose digit width `d = 8` for `W = 8, 16, 32` and `d = 13`
for `W = 64, 128`; let `B = 2^d` and `N = ceil(W/d)`. The final input digit
contains only `m = W - d(N-1)` bits. It is packed from exactly those proved
Boolean source bits, so it is bounded by `2^m - 1` without a separate range
lookup. The remaining input digits are bounded by `B - 1`.

| `W` | `d` | `N` | top input bits `m` | maximum column sum | maximum carry | carry bits |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 8 | 1 | 8 | 65,025 | 254 | 8 |
| 16 | 8 | 2 | 8 | 130,304 | 509 | 9 |
| 32 | 8 | 4 | 8 | 260,864 | 1,019 | 10 |
| 64 | 13 | 5 | 12 | 268,394,496 | 32,763 | 15 |
| 128 | 13 | 10 | 11 | 603,897,856 | 73,718 | 17 |

The maxima use both operands with every source bit set. For column `t`, put
`S_t = C_t + sum(a_i b_(t-i))`, with only valid digit indices in the sum,
`C_0 = 0`, `D_t = S_t mod B`, and `C_(t+1) = floor(S_t/B)`. The circuit creates
Boolean bits for `D_t` and `C_(t+1)`, packs them, and constrains

```text
sum(a_i * b_(t-i)) + C_t = D_t + B * C_(t+1).
```

It enforces the equation with an arithmetic zero self-loop, not an equality
gate or a fixed `u16` lookup. Source bits may be reused from the compiler's
bit cache. Result bits can be recorded in that cache for subsequent integer
operations. Every newly created Boolean wire has one `b * b = b` producing
gate, preserving the direct circuit's single-producer invariant.

For wrapping multiplication, emit columns `0` through `N-1` and assemble the
result from product bits `[0, W)`. Bits `[W, N*d)` in the last digit are
legitimate overflow bits and are discarded. For a signed checked product, emit
columns `0` through `2*N-2`; the final carry is digit `2*N-1`. Constrain the
final carry's bits above digit width `d` to zero. Concatenate the `2*N` digits, pack
bits `[0, W)` into low `u16` limbs and bits `[W, 2*W)` into high limbs, and
constrain the padding bits `[2*W, 2*N*d)` to zero. The split may occur inside
a 13-bit digit. Signed overflow uses the high-limb identity below.

For `W=64`, digit 4 covers bit positions 52 through 64. Its first 12 bits
finish the low word at bit 63; bit 64 starts the high word. The 130-bit full
digit canvas has two trailing padding bits, both required to be zero.

### Unsigned checked shortcut

The unsigned checked path does not materialize the high product digits. It
emits only the first `N` radix columns, then constrains their terminal carry
to zero and every bit in `[W, Nd)` of the low canvas to zero. For each omitted
high convolution coefficient `k = N, …, 2N-2`, it separately constrains

```text
sum_(i+j=k) a_i*b_j = 0.
```

Each coefficient is nonnegative and at most `N*(2^d-1)^2`; for the largest
case this is `10*8191^2 = 670,924,810 < p`. Thus its field-zero constraint
implies integer zero. The low-column recurrence telescopes to

```text
decode(a)*decode(b)
  = decode(low_digits) + 2^(N*d)*terminal_carry
    + 2^(N*d)*decode(high_coefficients).
```

The terminal carry and high coefficients are zero, giving the exact product
`decode(low_digits)`. The spill-bit constraints make this product `< 2^W`.
The signed checked path still needs the complete high product and its sign
identity; wrapping still permits overflow.

## Hand calculation

For a `u16` product, take `a = 255 = 0x00ff` and `b = 258 = 0x0102`.
Their little-endian byte digits are `a = [255, 0]`, `b = [2, 1]`.

| column | product terms plus incoming carry | output digit | outgoing carry |
| ---: | --- | ---: | ---: |
| 0 | `255*2 + 0 = 510` | `254` | `1` |
| 1 | `255*1 + 0*2 + 1 = 256` | `0` | `1` |
| 2 | `0*1 + 1 = 1` | `1` | `0` |

Thus `255*258 = 0x000100fe`. Wrapping returns `0x00fe`; unsigned checked
multiplication rejects at the nonzero terminal carry after column 1, without
building column 2. A different overflow, `256*256`, has zero low columns and
zero terminal carry but a nonzero high coefficient at column 2, so the extra
high-coefficient constraint is essential. The circuit proves each row's
integer equation and each digit/carry range, so the public low word alone
cannot be changed while keeping the same input witness.

## Why field wrap cannot forge a digit

Builder wires live in QM31, but `b*b=b` has only roots zero and one in that
field; packing these bits with base-field constants keeps each digit in the
embedded M31 subfield. The M31 prime is `p = 2,147,483,647`. With `d = 8`,
`N <= 4`, even a loose
12-bit carry gives a column left side no larger than
`4*255^2 + 4095 = 264,195` and a right side no larger than
`255 + 256*4095 = 1,048,575`. With `d = 13`, `N <= 10`, even a loose
17-bit carry gives a left side no larger than
`10*8191^2 + 131071 = 671,055,881` and a right side no larger than
`8191 + 8192*131071 = 1,073,741,823`. All are strictly below `p`.
Consequently equality in M31 is equality of these nonnegative integers.
The first column fixes its carry and digit uniquely; induction fixes every
later column. The table's smaller carry widths follow from the all-maximum
input recurrence and reduce gate count without changing this argument.

## Signed checked overflow

Let radix `R = 256` for `W = 8`, otherwise `R = 65536`. Write the unsigned
patterns as `A` and `B`, and the exact unsigned product as
`A*B = low + 2^W * high`. Let `sa`, `sb`, and `sr` be the top Boolean bits of
`A`, `B`, and `low`. With little-endian radix-`R` limbs, constrain

```text
high_i + R*c_(i+1)
  = sa*B_i + sb*A_i + sr*(R-1) + c_i,
c_0 = 0,  c_i in {0,1,2,3},  c_final = sa*sb + sr.
```

Each sign bit comes from a proved input or result bit. The four-value carry
polynomial proves membership in `{0,1,2,3}`; arithmetic zero self-loops
enforce the limb equations and terminal condition. Both sides are at most
`4R-1 <= 262,143 < p`. Summing the limb equations gives exactly
`high + sa*sb*2^W = sa*B + sb*A - sr`, equivalent to
`(A-sa*2^W)*(B-sb*2^W) = low-sr*2^W`. Thus admission is precisely a
representable signed product, including rejection of `MIN * -1`.

For a one-limb `i8` check, `-3` has pattern `253` and `7` has pattern `7`.
The unsigned product is `1771 = 235 + 256*6`; `sa=1`, `sb=0`, `sr=1`.
The equation is `6 + 256*c_1 = 7 + 255`, so `c_1=1`, matching the required
terminal value `sa*sb+sr=1`. The low pattern `235` represents `-21`.

## Implementation and evidence boundary

The arithmetic gadget is implemented in
[`integer_multiply.zig`](../../../src/frontends/s31/language/gadgets/integer_multiply.zig).
Its `ArithmeticProduct` API takes the existing limb wires and their
concatenated, proved Boolean bits and returns low/high limbs and the low
result bits. The compiler dispatch and bit-cache/sign-bit integration are in
[`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig).
The unsigned shortcut's arithmetic model is proved in
[`UnsignedCheckedShortcut.lean`](../../../formal/s31/S31/Gadgets/UnsignedCheckedShortcut.lean):
low-column recurrence, zero terminal carry, zero high coefficients, and zero
spill imply exact product equality and the `< 2^W` bound. The theorem assumes
that circuit field equations have already been lifted to integer equations,
and does not claim compiler correspondence or proof-system soundness.
The sparse-wide gadget and canonical relation IR remain unchanged. Gadget-local
Zig tests mutate source, digit, carry, and result wires; compiler-level tests
cover input-bit provenance and signed overflow. The unsigned shortcut tests
include the two independent overflow mechanisms above and a d13 spill case.
The ReleaseSafe Zig suite and focused/full Lean builds passed for this source
head. The saved [checked matrix](../measurements/language/direct-multiply-checked-2026-10-12.json)
and [wrapping matrix](../measurements/language/direct-multiply-wrapping-2026-10-12.json)
cover all ten signed/unsigned widths each. Every native proof verified and
rejected a changed public claim; every checked prover also rejected an
overflowing assignment. The u128 unsigned checked shortcut uses 2,669 raw
QM31 rows versus 3,732 before the shortcut, but both round up to 4,096
padded rows. These matrices measure geometry and proof bytes, not an isolated
proving-time gain.

All ten signed/unsigned widths were compared against an independent integer
oracle, adversarial value circuits and value/topology parity passed, and the
native proof/overflow/changed-claim controls above passed. A paired
same-witness direct-versus-sparse proving-time study is still needed before
claiming a speedup. This local
constraint argument assumes the direct AIR enforces each arithmetic gate,
the fixed columns and address multiplicities are bound correctly, and the
native PCS/FRI verifier is sound; it does not prove those assumptions.
