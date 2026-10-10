# Fixed-width integers, from source to AIR

An M31 field element and an integer answer different questions. In M31,
$p-1+1=0$ because arithmetic is modulo $p=2^{31}-1$. In `u8`, the same bit
patterns use modulus $2^8=256$ for **wrapping** addition, while **checked**
addition rejects an overflow. S31 keeps those meanings separate in source,
in its normalized relation, and in the proof.

## A complete one-byte program

This is the checked-in [source](../examples/math/int_u8_checked.s31) and its
[assignment](../examples/math/int_u8_checked.valid.json):

```s31
use std@1;

// Both inputs are one-byte integers. A proof exists only if their exact sum
// fits in u8; 250 + 5 = 255 is the largest accepted result.
circuit int_u8_checked(private a: u8, private b: u8) -> public u8 {
    let sum = std::int::add_checked(a, b);
    sum
}
```

```json
{
  "public_inputs": {},
  "private_inputs": {"a": [250], "b": [5]},
  "public_outputs": {"sum": [255]}
}
```

The brackets in the assignment carry one little-endian limb; the source
value is a scalar `u8`. The verifier learns the claimed result 255 and that
some private bytes sum to it. It does not learn that the inputs specifically
were 250 and 5; the prover could use any pair satisfying the same circuit.
Run `s31.py lower` to inspect the relation. It contains two `int_view` nodes
tagged with width 8 and one `int_add_checked` node. The tags bind the intended
width to the compiled relation and verifier key. For example, replacing
`u8` with `i8` changes the tag and the arithmetic interpretation even though
both occupy one `u16` limb in the low-level relation.

## Representation and operations

| Source type | Range as an integer | Proof representation |
| --- | ---: | --- |
| `u8`, `i8` | `0..255`, `-128..127` | One range-checked `u16` limb, additionally proved below 256. |
| `u16`, `i16` | `0..65535`, `-32768..32767` | One `u16` limb. |
| `u32`, `i32` | Unsigned `0..2^32-1`, signed `-2^31..2^31-1` | Two little-endian `u16` limbs. |
| `u64`, `i64` | Unsigned `0..2^64-1`, signed `-2^63..2^63-1` | Four little-endian `u16` limbs. |
| `u128`, `i128` | Unsigned `0..2^128-1`, signed `-2^127..2^127-1` | Eight little-endian `u16` limbs. |

For `iW`, the stored pattern $x$ represents $x$ if its high bit is zero, and
$x-2^W$ otherwise. Thus an `i8` value of $-1$ appears as `[255]` in a
proof assignment; `[−1]` is not a canonical limb. Every operation requires
two operands of the same nominal type. Neither field arithmetic nor
`UInt256` arithmetic is chosen implicitly.

| `std::int` call | Meaning |
| --- | --- |
| `add_checked(a,b)`, `sub_checked(a,b)` | Exact integer result in the type's signed or unsigned range; overflow or underflow has no valid witness. |
| `add_wrapping(a,b)`, `sub_wrapping(a,b)` | Low $W$ bits of the result, interpreted according to the result type. |
| `mul_wrapping(a,b)` | Low $W$ product bits, using constrained base-256 columns. |
| `mul_checked(a,b)` | Exact product in the type's range; proves the full product and rejects overflow. |
| `le(a,b)`, `lt(a,b)`, `ge(a,b)`, `gt(a,b)` | Signed ordering for `iW`, unsigned ordering for `uW`; constrained `bit` result. |
| `eq(a,b)`, `ne(a,b)` | Bit-pattern equality or inequality; constrained `bit` result. |
| `from_limbs_u8(raw)` through `from_limbs_i128(raw)` | Turn an exactly sized `[u16; L]` into the named scalar; the `u8` and `i8` forms prove the extra byte bound. |
| `limbs(x)` | Explicitly view a scalar as its `[u16; L]` bit pattern; no arithmetic node. |
| `reinterpret_u8(x)` through `reinterpret_i128(x)` | Reinterpret the same bits at the **same width** with the named signedness; no numeric conversion. |
| `cast_checked_u8(x)` through `cast_checked_i128(x)` | Preserve the numeric value in the named target type; reject values outside its range. |
| `bit_and(a,b)`, `bit_or(a,b)`, `bit_xor(a,b)`, `bit_not(a)` | Operate on the exact $W$-bit patterns; signed and unsigned inputs have the same Boolean equations. |

There is no integer `+` or `-` operator yet: call `std::int` to choose checked
or wrapping semantics. `std::math::sub` and source `-` remain M31 operations.
There are no fixed-width division or shift operations yet.
Reinterpreting `i8` to `u8` maps $-1$ to
255; it does not reject or change the bits.

## The one-byte circuit by hand

For the program above, let $a,b,r$ be byte wires and $c$ the carry bit.
The compiler builds range and arithmetic gates enforcing:

$$
0\le a,b,r<256,\qquad c(c-1)=0,\qquad a+b=r+256c,\qquad c=0.
$$

The assignment $(a,b,r,c)=(250,5,255,0)$ satisfies every equation. If
`b=10`, the only byte result is $r=4$ with $c=1$, because
$250+10=4+256$. `add_wrapping` accepts that result; `add_checked` rejects
it by requiring $c=0$. A claimed public result other than the computed byte
also fails its public-output binding. The prover cannot choose an unbounded
`r` to make a false addition appear true: the byte range is proved.

The underlying `u16` range check is a lookup into the existing range table.
For a byte $x$, the circuit additionally guesses a range-checked `u16` wire
$q$ and enforces $256x=q$. As $0\le q<65536$ and the product stays below the
M31 modulus, this proves $0\le x<256$ as an ordinary integer inequality.
The carry is separately constrained by $c^2-c=0$. These witness wires are
verified circuit wires, not trusted host calculations.

For widths above 8, with base $B=65536$ and little-endian digits indexed by
$j$, each addition step proves

$$a_j+b_j+c_j=r_j+B c_{j+1},\qquad c_0=0,\qquad c_j\in\{0,1\}.$$

Subtraction proves $a_j+B d_{j+1}=b_j+d_j+r_j$ with Boolean borrows.
Unsigned checked arithmetic constrains the final carry or borrow to zero.
This scales with one, two, four, or eight digits, instead of padding every
operation to the sixteen digits of `UInt256`.

## Signed values and comparisons

The top digit is split into a lower part $\ell$ and sign bit $s$:

$$t=\ell+2^{k-1}s,\qquad s(s-1)=0,$$

where $k=8$ for `i8` and $k=16$ for the other signed types. The lower part
is bounded with a separate range-checked scaled wire: $512\ell<65536$ for
`i8`, or $2\ell<65536$ for a 16-bit top digit. Thus the bit really is the
high bit; it cannot be assigned independently of the input pattern.

Signed wrapping addition uses the same bit-pattern carry equations. Checked
addition also rejects equal-sign operands whose result has the opposite
sign. For example, `i8(120) + i8(10)` wraps to bit pattern 130, which means
$-126$; checked addition rejects it. Checked subtraction rejects a changed
result sign when the operand signs differ. These are Boolean gate equations
over constrained sign bits.

For `le(a,b)`, the circuit subtracts $a$ from $b$ limb by limb. If the final
borrow is $d$, unsigned $a\le b$ is $1-d$. For signed values with different
sign bits, the answer is the sign of $a$; with equal signs, use the unsigned
answer. So `i8(-1) <= i8(1)` is true even though their raw bytes are 255 and
1. The remaining comparisons compose `le` with constrained Boolean `not`
and `and` gates; they do not use a host-only comparison.

## Checked numeric casts by hand

The [cast examples](../examples/math/casts/README.md) use
`std::int::cast_checked_T(x)` for every pair of the ten fixed-width integer
types. The call is **partial**: if the integer does not fit in `T`, there is
no valid witness, including in an inactive witness-dependent branch.
`reinterpret_T(x)` instead keeps the bits and requires the same width.

For `i8(-1) → i16`, the source byte is $a=255$ with proved sign bit $s=1$.
The circuit computes its target limb from

$$r=a+65280s=255+65280=65535.$$

The two interpretations agree: $255-256=-1=65535-65536$. For widening
to multiple limbs, every new upper limb is $65535s$. A nonnegative source
has $s=0$, so its added limbs are zero. These are constrained arithmetic
wires; the prover cannot supply a different extension.

For the [`i16 → i8` example](../examples/math/casts/i16_to_i8.s31),
the source limb $a=65408$ is split into a target byte $r=128$ and an
upper byte $h=255$:

$$a=r+256h=128+256(255),\qquad h=255s_a,\qquad s_r=s_a=1.$$

Here both bits prove the sign of their own word, and both bytes are bounded.
The field equation is an integer equation because each side is below
$2^{24}<p$. A proposed cast of `i16(-129)` has source pattern $65407$.
It splits as $r=127,h=255$, but $s_r=0$ while $s_a=1$, so the sign equality
rejects it. `u16(128) → i8` fails for the opposite reason: its high byte
is zero, but the target byte has sign bit one. For larger narrowing casts,
every discarded 16-bit limb must equal $65535s_a$, and the destination sign
must match the source sign. A signed-to-unsigned cast separately requires
$s_a=0$, even when the unsigned target is wider.

The relation records both source and target width/sign tags in one
`int_cast_checked` node. The [Lean cast model](../../../../formal/s31/S31/Gadgets/IntegerCast.lean)
proves that the extension and discarded-limb equations preserve the
interpreted integer. It does not establish correspondence of production
Zig gates to that model; local circuit controls and native proofs check that
path separately.

The [native cast gate](../tests/acceptance/math/casts.py) proves these exact
sources and rejects plausible truncated outputs on overflow:

| Source → target | Raw QM31 rows | Padded QM31 rows | Raw range rows | Proof bytes, one local run |
| --- | ---: | ---: | ---: | ---: |
| `i8 → i16` | 48 | 64 | 4 | 236,747 |
| `i16 → i8` | 54 | 64 | 8 | 227,219 |
| `i128 → i64` | 70 | 128 | 12 | 231,179 |

The [measurement record](../../../../design/s31/measurements/language/checked-integer-casts-2026-10-10.json)
pins the complete rows and canonical circuit hashes. The shared 65,536-cell
range table dominates fixed preprocessing, so these numbers describe proof
shape rather than an established throughput gain.

## Bitwise operations by hand

The [byte XOR source](../examples/math/bitwise/u8_xor.s31) proves a private
calculation with public result 102:

```s31
use std@1;

circuit u8_xor(private a: u8, private b: u8) -> public u8 {
    let result = std::int::bit_xor(a, b);
    result
}
```

The assignment gives `a=[170]` and `b=[204]`. A `u8` occupies one
little-endian limb in the assignment; inside the bit gadget it is decomposed
into eight constrained bits, numbered from the least significant bit:

| Bit position $i$ | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $a_i$ for 170 | 1 | 0 | 1 | 0 | 1 | 0 | 1 | 0 |
| $b_i$ for 204 | 1 | 1 | 0 | 0 | 1 | 1 | 0 | 0 |
| $y_i=a_i\oplus b_i$ | 0 | 1 | 1 | 0 | 0 | 1 | 1 | 0 |

For each guessed input bit, the circuit checks $a_i^2=a_i$ and
$b_i^2=b_i$. It also checks $a=\sum_{i=0}^7 2^i a_i$ and the same equation
for $b$. XOR uses $y_i=a_i+b_i-2a_ib_i$, then packs
$y=\sum_{i=0}^7 2^i y_i=102$. The Boolean input equations force every
$y_i$ to be Boolean; the output limbs and public result are bound by the
ordinary circuit and AIR gates. An invented bit decomposition cannot satisfy
the reconstruction equation for a different input byte. Since the packed
values are below 256, these field equalities do not hide an M31 wrap.

`bit_and` uses $a_ib_i$; `bit_or` uses $a_i+b_i-a_ib_i$; `bit_not`
uses $1-a_i$. The same construction repeats for all $W$ bits of `u16` through
`u128` and their signed peers. Every 16-bit input limb is reconstructed from
exactly 16 bits. The compiler caches proved bits by circuit wire, so a
straight-line expression that reads the same input in both AND and XOR shares
its decomposition. The [mixed `u32` source](../examples/math/bitwise/u32_mix.s31)
exercises this reuse across two 16-bit limbs. Its two 32-bit inputs require
64 bit Boolean checks in total; the subsequent NOT and OR use already proved
result bits. The recorded 68 raw Eq rows include those 64 bit checks and four
other equality checks. The generated proof establishes
these equations and the public output; it does not reveal the private inputs.

The [Lean Boolean model](../../../../formal/s31/S31/Gadgets/IntegerBits.lean)
proves soundness and completeness of the pointwise operations for any `BitVec`
width. The source-to-Zig gate correspondence is still checked by executable
circuit tests and native proof controls, not by a Lean refinement theorem.
The [native bitwise gate](../tests/acceptance/math/bitwise.py) pins the
canonical circuit hash and AIR rows, verifies all three examples, and rejects a
false output and a changed verifier statement. In one local run, `u8_xor`
used 141 raw QM31 rows and a 230,986-byte proof; `u32_mix` used 820 raw QM31
rows and a 237,398-byte proof. Signed `i128_xor` used 1,812 raw QM31 rows
and a 236,298-byte proof. The
[measurement record](../../../../design/s31/measurements/language/fixed-width-bitwise-2026-10-10.json)
includes padded rows and fixed preprocessing. The shared range table still
dominates fixed work, and these single-run sizes are not speed benchmarks.

## Wrapping multiplication by hand

The [checked-in `u8` program](../examples/math/multiplication/u8_wrapping.s31)
contains `std::int::mul_wrapping(a,b)`. Its private inputs are 250 and 7;
the public output is 214 because $250\cdot7=1750=214+256\cdot6$:

```s31
circuit u8_wrapping(private a: u8, private b: u8) -> public u8 {
    let product = std::int::mul_wrapping(a, b);
    product
}
```

The compiler emits one `int_mul_wrapping` node. The circuit constrains input
bytes $a,b$, output byte $d$, and carry $c$ with

$$
0\le a,b,d<256,\qquad 0\le c<65536,\qquad ab=d+256c.
$$

| Wire | Hand-calculated value | Why it is constrained |
| --- | ---: | --- |
| `a`, `b` | 250, 7 | Each is a range-checked input byte. |
| `a*b` | 1750 | A circuit multiplication of the two input wires. |
| `d` | 214 | The output byte has an independent byte-range proof. |
| `c` | 6 | The carry has a `u16` range proof. |

Since both sides are below $p=2^{31}-1$, the field equation is also an
ordinary integer equation. The prover cannot choose $d=215$ and compensate
with a fractional or out-of-range carry. The final carry is discarded because
the operation promises a result modulo $2^8$. A changed public output fails
the verifier's output binding.

For wider types, every `u16` limb is split into two proved bytes:
$w_j=a_{2j}+256a_{2j+1}$. The low byte has a direct byte range check. The
high byte is a `u16` witness proved below 256 by this reconstruction equation
and the original limb's `u16` bound; it needs no second byte check. If
$a_i,b_i$ are the little-endian input bytes,
column $k$ proves

$$
c_k+\sum_{i=0}^{k}a_i b_{k-i}=d_k+256c_{k+1},\qquad c_0=0.
$$

The circuit computes only columns $0$ through $W/8-1$ and combines each
output byte pair as $r_j=d_{2j}+256d_{2j+1}$. For at most 16 bytes, a column
has at most 16 products of values below 256. Its left side is at most
$16\cdot255^2+65535=1{,}105{,}935$, and its right side is at most
$255+256\cdot65535=16{,}777{,}215$. Both are below $p$, so no M31 wrap can
hide a false integer equation. Each carry is a proved `u16` value, and each
output digit is a proved byte.

In the [`u32` example](../examples/math/multiplication/u32_wrapping.s31),
$a=2^{32}-1$ has bytes `[255,255,255,255]` and $b=2$ has bytes
`[2,0,0,0]`. Its columns give $510=254+256\cdot1$ followed by three
copies of $511=255+256\cdot1$. The result bytes
`[254,255,255,255]` become little-endian limbs `[65534,65535]`, or
$2^{32}-2$. The [`i128` example](../examples/math/multiplication/i128_wrapping.s31)
uses the same bit-pattern rule: $-1\cdot2$ wraps to the 128-bit pattern
for $-2$.

Lean proves the high-byte bound, the per-column integer bound, unique byte
and carry, an honest column witness, and the composed low-product value in
[`IntegerMultiply.lean`](../../../../formal/s31/S31/Gadgets/IntegerMultiply.lean).
Native acceptance tests check representative complete circuits and false
public claims. The Lean model does not by itself prove that Zig emits the
modeled columns.

## Checked multiplication by hand

`std::int::mul_checked` computes all $2W$ product bits. Its byte columns run
through index $2W/8-1$, and the final carry is constrained to zero. Write the
complete product as $U=L+2^W H$, where $L$ and $H$ each have $W$ bits. For an
unsigned type, the circuit requires every byte of $H$ to be zero. In the
[`u8` example](../examples/math/multiplication/u8_checked.s31),
$25\cdot10=250=250+256\cdot0$, so the check passes. With the same first
input and second input 11, $275=19+256\cdot1$; the nonzero high byte makes
the circuit unsatisfiable even if a caller claims the low byte 19.

Signed types interpret a bit pattern $A$ as $A-s_A2^W$, where $s_A$ is its
proved sign bit. Let $s_B$ be the other operand's sign and $s_L$ the sign
of the low product. The circuit proves one more bounded carry chain for

$$
H+2^W C=s_A B+s_B A+s_L(2^W-1),
\qquad C=s_As_B+s_L.
$$

It follows by expanding $(A-s_A2^W)(B-s_B2^W)$ that the **integer** product
equals $L-s_L2^W$, exactly the signed value represented by the output.
Each correction column uses base $2^{16}$, or 256 for `i8`; its carry is
constrained to one of 0, 1, 2, 3 by a four-root polynomial. Its two sides
are below the M31 modulus, so field wrap cannot fake this equality.

The [`i8` program](../examples/math/multiplication/i8_checked.s31) proves
$(-1)\cdot2=-2$. Its unsigned byte patterns are $A=255$, $B=2$, and
$U=510=254+256\cdot1$. The signs are $(s_A,s_B,s_L)=(1,0,1)$:

| Checked quantity | Hand calculation | Required equality |
| --- | ---: | --- |
| Full product | $255\cdot2=510$ | $L=254$, $H=1$ |
| Sign correction | $1\cdot2+0\cdot255+1\cdot255=257$ | $H+256C=1+256\cdot1$ |
| Terminal carry | $C=1$ | $s_As_B+s_L=0+1$ |
| Signed result | $(255-256)\cdot2=-2$ | $254-256=-2$ |

For `i8`, $(-128)\cdot(-1)=128$ is rejected: 128 is outside
$[-128,127]$. The full-product and correction equations reject it even
though the low byte alone would be 128. The source operation is **partial**:
it cannot appear in an inactive branch of a witness-dependent `if`.
The same gadget covers signed and unsigned widths through 128 bits; it
uses a full byte convolution, so its proof cost grows with width.

Lean proves the complete unsigned product, the unsigned high-zero rule,
and both directions of the exact signed correction equation in
[`IntegerMultiply.lean`](../../../../formal/s31/S31/Gadgets/IntegerMultiply.lean).
The production Zig emission and complete AIR are separately checked by
local circuit tests and native proofs; they are not covered by that Lean
theorem.

The native [`multiplication.py`](../tests/acceptance/math/multiplication.py)
gate pins these `sparse-wide-gate` AIR costs and checks one proof per
representative operation and width:

| Program | Raw QM31 rows | Padded QM31 rows | Raw range rows (`m31_to_u32`) | Raw Eq rows |
| --- | ---: | ---: | ---: | ---: |
| `u8_wrapping` | 39 | 64 | 7 | 4 |
| `u32_wrapping` | 86 | 128 | 28 | 16 |
| `i128_wrapping` | 452 | 512 | 112 | 64 |
| `u8_checked` | 43 | 64 | 10 | 7 |
| `i8_checked` | 78 | 128 | 16 | 19 |
| `u32_checked` | 116 | 128 | 40 | 25 |
| `i128_checked` | 903 | 1,024 | 166 | 123 |

These totals include input, output, lookup, and proof-profile overhead. The
128-bit wrapping circuit has 16 output-byte columns, with 136 byte-product
terms in total. The checked circuit computes all 32 product columns and
proves the signed correction. Small integer relations use minimum constant
radix 16 instead of the generic radix 256: for `i8_checked`,
finalization fell from 269 to 34 QM31 rows. Its complete circuit fell from
313 to 78 raw QM31 rows, but the fixed `seq_16` range table still contributes
65,536 preprocessed cells. The local proofs remained around 230–239 KB and
the one-run prover timings did not establish an end-to-end speedup. The
[measurement record](../../../../design/s31/measurements/language/compact-integer-constants-2026-10-10.json)
separates rows, fixed cells, and proof observations.

## Where the AIR and proof enter

The source compiler emits width-tagged `int_view`, arithmetic, or comparison
nodes. The circuit compiler expands each node into range checks, carry or
borrow gates, sign gates where needed, and output wires. The generic circuit
AIR then places these gates in trace rows. Gate constraints check the local
equations; address lookups connect an output wire to every later use of that
wire, and public binding fixes the result to the statement. Stwo commits to
the trace and proves the AIR constraints through its polynomial protocol.
The generated native verifier checks that proof against this program's
compiled key and public statement.

For example, the byte addition gate has a zero polynomial
$P_{\mathrm{add}}(a,b,r,c)=a+b-r-256c$. A Boolean carry gate has
$P_{\mathrm{bit}}(c)=c(c-1)$. The prover's trace polynomials must satisfy
these at the active gate rows; the quotient construction and low-degree test
check that claim over the committed trace. The equations above describe the
integer gadget. The [circuit AIR chapter](air.md) describes the actual packed
gate rows, selectors, wire lookups, and quotient used around it.

To inspect this exact program locally:

```sh
python3 src/frontends/s31/python/s31.py lower src/frontends/s31/examples/math/int_u8_checked.s31
python3 src/frontends/s31/python/s31.py oracle src/frontends/s31/examples/math/int_u8_checked.s31 src/frontends/s31/examples/math/int_u8_checked.valid.json
python3 src/frontends/s31/python/s31.py trial src/frontends/s31/examples/math/int_u8_checked.s31 src/frontends/s31/examples/math/int_u8_checked.valid.json --lowering sparse-wide-gate --out zig-out/s31/int-u8-checked
```

`lower` shows width-bearing relation nodes. `oracle` evaluates the relation
independently of proof generation. `trial` builds the native verifier, proves
the fixture, and verifies it. For a focused negative case, change `b` to 10
and `sum` to 4: the oracle or proof rejects `add_checked`; changing the call
to `add_wrapping` makes that bit-pattern result valid.
