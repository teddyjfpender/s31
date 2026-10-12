# A direct integer product, from source to proof

This chapter follows one `u16` multiplication through the current
`direct-gate` profile. You can calculate every digit with a pencil. The
[fixed-width guide](fixed-width-integers.md) explains the alternative
`sparse-wide-gate` byte and lookup circuit; the direct circuit uses Boolean
bits and arithmetic gates instead of the fixed 65,536-cell range table.

## 1. The program and its claim

```s31
use std@1;

circuit hand_u16_product(private a: u16, private b: u16) -> public u16 {
    let product = std::int::mul_checked(a, b);
    product
}
```

For one valid run, the prover supplies `a = 255`, `b = 2`, and claims
`product = 510`. Each value occupies one little-endian `u16` assignment
limb. The verifier learns the public result, the program and its proof key;
it does not learn which private factor pair the prover used.

```json
{
  "public_inputs": {},
  "private_inputs": {"a": [255], "b": [2]},
  "public_outputs": {"product": [510]}
}
```

The source call is **checked**: its exact, nonnegative integer product must
fit in `0..65535`. `mul_wrapping(a,b)` instead returns the low 16 bits even
when the exact product is larger.

## 2. The relation is small; the circuit does the work

`s31.py lower` emits three normalized nodes for this program:

| Node | Operation | Inputs | Meaning |
| --- | --- | --- | --- |
| `_s31_0` | `int_view`, tag 16 | `a` | Interpret the input limb as `u16`. |
| `_s31_1` | `int_view`, tag 16 | `b` | Interpret the input limb as `u16`. |
| `product` | `int_mul_checked`, tag 16 | `_s31_0`, `_s31_1` | Bind the exact product to the public output. |

The `16` tags encode unsigned width 16; they are part of the compiled
relation and verification key. One multiplication *node* is not one AIR
row. The relation compiler expands it into range bits, product digits,
carry bits, arithmetic gates, and public binding.

```text
private a,b ──proved 16-bit decompositions──▶ two radix-256 digits each
                                           │
                                           ▼
                             bounded product-and-carry equations
                                           │
                                           ▼
                              low 16 bits + overflow checks
                                           │
                                           ▼
                              public `product` binding
```

For `u16`, the direct gadget uses base $B=256$ and two digits per operand:
$a=a_0+256a_1$ and $b=b_0+256b_1$. Each input limb is packed from its
sixteen proved Boolean bits. In particular, the prover cannot claim an
out-of-range digit independently of the input limb. The output digits and
carries are also packed from freshly proved Boolean bits.

## 3. Fill the circuit by hand

Choose `a = 255 = 0x00ff`, `b = 2 = 0x0002`.
Their little-endian digits are $a=[255,0]$ and $b=[2,0]$. The gadget checks
these two low columns, with $c_0=0$:

$$
\begin{aligned}
a_0b_0+c_0 &= d_0+256c_1,\\
a_0b_1+a_1b_0+c_1 &= d_1+256c_2.
\end{aligned}
$$

| Low column, from least significant | Actual left side | Result digit | Carry to next column | Equality the circuit checks |
| --- | ---: | ---: | ---: | --- |
| 0, bits 0–7 | $255\cdot2+0=510$ | $d_0=254$ | $c_1=1$ | $510=254+256\cdot1$ |
| 1, bits 8–15 | $255\cdot0+0\cdot2+1=1$ | $d_1=1$ | $c_2=0$ | $1=1+256\cdot0$ |

The public limb is $d_0+256d_1=254+256=510$. Checked multiplication also
requires $c_2=0$ and the omitted high coefficient $a_1b_1=0$. Both hold.
These are **separate checks**: `255 * 258` produces a nonzero $c_2=1$,
while `256 * 256` has $c_2=0$ but $a_1b_1=1$. Both must fail `mul_checked`.
`mul_wrapping` would return 254 and 0 respectively.

For `255 * 258`, the low columns are
$510=254+256\cdot1$ and
$255\cdot1+0\cdot2+1=256=0+256\cdot1$.
The low limb is `0x00fe = 254`, but the final carry is 1: the exact product
is $65{,}790$, outside `u16`. For `256 * 256`, both low digits and the
terminal carry are zero; the omitted high coefficient catches its product
$65{,}536$. Omitting either checked rule would accept a false product.

The circuit's key local constraints can be read as:

$$
z(z-1)=0\quad\text{for every Boolean digit/carry bit }z,
$$

$$
L_t=D_t+256C_{t+1}\quad(t=0,1),\qquad C_2=0,\qquad a_1b_1=0.
$$

Here $L_t$ is the product sum plus incoming carry in the table, and $D_t$
and $C_{t+1}$ are packed from the proved bits. The compiler realizes a
zero equation with an arithmetic self-loop gate, so this direct circuit
does not need a generic Eq gate or a `u16` range lookup. Each side of every
`u16` column equation is below the M31 prime $p=2^{31}-1$. Therefore a
field equality cannot conceal an incorrect integer equation by wrapping
modulo $p$.

For wider widths, the same direct gadget uses 8-bit digits through `u32`
and 13-bit digits for `u64`/`u128`. The top 13-bit digit may be partial:
only its real source bits are packed. Signed checked multiplication proves
the full unsigned bit-pattern product and a separate sign-correction carry
chain. Those cases have different equations and costs; see the
[implementation design](../../../../design/s31/language/DIRECT_FIXED_INTEGER_MULTIPLICATION.md).

## 4. Where AIR rows and polynomials enter

The table above is a **logical digit table**, not a dump of physical AIR
rows. Each Boolean check, packing operation, product term, addition, and
zero self-loop becomes circuit gates. In the `direct-gate` profile, those
gates occupy the QM31-operation AIR component. Its fixed columns select
opcodes and wire addresses; witness columns hold input/output wire values.
For example, a multiplication gate has the local relation $C-A\cdot B=0$;
an addition gate has $C-A-B=0$. A Boolean bit $z$ uses a self-product
gate with $A=B=C=z$, giving $z-z^2=0$. The arithmetic zero self-loop
with an output reused as an input forces its other input to zero.

LogUp joins each consumed address/value tuple to its producer, so a prover
cannot make a carry equal 1 in one gate and 0 where it is used next. The
public-output binding joins the reconstructed `product` limb to the claimed
510. The profile also adds input, constant, permutation, and finalization
rows. Thus neither the two digit columns nor the three relation nodes give
the complete AIR row count.

Each actual trace column is interpolated as a low-degree polynomial over
Stwo's circle evaluation domain. Schematically, for a gate selector
$s_{\rm mul}$, a local constraint polynomial has the form

$$C(X)=s_{\rm mul}(X)\bigl(O(X)-A(X)B(X)\bigr).$$

It vanishes on every relevant trace row. The prover combines such
constraints, divides by the trace-domain vanishing factor, and proves the
resulting composition has the required low degree with FRI. This formula
shows the gate **semantics**; the current `equations` command does not export
every instantiated term in the pinned AIR's symbolic constraint program.
The [circuit chapter](circuits.md) explains the actual columns and lookup
join; [AIR and polynomials](air.md) explains quotient and FRI checks.

## 5. What a successful proof means

Run the ten-width [direct multiplication acceptance gate](../tests/acceptance/math/direct_multiplication.py)
or select this one case:

```sh
python3 src/frontends/s31/tests/acceptance/math/direct_multiplication.py \
  --case u16 --mode checked --native
```

The gate checks the independent integer oracle, creates a native proof,
checks it with the generated verifier, tries a changed public statement,
and requires the native prover to reject an overflowing assignment.
Verifier acceptance means that, under the pinned circuit AIR and proof
system assumptions, **there exists** a private input pair whose exact
`u16` product equals the public limb. It does not certify that the private
inputs specifically were 255 and 2; those values are one satisfying
witness. Overflow is rejected by the circuit's checked rules, while a
changed public result is rejected by the verifier's statement binding.

The local digit bounds and tests do not amount to a full proof that Python
source lowering, Zig circuit emission, the AIR, and Stwo's PCS/FRI verifier
are mutually correct. The current [correspondence ledger](../../../../design/s31/language/COMPILER_CORRESPONDENCE.md)
tracks those separate obligations.
