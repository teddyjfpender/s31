# Scalar `is_zero`: source, Gate rows, and proof boundary

The admitted source fragment has one public `[m31; 1]` input and one public
`[m31; 1]` result. It contains exactly one zero test and returns that result:

```s31
use std@1;
circuit zero(public x: [m31; 1]) -> public [m31; 1] {
    let z = std::field::is_zero(x);
    z
}
```

An independent bounded parser reads the **exact source bytes** and checks that
the normalized relation is exactly one `is_zero` node, with no private inputs,
assertions, extra producers, or different output. Whitespace, comments, and
identifiers may vary. The parser rejects `inv` and `select`: their native
correspondence requires separate review. The package verifier requires the
source-derived row certificate whenever this source shape is admitted.

## What the compiler builds

Let `p = 2^31 − 1`. The compiler supplies two witness values: `z` (the answer)
and `h` (an inverse hint). The Gate AIR constrains both through these equations
in the field:

| Native row | Gate equation | Meaning |
| --- | --- | --- |
| multiply | `x · h = product` | Compute a candidate inverse product. |
| subtract | `1 − z = complement` | Choose the expected product. |
| subtract | `product − complement = difference` | Compare the two sides. |
| add self-loop | `anchor₁ + difference = anchor₁` | Force `difference = 0`. |
| multiply | `x · z = productZ` | Test the zero branch. |
| add self-loop | `anchor₂ + productZ = anchor₂` | Force `productZ = 0`. |
| add public copy | `z + 0 = public_output` | Bind the answer to the statement. |

The two self-loops are real Gate rows. The arbitrary anchor values cancel, so
the rows enforce `x·h = 1−z` and `x·z = 0`. These equations are total: when
`x=0`, the first equation forces `z=1` and any `h` works; when `x≠0`, the
second forces `z=0` and the first fixes `h=x⁻¹`. Therefore the output is a
Boolean M31 value without a separate bit gate.

Here are two complete hand calculations:

| Input `x` | Indicator `z` | Hint `h` | `x·h` | `1−z` | `x·z` | Public output |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `0` | `1` | `0` | `0` | `0` | `0` | `1` |
| `7` | `0` | `1,840,700,269` | `1` | `1` | `0` | `0` |

The one-lane direct Gate layout stores `x` at address 11, `z` at 14, and `h`
at 15. Its core rows are `mul` positions 505 and 506, `sub` positions 502 and
503, and the two add self-loops at positions 0 and 1. Add position 3 copies
`z` to the public result. The remaining rows derive fixed field constants,
bind the public input, provide the required one-producer identity rows for
the two guesses, and pad the trace. The independent checker reconstructs and
compares **all 512 fixed rows**: four selectors, three addresses, and one
multiplicity per row. This source currently costs 281 raw and 512 padded QM31
Gate rows.

The Gate AIR evaluates nine local polynomials per row: one-hot selector,
selector Booleanity, and the four packed output equations. The address
lookup relation links every use of an address to its produced value. The
fixed-row certificate checks the exported selector/address/multiplicity
columns and matches their native fixed commitment root to the sealed key.
The Lean [`ZeroRows.lean`](../../../formal/s31/S31/Gadgets/Air/ZeroRows.lean)
theorems prove that **every** witness satisfying the listed row equations
has `z=1 ↔ x=0` and `z=0 ↔ x≠0`; they also construct honest witnesses for
all inputs. `native_scalar_zero_roles_sound` additionally names the concrete
Gate wire addresses and proves the public output at address 4 equals the zero
test of the public input at address 3, conditional on the checked row equations
and constant wires. These algebraic theorems do not assume the native hint
generator chose the right `h`.

The native acceptance test compares all 6,144 main cells of honest exports
for `x=0` and `x=7` against an independent source-derived trace, verifies
both proofs, and checks the accepted main roots. Those two executions test
the implementation; the Lean theorem supplies the arbitrary-witness local
equation argument. The fixed-root and honest-proof joins still rely on the
native inspector, verifier, Gate lookup binding, and PCS. This slice does not
authenticate arbitrary proof openings or prove the general compiler correct.

Run the focused checks:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/zero_test_native_rows.py
cd formal/s31 && lake build S31.Gadgets.Air.ZeroRows
```
