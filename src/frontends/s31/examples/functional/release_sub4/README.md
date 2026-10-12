# Ordered subtraction with a pure helper

`functional.s31` computes `-2*x` in four M31 lanes. The helper's three
arithmetic operations are `2*x`, `x - 2*x`, and `(x - 2*x) - x`. The order of
both subtraction operands matters; in particular, `x - 2*x` cannot be
commutatively sorted. `manual.s31` spells out the exact same three relation
nodes and generated wire names.

The compiler specializes `affine(x, x)` at build time. Both parameters `a`
and `b` become the existing input wire `x`; `doubled` becomes `x + x`,
`difference` becomes `x - doubled`, and the final expression becomes
`difference - x`. The call creates no runtime frame or AIR row. The checked
normalized relation has exactly these three arithmetic nodes for both files.

The independent direct-gate v2 source checker reparses both files, compares
their complete normalized relation and canonical IR, and checks the native
Gate AIR selector, address, multiplicity, and fixed-root schedule. The pure
function contributes zero gates. This example has 323 raw and 512 padded
QM31 rows in the current direct profile. Its public output is
`[(p - 2*x[i] % p) % p]`, where `p = 2^31 - 1`.

Run the native proof and strict five-pin release check from the repository
root:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/subtraction_release.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/subtraction_optimized_release.py
```

`optimized.s31` repeats the ordered operation `x - twice`. Opt-in v3
correspondence reuses that subtraction, so four source operations become
three native gates. `optimized_manual.s31` names those three gates directly.
The v3 test compares their complete canonical IR, AIR geometry, native proof,
and strict release admission. Reversing the subtraction would be a different
canonical gate and would not share it.

## By hand: source values and AIR rows

Take the public four-lane input `x = [0, 1, 2, 7]`. Each lane is an M31
field element modulo `p = 2,147,483,647`. A *lane* is one position in this
four-element vector; these operations act independently at each position.

| Source value | Lane 0 | Lane 1 | Lane 2 | Lane 3 |
| --- | ---: | ---: | ---: | ---: |
| `x` | 0 | 1 | 2 | 7 |
| `doubled = x + x` | 0 | 2 | 4 | 14 |
| `difference = x - doubled` | 0 | 2,147,483,646 | 2,147,483,645 | 2,147,483,640 |
| `result = difference - x` | 0 | 2,147,483,645 | 2,147,483,643 | 2,147,483,633 |

The circuit packs `x` into QM31 address `22`, then produces these three
arithmetic values at addresses `23`, `24`, and `25`. It allocates each once;
the helper call itself has no runtime wire. The native Gate AIR groups rows by
gate kind, so source order and physical row order differ:

| Source step | Circuit addresses: left, right → output | AIR selector `(add, sub, mul, pointwise)` | Physical AIR row |
| --- | --- | --- | ---: |
| `x + x` | `22, 22 → 23` | `(1, 0, 0, 0)` | 3 |
| `x - doubled` | `22, 23 → 24` | `(0, 1, 0, 0)` | 474 |
| `difference - x` | `24, 22 → 25` | `(0, 1, 0, 0)` | 475 |

The native output-use counts for these rows are `1, 1, 4`: the first result
feeds the next subtraction, the second feeds the final subtraction, and the
last result feeds the four public output masks. An AIR row is a position in
the arithmetic trace; it does not mean one row per M31 lane. All four lanes
are packed into each of these three rows.

For an add row, the four coordinate equations are
`out[i] - in0[i] - in1[i] = 0`. For a subtraction row they are
`out[i] - in0[i] + in1[i] = 0`, for `i = 0..3`, together with a fixed
one-hot selector and address/multiplicity columns. The first subtraction's
lane 3 equation is `2147483640 - 7 + 14 = 2147483647 = 0 mod p`. Address
`24` is read by the second subtraction; the Gate lookup must bind that read
to the same address *and value* produced by the first. Finally, four unpack
gates bind address `25` to the public output words. The source checker verifies
these three selectors, addresses, grouped row positions and read counts in
the exported fixed columns. The native verifier checks the proof under its
sealed key; the general lookup/PCS soundness proof is still separate work.

The certificate covers this bounded source and native fixed-row schedule.
It does not prove the underlying Gate lookup, PCS/FRI, or verifier soundness.

The [Lean packed-row theorem](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OrderedSubtractionRelease.lean)
proves that **every** auxiliary witness satisfying these three add/sub rows
has output `0 - (x + x)` in all four lanes, and constructs an honest witness
for every input. It also identifies each row with the executable normalized
node operation. The [exact-byte checker](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OrderedSubtractionBytes.lean)
parses the checked-in `manual.s31`, compares every byte of the production
normalized JSON, and rejects a changed subtraction opcode. The
[concrete theorem](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OrderedSubtractionConcrete.lean)
connects those bytes to the arbitrary-witness three-row result. The
[native fixed-cell fixture](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneratedOrderedSubtractionNativeRows.lean)
records the three selected rows exported by the sealed package and checks
their selectors, addresses, and use counts against a Lean projection of the
parsed source. A fresh native check also compares every fixed column and the
AIR geometry of the functional and manual packages. The
[functional byte theorem](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneratedOrderedSubtractionHelper.lean)
checks the helper source itself and proves it has the same normalized DAG as
the manual spelling. The [conditional row theorem](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/OrderedSubtractionHelperNative.lean)
shows that any single coherent address-to-value map satisfying the three
local packed rows forces the helper's public result. Authentication of native
main-row values and Gate lookups, and proof openings remain separate
obligations.
