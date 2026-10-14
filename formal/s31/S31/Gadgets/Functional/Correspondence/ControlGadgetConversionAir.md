# Why the public conversion cannot wrap around M31

The [public pin example](ControlGadgetPublicPins.md) passes each extracted
M31 scalar to one `m_31_to_u_32` row. The row's committed base cells are
`x` (input), `l` (low limb), `h` (high limb), and `v` (inverse or one). The
installed AIR has exactly these two arithmetic residuals, each required to
be zero in M31 where `p = 2³¹−1`:

```text
R₀ = (x·v − 1)·l
R₁ = x − (l + 65536·h)
```

The row uses the `RangeCheck_16` lookup table for `l`, `h`, and `32767−h`.
The table contains exactly the integers from 0 through 65535. Together,
those three memberships imply `0 ≤ l ≤ 65535` and `0 ≤ h ≤ 32767`.
Its Gate lookups read `(input_address, x)` and write
`(output_address, l, h)` with the installed multiplicity. For the five live
public words, the source-bound topology audit fixes those addresses to the
public input and four extracted result lanes.

| Candidate | `l` | `h` | Integer `l + 65536·h` | `R₁` for `x=0` | `R₀` for `x=0` |
|---|---:|---:|---:|---:|---:|
| Canonical zero | 0 | 0 | 0 | 0 | 0 |
| Wraparound alias | 65535 | 32767 | 2147483647 = `p` | 0 in M31 | `−65535`, nonzero |

The second row alone would let the wraparound alias represent zero. The
first row rejects it for **every** `v`, because `0·v−1 = −1`. Once this
case is excluded, the bounded integer sum is strictly below `p`; the M31
equation `R₁=0` becomes an ordinary integer equality. Division by 65536
then uniquely fixes `l = x mod 65536` and `h = floor(x/65536)`.

`ControlGadgetConversionAir.lean` proves this for arbitrary satisfying row
cells. Its public-pin theorem derives the earlier conversion-component law
from these exact residuals and explicit lookup closure facts. The source
guard checks the pinned native evaluator bytecode's component identity,
residual registers, root order, and the witness implementation's ordered
range and Gate tuples. Mutation tests change both the bytecode and a range
tuple. This is a guarded source correspondence; the guard itself is Python,
and the Lean theorem does not verify its implementation.

The theorem's remaining premises are precise: the three range tuples must
be authenticated as members of the fixed table, and the Gate input and
output tuples must agree with the addressed physical wires. Those are
consequences expected from the installed global lookup argument, whose
soundness and committed-trace authentication are not established here.
Likewise, binding the public statement bytes to those committed pin cells
and native PCS/FRI soundness remain open. The v0.1 release blocker stays
closed.
