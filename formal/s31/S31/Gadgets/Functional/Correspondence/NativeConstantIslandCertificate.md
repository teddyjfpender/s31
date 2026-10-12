# Direct Gate constant island certificate

The direct Gate profile has 512 physical rows. A checked source of `n ≤ 16`
instructions contributes `n` source rows and 25 public input/output rows. The
remaining `487 − n` rows form the constant derivation and padding island:

| Role | Physical rows | Count |
| --- | --- | ---: |
| Constant and padding adds | `11 + sourceAddCount` through `compiledAddRows − 1` | `465 − n` |
| Constant subtraction | `compiledAddRows` | 1 |
| Constant multiplications | `compiledAddRows + 7` through `compiledAddRows + 27` | 21 |

`NativeConstantIslandCertificate.check` accepts a list of fixed gate cells and
one `address → QM31` value table. It checks the exact row list, one-hot selector
at every row, isolated constant addresses, canonical fixed words, a value at
every operand and output address, all nine local arithmetic residuals, unique
output addresses, and the seed, basis, and inverse-basis values and producers.
The theorem `checked_cells_arithmetic` extracts the true arithmetic relation
from a successful Boolean check. `checked_rows_count` proves exact island size.

The allowed shared addresses are 0, 1, 2 (seeds), 15 and 16 (basis), and the
three inverse-basis addresses `25+n`, `28+n`, and `31+n`. Other island addresses
start at `33+n`. The checker excludes source and public data addresses from
constant cells. When combining this island with a source/public witness, one
must still prove that both value maps agree at each shared address.

`PinnedSquare4ConstantIslandCertificate` instantiates the checker with the
square4 native fixed rows and a 512-address value table generated from the
pinned native physical export. The generator validates its source schema,
column dimensions, canonical M31 words, and the exact permutation of output
addresses before emitting the table. Use:

```sh
python3 -B src/frontends/s31/tools/formal/pinned_constant_values.py --check
cd formal/s31
LEAN_NUM_THREADS=1 lake build \
  S31.Gadgets.Functional.Correspondence.PinnedSquare4ConstantIslandCertificate
```

This proof checks a concrete pinned example and a reusable certificate
contract. It does not prove that arbitrary Zig compilation emits the
certificate cells, that committed columns equal the decoded cells, that the
Gate lookup balances across all rows, or that the production PCS verifier
authenticates the values. Those are separate correspondence obligations.
