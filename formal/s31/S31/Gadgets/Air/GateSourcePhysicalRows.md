# Source nodes to physical QM31 rows

`gate_claim_trace_audit.py --certificate PATH` emits a checked, public JSON
certificate for one sealed, transparent v1 Gate proof. It derives its node
list from the packaged source bytes. The noninstalled native diagnostic parses
those bytes again, builds canonical IR, compiles both with and without witness
values, and compares the resulting circuits and per-node spans. The packaged
native verifier must first accept the proof; the diagnostic then compares its
reconstructed base and interaction commitments and all component claims.
The audit also checks the sealed source hash, canonical IR hash, preprocessed
root, source map, and fixed QM31 selector/address cells. A caller cannot pass
in a row roster. The certificate is written only after these checks complete.

The compiler has four arrays of binary QM31 gates: add, subtract, packed
multiply, and pointwise multiply. The installed preprocessor concatenates
these arrays in that order, followed by permutation rows. A compiler's
aggregate `qm31_start..end` count is therefore **not** an AIR row interval.
The audit captures four separate spans for every canonical node and adds the
correct class offset before checking the actual fixed AIR columns. It checks
that each class's source spans are contiguous and that the binary prefix ends
exactly where permutation rows begin. All source-owned binary rows are covered;
output binding, finalization, padding, and permutation rows are separate.

## Hand example: common subexpression and physical order

The fixture `scripts/compiler/fixtures/physical_alias_arithmetic.s31.json`
has two four-lane inputs `a` and `b` and the nodes:

```text
sum        = a + b
same_sum   = b + a
difference = sum - b
product    = difference * b
```

The canonical optimizer merges `sum` and `same_sum`; both source names have
canonical ID 2 and packed output address 24. In this built fixture the
source-owned operation intervals are:

| Source name | Canonical ID | Physical row interval | Selector | Output address |
| --- | ---: | ---: | --- | ---: |
| `sum` / `same_sum` | 2 | `[3, 4)` | add | 24 |
| `difference` | 3 | `[474, 475)` | subtract | 25 |
| `product` | 4 | `[503, 504)` | pointwise multiply | 26 |

The large jumps are real: the four operation arrays are grouped by class,
and input setup occupies other source-owned rows. Intervals are half-open;
`[474, 475)` is one row at index 474. There are 9 distinct source-owned
binary QM31 rows in all, although `sum` has two source names. For the input
`a=[1,2,3,4]` and `b=[5,6,7,8]`, the output is `[5,12,21,32]`.

For the add row, the fixed selector is `(1,0,0,0)` and its three fixed Gate
addresses are the two input wires and output wire. The variable columns hold
packed operands `x`, `y`, and `z`. The AIR evaluates nine residuals: one
selector sum, four selector bit checks, and four coordinate equations such
as `z.a - (x.a + y.a)`. If all nine vanish, `z=x+y` in QM31. Subtraction uses
`(0,1,0,0)` and `z=x-y`. The fixture's `mul` source node lowers to a
**pointwise multiply** row with selector `(0,0,0,1)`, so each of its four
lanes satisfies `z_i=x_i*y_i`. Packed QM31 multiplication has its own
selector `(0,0,1,0)` and a different four-coordinate polynomial.

`GateSourcePhysicalRows.lean` proves the row equation for **any** finite
source/canonical map and any number of physical rows. Its premises say that
source aliases have the same canonical row list, the checked fixed selectors
label the rows, and the installed nine residuals vanish. The result is the
operation equation for every listed row. The theorem uses the exact
source-generated native residual tree, whose equality to the readable
`Qm31Ops` residuals is proved separately. It also proves that two source
names with the same canonical ID have the same row list.

The native diagnostic checks one supplied witness against one accepted proof;
it does not establish that all accepted proofs have those reconstructed trace
cells. The Lean theorem assumes the source/canonical mapping and local AIR
residuals; it is not a proof of the parser or arbitrary-proof PCS/FRI
authentication. For source operations more complex than primitive add,
subtract, and pointwise multiply, the certificate covers their owned binary
rows and fixed cells, while whole-operation semantics still needs a
composition theorem. Gate lookup, public pin ownership, other component AIRs,
and global LogUp remain separate obligations. This certificate is a diagnostic
artifact, not a verifier input or a release admission claim.

## Reproduce

```sh
python3 src/frontends/s31/python/s31.py build \
  scripts/compiler/fixtures/physical_alias_arithmetic.s31.json \
  --out /tmp/s31-physical-alias --lowering gate
python3 src/frontends/s31/python/s31.py prove \
  /tmp/s31-physical-alias \
  scripts/compiler/fixtures/physical_alias_arithmetic.valid.json \
  /tmp/s31-physical-alias.proof
python3 scripts/compiler/gate_claim_trace_audit.py \
  /tmp/s31-physical-alias /tmp/s31-physical-alias.proof \
  /tmp/s31-physical-alias.proof.statement.json \
  scripts/compiler/fixtures/physical_alias_arithmetic.valid.json \
  --certificate /tmp/s31-physical-alias.certificate.json
python3 scripts/compiler/gate_claim_trace_controls.py \
  /tmp/s31-physical-alias /tmp/s31-physical-alias.proof \
  /tmp/s31-physical-alias.proof.statement.json \
  scripts/compiler/fixtures/physical_alias_arithmetic.valid.json
(cd formal/s31 && lake build S31.Gadgets.Air.GateSourcePhysicalRows)
```
