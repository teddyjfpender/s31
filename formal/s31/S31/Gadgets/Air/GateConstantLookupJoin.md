# An interned constant through the exact Gate relation

`GateConstantDAG.lean` evaluates a compiler constant from its actual
finalization DAG, assuming a single wire value for each address and AIR
acceptance for every DAG gate. `GateConstantLookupJoin.lean` constructs that
wire assignment from physical Gate rows under an **exact multiset balance**
premise. It applies to any finite row list, any canonical nonzero source
literal admitted by the DAG certificate, and any number of active M31 lanes.

## A row by hand

Take two produced Gate events, `(7, 5)` and `(8, 3)`, and one add row:

```text
address:       left=7       right=8       output=9
trace values:       5             3              8
local AIR:                 8 − (5 + 3) = 0
Gate uses:       (7,5)        (8,3)
Gate yields:                              (9,8)
public use:                               (9,8)
```

The use multiset `{(7,5), (8,3), (9,8)}` equals the yield multiset. The
unique producer roster contains addresses `7, 8, 9`. The Lean example
`example_owner_air` checks that the local row AIR transfers to the one
addressed wire map. In the adversarial example, the row reads `(7,4)` and
locally computes `4+3=7`, while the external producer still yields `(7,5)`.
Its arithmetic AIR passes but exact Gate balance fails.

For a real `add_const k`, the compiler's finalization rows produce the
broadcast `(k,k,k,k)` at one address. Each packed source add row reads that
address as its right operand. Exact balance and a unique producer at each
address force the row's four right values to equal the DAG value. The native
nine residuals then give, for every active lane `j`:

```text
output[j] = input[j] + k mod (2³¹−1).
```

The last packed row may have fewer than four active lanes. No value is
claimed for inactive padding lanes. The `u=(0,0,1,0)` anchor comes from the
public producer event; the existing zero self-add and `u × one = u` rows
derive the other two anchors.

## Assumptions and provenance

| Fact | This module's treatment |
| --- | --- |
| One positive physical row owns each finalization gate and source add row, with installed address and selector | Explicit `Owner` and source row premises, checked for finite native packages by the existing v4 certificate audit |
| Row arithmetic residuals vanish | Explicit physical row premises; `owner_air` transfers them to coherent addressed wires |
| The full Gate relation balances as an exact event multiset | Explicit `balanced` premise |
| Each produced address has one logical owner, allowing multiplicity copies of the same output | Explicit no-duplicate positive producer roster and external coverage premises |
| Source input/output active lanes are bound to the selected physical row | Explicit source port premises |
| Arbitrary accepted proof authenticates these cells, row roster, public event, and exact lookup balance | **Open**: requires native verifier/PCS/FRI correspondence and the probabilistic LogUp reduction |

This theorem removes independent *value* assumptions about the finalization
gates and the source row's constant operand once the exact Gate and physical
row premises hold. It does not assert a production verifier theorem or change
the release status.

```sh
(cd formal/s31 && LEAN_NUM_THREADS=1 lake build S31.Gadgets.Air.GateConstantLookupJoin)
python3 scripts/compiler/gate_constant_dag_controls.py --constant 7
```
