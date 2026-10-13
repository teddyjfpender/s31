# Conservative dead-code pruning model

[`ConservativeDeadCode.lean`](ConservativeDeadCode.lean) models the source
optimizer's liveness decision over positional SSA nodes. It deliberately has
one narrow erasable class: M31 constants, addition, multiplication, and their
constant-operand forms. Inputs, assertions, and arbitrary partial or effectful
operations remain roots. A retained node keeps every wire it reads.

Consider this hand-written graph, with `x` as the public input:

| ID | Node | Reads | Why it stays |
| --- | --- | --- | --- |
| 0 | `x = input[0]` | — | Needed by nodes 2 and 4 |
| 1 | `unused = 7` | — | Removed: total arithmetic, no readers |
| 2 | `square = x * x` | 0, 0 | Needed by the check and output |
| 3 | `assert square == x` | 2, 0 | Assertion is always observable |
| 4 | `output = square + x` | 2, 0 | Public output root |

The backward scan starts with IDs 3 and 4. Their dependencies bring in IDs 2
and 0; ID 1 never becomes live. The retained mask is
`[true, false, true, true, true]`, and the output remains `x² + x` in M31. At
`x = 2`, the output value is `6`, but the assertion fails (`4 ≠ 2`) in **both**
graphs. Erasing the assertion would make the pruned graph accept a computation
the source rejects.

`Needed` is the least logical closure of public outputs, ABI leaves, assertion
IDs, all other non-erasable nodes, and references of live nodes.
`reachableMask_safe` shows that closure meets `SafeMask`: roots stay, effects
stay, and every kept node's references stay. `retained_value_eq` then proves,
for every input and fuel depth, that each kept wire has the same `Option M31`
result before and after erasure. `observations_eq` applies this to output and
assertion lists. The equality includes `none`, so a modeled failed check is
preserved. `effect_value_eq` covers each retained partial/effect node's
returned value or failure.

The production text compiler now checks each changed normalized relation
with an [independent pruning certificate](../../../../../../src/frontends/s31/docs/reference/PRUNING_CERTIFICATE.md).
It requires exact retained-node identity, reviewed total removals, preserved
roots and dependencies, and matching source locations. A failed check stops
compilation before AIR lowering.

The model does **not** establish that Python `dead_code.py` computes this
closure or that the certificate checker implements the Lean predicates. It
assumes positional IDs, a reviewed list of dependencies, and a
deterministic value/failure semantics for external operations. It does not
model external I/O event order, source spans, record ABI validation, JSON
serialization, the Zig compiler, AIR emission, or native proof verification.
Those are separate correspondence and authentication obligations. The Python
pass's fail-closed shape checks and native acceptance tests provide executable
evidence for its concrete implementation, but are not a Lean refinement
theorem.

Focused check:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.ConservativeDeadCode
lake env leanchecker S31.Gadgets.Functional.Correspondence.ConservativeDeadCode
```
