# An interned `add_const` value from native finalization

An S31 `add_const k` becomes one QM31 add gate per four active M31 lanes. The
right input of each gate is an interned wire holding `(k,k,k,k)`. The add AIR
alone says that the two input **values** were added; it does not say where the
right value came from. `GateConstantDAG.lean` proves the missing local value
step for any canonical nonzero `k < 2³¹−1`, provided the actual finalization
gates, their AIR equations, and their trace-cell joins are authenticated.

The native circuit builder constructs constants with a shared graph. It starts
from reserved zero, one, and `u` wires; creates small integers by addition;
uses radix decomposition for larger integers; and builds the QM31 broadcast
basis by additions, subtraction, and multiplication. The builder may share
intermediate wires between constants, so the certificate records a **DAG**, not
an assumed fixed chain. A zero source literal is canonicalized to an alias
before this path. A one literal still uses its real native broadcast path.

For a small hand example, if a gate produces `two = one + one` and another
produces `three = two + one`, their AIR equations are

```text
two   − (one + one) = 0
three − (two + one) = 0
```

Once the `one` wire is fixed, the first equation forces `two = 2`, and the
second forces `three = 3`. The same induction works for a branch or shared
subexpression. Multiplication uses the native four-coordinate QM31 product;
its operation is not a coordinatewise multiply. The final gate must reach the
exact interned wire read by each `add_const` row and evaluate to `(k,k,k,k)`.

## What the v4 certificate checks

For each canonical `add_const` node, the source-derived certificate contains
its literal, the interned constant address, the source-owned add rows, three
anchor rows, and a topologically ordered list of finalization rows. It checks
the installed fixed selectors and addresses, active Gate producer lookups,
and those rows' values in the reconstructed committed base trace. Its
independent Python evaluator starts from `zero = (0,0,0,0)`,
`one = (1,0,0,0)`, and `u = (0,0,1,0)`, computes every DAG edge in QM31, and
requires the last wire to equal the source literal broadcast. It rejects
unknown inputs, duplicate outputs, unused edges, changed constants, and
changed addresses. The native receipt hashes the exact certificate bytes.

The zero self-add row forces zero. The `u × one = u` row fixes one because
public `u` is a nonzero field element; the public output event fixes `u`.
The remaining anchor row is `one + zero = one`. These are installed Gate rows,
not values merely asserted in the certificate.

For the five-lane fixture, `shifted = a + 7` uses two source-owned add rows,
because the second packed row contains only one active lane. The interned
constant is wire **13**. Its original 15-row literal-seven derivation is
listed [here](GateAddConstSevenFinalization.md); v4 also records the same
value as a generic DAG. Each source add row reads address 13 as `in1`, so the
native add residual then forces each active lane to be its input plus 7.
The theorem composes this DAG value with the existing arbitrary-length
active-lane `add_const` theorem.

The focused controls prove and audit several real packages, including `1`,
`7`, the radix boundary `255/256`, `65535`, and `p−1`. They mutate the
literal, DAG input, or final edge while holding the accepted proof fixed. In
the pinned builder, the six accepted dependency paths have the following
sizes; each package still has only two source-owned packed add rows:

| Source literal `k` | Finalization DAG rows, including 3 anchors |
| ---: | ---: |
| 1 | 9 |
| 7 | 15 |
| 255 | 263 |
| 256 | 264 |
| 65535 | 266 |
| 2147483646 (`p−1`) | 270 |

The default native builder creates a plus-one chain through base 256, which
accounts for the long paths near that base. These counts describe audit
dependencies in the current implementation; this work does not reduce the
prover's constant-finalization cost.

```sh
(cd formal/s31 && LEAN_NUM_THREADS=1 lake build S31.Gadgets.Air.GateConstantDAG)
python3 scripts/compiler/gate_constant_dag_controls.py
```

**Boundary of this result.** The Lean induction ranges over an arbitrary
finite topologically ordered gate DAG, but assumes its roster and native AIR
equations. The v4 native audit reconstructs one supplied witness and compares
its base and interaction roots with one accepted proof. Python checks the
source-derived certificate and exact native receipt, but trusts native
extraction of physical cells. Neither checker proves that *every* accepted
proof authenticates those cells, nor that global LogUp balance follows from
PCS/FRI acceptance. The general compiler correspondence and release gate
therefore remain open.
