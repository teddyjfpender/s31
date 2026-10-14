# How `add_const 7` gets its constant

An `add_const` row reads an input word and a four-coordinate constant word.
The row's AIR can prove it added those two words, but does not by itself prove
the second word is seven. [GateAddConstSevenFinalization.lean](GateAddConstSevenFinalization.lean)
closes that value gap for the interned literal `7` by following its producer
chain through native constant finalization.

In the five-lane [fixture](../../../../../scripts/compiler/fixtures/physical_add_const.s31.json),
the source says `shifted = a + 7`. It emits two physical add rows, both reading
constant wire **13**. The checker reconstructs the same finalized circuit and
one accepted proof, then checks these rows against the installed fixed columns
and committed base-root reconstruction. Wire numbers and row numbers here
belong to this fixture; another program may assign different numbers.

| Native operation | Physical row | Input wires | Output wire | Forced value |
| --- | ---: | --- | ---: | --- |
| `Add(0,0)` | 10 | 0, 0 | 0 | zero |
| `Add(1,0)` | 11 | 1, 0 | 1 | one, given the next anchor |
| `Mul(u,one)` | 485 | 2, 1 | 2 | fixes one from public `u` |
| `Add(one,one)` | 12 | 1, 1 | 34 | base 2 |
| five more `Add(previous,one)` | 13–17 | chain | 35–39 | base 3 through 7 |
| `Mul(u,u)` | 486 | 2, 2 | 289 | `2+i` |
| `Sub(2+i,2)` | 481 | 289, 34 | 18 | `i` |
| `Add(i,one)` | 267 | 18, 1 | 290 | `i+1` |
| `Mul(i+1,u)` | 487 | 290, 2 | 291 | `u+iu` |
| `Add(i+1,u+iu)` | 268 | 290, 291 | 292 | `(1,1,1,1)` |
| `Mul(7,ones)` | 488 | 39, 292 | **13** | `(7,7,7,7)` |

The `u` wire has address 2 and public value `(0,0,1,0)`. Native multiplication
`u × one = u` forces the one wire to `(1,0,0,0)`; the 13 value-chain equations
then force the last word to `(7,7,7,7)`. The native audit additionally checks
the zero and one anchoring rows, for 15 rows total. These are QM31 arithmetic
rows. The source
`add_const` rows use that final word as their right input, so each active M31
lane receives seven. For the five-lane fixture, packed row 0 covers lanes
0–3, while packed row 1 contributes only lane 4. Lean proves the result for
any active lane count, including an incomplete last packed word.

The native v3 certificate records all 15 exact row selectors, physical
addresses, and active Gate producer tuples. It checks the row operands and
outputs against the reconstructed committed base cells, then checks the
reconstructed base and interaction roots against the accepted proof. The
Python validator checks the path order and its connection to the canonical
`add_const` node; the native receipt binds the exact certificate bytes. A
changed source constant, changed final broadcast address, missing producer,
or wrong chain input is rejected by the focused controls.

**Proof boundary.** The Lean theorem assumes the path gate roster, local AIR
residuals, the public `u` cell, the active source input/output lane mapping,
and the Gate lookup address/value join. This finite reconstruction
does not prove that an arbitrary accepted proof has all claimed committed
cells or that every LogUp equality is sound; those depend on the outstanding
PCS/FRI and claim-to-cell arguments. The certificate is an audit witness, not
a replacement verifier or a general compiler theorem. Constants other than
seven still need a corresponding finalization proof.

Focused checks:

```sh
(cd formal/s31 && LEAN_NUM_THREADS=1 lake build S31.Gadgets.Air.GateAddConstSevenFinalization)
python3 scripts/compiler/gate_claim_trace_controls.py \
  /tmp/s31-add-const /tmp/s31-add-const.proof \
  /tmp/s31-add-const.proof.statement.json \
  scripts/compiler/fixtures/physical_add_const.valid.json
```
