# Finite Gate claims and arbitrary event lists

`GateClaimTraceJoin.lean` removes the fixed control program and fixed public
output length from the claim-to-Gate argument. For any finite public output
list, QM31 row list, external component producer list, and component use list,
it proves a conditional chain:

```text
native final sum = 0
  + 11 claimed values equal the signed sums of authenticated cells
  + canonical addresses, bounded tuple counts, good challenges
  -> exact Gate use/yield multiset balance
  + unique active producer-address roster
  -> each public output lookup equals its one produced wire value
  + vanishing local QM31 AIR residuals
  -> each active QM31 row evaluates on those same wires
```

An external producer is one physical row with an address, four M31 limbs,
and a fixed multiplicity. A multiplicity of three creates three identical
Gate yield events but just **one** logical producer. The theorem derives
coverage of all such events from the producer rows; callers no longer supply
an unexamined external-event coverage premise. The public event list includes
the native fixed `u` event at address 2 and one event per public word at
addresses 3, 4, and so on. Six-word Gate events are padded with zero to match
the verifier's seven-word compression.

The diagnostic in `scripts/compiler/gate_claim_trace_audit.py` works on a
sealed **v1, transparent, legacy, single-fold Gate package**. It verifies
the package and runs its native verifier. The noninstalled Zig diagnostic
then parses the packaged source, evaluates **all** source nodes independently
of circuit compilation, derives the canonical source map and physical spans,
checks that consecutive source spans leave no gap in each tracked gate class,
and compares witness-bearing and witness-free compiler topology and spans.
It checks the ordered public output cells against the source evaluator and
statement; reconstructs both committed trace roots and all eleven component
claims; and enumerates active QM31, triple XOR, M31-to-u32, and Blake G
Gate-yield tuples from actual base/fixed cells. The caller supplies a private
assignment to reconstruct **one** proof. It cannot supply a trusted row roster
or output pin map to the audit.

Three accepted circuit shapes have been exercised: the scalar control
fixture (`[329,0,5,0]` active producers), `functional_square4.s31`
(`[321,0,8,0]`), and `hash4.s31.json` (`[438,8,12,320]`). The count order is
QM31, triple XOR, M31-to-u32, Blake G. The hash case exercises all four
producer classes. For the hash case, appending an **invalid unused** node with
an unknown operand fails source parsing. Appending a **valid unused**
`add_const` node leaves the public expression unchanged but changes the
compiled fixed circuit root; the unchanged proof is rejected. Thus the
finite audit covers source nodes even when the output does not reference
them. The canonical optimizer may merge two source nodes into one physical
span; the source map explicitly records that alias.

The Lean theorem is a **conditional event bridge**, not a full compiler
correspondence or proof-system soundness theorem. Its `CellClaims` premise
still asserts that the eleven accepted claims equal sums derived from
authenticated committed cells. The local QM31 AIR premise, unique active
producer roster, and good-challenge assumptions are explicit. The finite
diagnostic checks one supplied witness against one accepted proof, but does
not show that every accepted proof has that witness. Native PCS/FRI
authentication and global LogUp soundness remain open release blockers.

## Reproduce with a built Gate package

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/hashes/hash4.s31.json \
  --out /tmp/s31-hash4-gate --lowering gate
python3 src/frontends/s31/python/s31.py prove \
  /tmp/s31-hash4-gate \
  src/frontends/s31/examples/hashes/hash4.valid.json \
  /tmp/s31-hash4-gate.proof
python3 scripts/compiler/gate_claim_trace_controls.py \
  /tmp/s31-hash4-gate /tmp/s31-hash4-gate.proof \
  /tmp/s31-hash4-gate.proof.statement.json \
  src/frontends/s31/examples/hashes/hash4.valid.json
(cd formal/s31 && lake build S31.Gadgets.Air.GateClaimTraceJoin)
```
