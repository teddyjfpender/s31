# Private witness extraction from a record-v2 Gate trace

This is the private-input direction missing from the source-to-physical result
theorem. The bounded source fragment has one-word M31 record fields and `+`
and `.*` nodes. The theorem starts with a public statement and an **arbitrary**
decoded 512-row Gate trace. It never receives a private assignment.

For example:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit combine(public visible: Pair, private secret: Pair) -> public Pair {
    let sum = visible.left + secret.left;
    let product = sum .* visible.right;
    Pair { left: product, right: sum }
}
```

The public statement can fix `visible=(2,3)` and the result `(18,6)` without
revealing `secret`. The decoded Gate map may have `wire[15]=4` and
`wire[16]=5`. The theorem extracts those canonical words and constructs
`privateInputs=[("_s31_abi_input_2",[4]),("_s31_abi_input_3",[5])]`.
It then proves that the **actual** normalized `Program.evaluate` accepts the
constructed assignment and the public claim.

The proof has three independent parts:

1. `trace_cell_accept` applies the installed nine local arithmetic roots to
   a decoded row. Ideal exact Gate balance and unique production turn its
   read/write values into one address-indexed wire map. A positive
   multiplicity is required for a row output to enter that map.
2. `checkStatic` runs `checkSourceTopology` on the source reconstructed from
   exact bytes and stores its proof in the admission certificate. The name
   check verifies operand availability and result references without reading
   any values. `checked_topology_total` then proves the scalar source graph
   executable for **every** canonical input. Explicit regressions reject an
   unavailable operand and an unavailable result name.
3. `private_assignment_exists` extracts private words from the Gate map,
   checks the public input partition, propagates source values through all
   live source cells, checks public output pins, and invokes the independent
   scalar-to-typed evaluator correspondence theorem.

The theorem explicitly assumes that the supplied complete fixed-cell list
matches the decoded trace, **every** source arithmetic node has a cell with
positive
multiplicity, local arithmetic roots vanish, Gate events balance exactly,
produced values are unique, input cells are scalar, and public inputs and
outputs are pinned to the same wire map. `checkFixedSourceCells` verifies the
512-row fixed list's unique positions and source selectors/addresses; it does
not authenticate the fixed-root commitment. A
dead-source-node elimination theorem would remove the live-cell restriction;
the theorem does not silently assign a positive multiplicity to all 512 rows.

This is a **conditional ideal trace theorem**, not a native verifier theorem.
Native PCS/FRI must authenticate the fixed and main commitments, the LogUp
argument must reduce verifier acceptance to exact Gate balance at the chosen
security profile, and Fiat–Shamir must justify the challenge distribution.
The current theorem assumes those decoded-trace facts directly. It also
requires the public partition checks to pass for the accepted source package.
The pinned narrow record release invokes `checkStatic` through its Lean CLI,
so it runs the topology check. This does not wire the broader native verifier
or all record-v2 packages through that Lean admission path.
