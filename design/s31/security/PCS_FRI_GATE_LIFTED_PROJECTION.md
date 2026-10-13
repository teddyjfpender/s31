# P03: gate lifted-tree and per-column query indices

The diagnostic covers a sealed `gate`/`circuit-v1` leaf package with FRI
fold step 1. It does not modify package artifacts, but runs the package's
native `check-key` executable; use only a locally trusted binary. Manifest
hashes check internal consistency and do not establish executable provenance.

```sh
python3 -B scripts/release/pcs_fri_gate_lifted_projection.py /path/to/sealed-gate-package
python3 -B scripts/release/pcs_fri_gate_lifted_projection.py /path/to/sealed-gate-package --require-p03
```

The second command exits 2 while the global P03 oracle relation is open.
The first reuses the sealed gate P01 checks, pins the relevant PCS, lifted
Merkle and S31 capture-source branches, and emits each tree's column groups.
A group has a starting column index, count, extended column log `c`, and the
exact projected index formula for every column in the group. Its source
hashes and package/key hashes let a reviewer reproduce the diagnostic. The
`leaf_hash_column_order` array separately gives the native log-size sort
order, with original column index breaking ties; the groups use original
proof column order.

For the local sealed `affine_guard` package, the verified key has trace log
20, blowup log 1, and composition column log 20. All four nonempty native
trees have explicit height `H=21`. Their columns are:

| Tree | Columns | Natural height | Extended column logs |
| --- | ---: | ---: | --- |
| Preprocessed | 45 | 21 | 5, 9, 10, 15, 17, 19, 21 |
| Main trace | 114 | 21 | 5, 9, 10, 15, 17, 19, 21 |
| Interaction trace | 152 | 21 | 5, 9, 10, 15, 17, 19, 21 |
| Split composition | 8 | 21 | 21 |

The preprocessed column logs come from the sealed roster. The main and
interaction counts come from its component widths, which the installed
`check-key` rebuilds from the sealed source. `logsFor` repeats each component
trace log by its width. The composition count is
`2^COMPOSITION_LOG_SPLIT * QM31.SECURE_EXTENSION_DEGREE = 2 * 4 = 8`.
Every column log is extended by the FRI blowup log when committed, and
`PcsConfigV2.treeHeight` requires that it fit under `H`.

For a raw query `q < 2^H`, the PCS capture path calls
`prepareTreeQueryPositions` with the last tree's lifting log `H` and each
tree's explicit height `H`, so the path passed to `verifyWithPathCapture`
retains `q` in exact raw order and multiplicity. A column at extended log
`c` has projected index

```text
P(H,c,q) = 2 * floor(q / 2^(H-c+1)) + (q mod 2).
```

The low bit selects the same conjugate-circle half. For example, at `H=21`,
`q=7` projects to index 1 in a log-5 column and stays 7 in a log-21 column.
The native prover builds smaller-column leaves at their natural height and,
when needed, replicates their leaf hashes to the explicit height. The Lean
theorem `projectedPosition_compose` proves that projection from height `H`
to natural height `T`, then to column height `c`, equals direct `P(H,c,q)`
for **arbitrary** `c ≤ T ≤ H`. `gate21_tree_column_position` specializes it
to this package's height. The theorem proves an integer-index identity; it
does not extract values from Zig, identify a committed oracle, or establish
Merkle authentication.

The source guard pins the `verifyWithPathCapture` branch's explicit height,
range rejection, stable column sort, duplicate-value rejection, row hashing,
root check, and raw-order capture. Mutation tests remove or alter those
anchors. They do not prove Zig execution semantics or that a successful
capture's row equals a fixed cross-domain oracle. The latter still needs
source-to-binary correspondence, native-success extraction, a committed
oracle ownership premise, collision reduction, and a cross-domain IOP and
proximity theorem. P03 remains open.

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_lifted_projection scripts.tests.test_pcs_fri_projection -q
```
