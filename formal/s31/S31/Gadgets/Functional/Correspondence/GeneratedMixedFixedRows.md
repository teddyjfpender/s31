# Pinned mixed source to fixed AIR rows

This check follows the direct mixed source family at one and eight chip calls.
It ties the source's expected circuit addresses to the eight **preprocessed**
Qm31 columns emitted by the production compiler. The columns are, in order:

```text
add flag | sub flag | mul flag | pointwise-mul flag |
input 0 address | input 1 address | output address | output use count
```

The native exporter compiles the pinned source, builds the same preprocessed
columns as the mixed proving package, checks the source SHA-256 and complete
fixed-column root, and emits all 512 rows for each call count. The Python
renderer independently calculates the row locations, addresses, flags, and
use counts for every pack row, both packed public operations, all unpack and
copy rows, and all scalar bridge endpoint rows. It compares each selected
eight-cell tuple against the native export before writing the Lean fixture.
It also checks canonical M31 cells and the opcode partition across all 512
rows. Pinned SHA-256 digests of the complete row arrays catch changes even
outside the selected paths. The selected schedule check covers 44 physical
rows at `N=1` and 114 at `N=8`.

For example, at `N=1` the first pack addition is native row 0:

```text
row 0: [1, 0, 0, 0, 11, 17, 18, 1]
         add          scalar0 + basis1×scalar1 -> partial1
```

The final packed state is at address 32. The two public operations produce
packed addresses 33 and 34. One unpack mask reads address 33 and produces
address 35; its copy row binds that scalar to public output address 3:

```text
row   6: [1, 0, 0, 0, 22, 32, 33, 4]  packed sum
row 495: [0, 0, 0, 1, 22, 32, 34, 4]  packed pointwise product
row 496: [0, 0, 0, 1, 33,  1, 35, 1]  mask sum lane 0
row   7: [1, 0, 0, 0, 35,  0,  3, 1]  public lane 0 copy
```

At `N=8`, the final packed state is address 102, and the packed sum and
product are at 103 and 104. The bridge's last scalar output is address 96;
its finalization row is row 511:

```text
row 511: [0, 0, 0, 1, 96, 1, 96, 3]
```

`GeneratedMixedFixedRows.lean` proves, by kernel reduction, that both full
exports have 512 rows of eight canonical cells and the expected four-selector
opcode partition. It also proves that the exported row at every hand-derived
selected position equals the expected tuple. It
then proves `selected_fixed_matches`: a decoded direct-Gate trace whose fixed
cells equal this export has `fixedMatches` for every selected pack, public,
and bridge row. This removes a free selected-row fixed-shape premise for the
pinned N1/N8 source family. The theorem does **not** supply the trace's main
values or local AIR acceptance. Those remain the separate `AcceptedRow`
obligations in `SourceMixedPackCorrespondence` and
`SourceMixedPublicClosure`; exact Gate balance and native proof authentication
also remain explicit.

`SourceMixedFixedScheduleBridge.lean` transports these selected fixed cells
to the mixed-chain `ScheduledRow` predicate when the decoded trace rows equal
the source-owned canonical row list. It covers every selected row with
positive output multiplicity, pins the two packed public tail operations for
N=1 and N=8, and proves that every exported output address is below the
native 512-variable bound. Main-value `ValueAt` facts, the full producer scan,
and authentication of the decoded trace remain separate premises.

From the S31 repository root:

```sh
python3 src/frontends/s31/tests/python/generated/render_lean_mixed_fixed_fixture.py --write
python3 -m unittest src/frontends/s31/tests/python/generated/test_lean_mixed_fixed_fixture.py
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.GeneratedMixedFixedRows)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneratedMixedFixedRows)
```

The generator's default mode reruns the native exporter. `--native-json`
accepts a previously captured export for offline review. Omitting `--write`
checks that the committed Lean file still matches the current native output.
