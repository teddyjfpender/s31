# Native source-row refinement fixture

The bounded direct Gate correspondence checker already reparses source bytes,
checks the complete 512-row native topology, and compares source rows against
the exported eight fixed columns. This fixture adds a finite Lean-visible
bridge for four pinned programs with one, eight, fifteen and sixteen source
gates. The eight-gate source uses aliases; the sixteen-gate source uses
comments and returns an earlier result, leaving some eager gates unused.

`native_source_cells.py --native --write` builds each source through the
production direct Gate package path. It obtains a fresh `inspect-topology`
export from the native prover and requires equality with the sealed package
topology. It runs the existing package checker, checks exact source,
normalized and canonical IR digests, and compares each source-owned physical
row with an independently enumerated positional DAG. It saves the observed
eight fixed cells at every source row, the full 4096-cell export digest, and
the native preprocessed root. The JSON fixture also stores the exact UTF-8
source and normalized JSON, the native prover binary hash, the runtime
exporter and relation lowering source hashes, and the pinned Stwo engine
gitlink. The generated Lean module checks those observed
cells against the certificate parsed from the exact source bytes and the
modeled source-derived add partition.

For the one-product source, the add partition has 475 rows. The native
pointwise product is physical row `475 + 28 = 503`, with selector
`[0, 0, 0, 1]`, both input addresses `22`, output address `23`, and output
use count `4`. The Lean equality checks all eight cells and the row number.

Fast source and fixture check:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_source_cells.py
```

Fresh native comparison and Lean replay:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_source_cells.py --native
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.GeneratedNativeSourceCells)
(cd formal/s31 && lake env leanchecker -v S31.Gadgets.Functional.Correspondence.GeneratedNativeSourceCells)
```

The fixture establishes equality for these four source-pinned native
exports. Exporter correctness remains an explicit assumption: these checks
cannot prove a universal theorem for Zig's emitter or bind
an arbitrary proof's committed fixed columns to this export, authenticate
main witness values, or prove lookup, PCS, FRI or Fiat–Shamir soundness.
