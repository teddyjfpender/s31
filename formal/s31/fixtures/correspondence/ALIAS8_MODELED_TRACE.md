# Case07 alias program: complete modeled direct-Gate trace

`case07` is an eight-producer public `[m31; 4]` circuit with aliases and a
selected earlier result (`p4`). Its source, normalized JSON, canonical IR,
native fixed roster, diagnostic base rows, and accepted proof are pinned by
the compiler correspondence fixture. The Lean instance here establishes a
separate **modeled** physical trace for every four-lane input.

## Reproduce the fixture

From the S31 repository root:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py
python3 src/frontends/s31/tools/formal/alias8_native_fixture.py --check
```

The generator reads `case07-full-native-roster.json`, pins its SHA-256, and
runs the full Python roster check before emitting
`GeneratedAlias8NativeFixture.lean`. That check independently reconstructs
the 512 fixed rows from the source DAG and host schedule, compares the sealed
fixed root and all 4,096 fixed cells, checks 6,144 coherent main words, all
4,608 installed arithmetic roots, public seed/output values, and the exact
Gate address/value ledger. The direct source spelling is also parsed and
required to produce the same normalized relation as the alias spelling.

The generated Lean data contains the **479 native constant/padding cells** in
role order, plus one 512-entry QM31 value table indexed by produced address.
The value table comes from the single honest public diagnostic export at
`[0,1,2,7]`; the proof for arbitrary input does not reuse that export's
source-specific values. It uses the checked island's fixed seed/basis/inverse
values and the independent source/public wire constructor to assign each new
input coherently.

## What Lean checks

`Alias8ConstantIslandCertificate.alias8_constant_check` checks all 479
constant cells against the exact case07 certificate. It covers their row
roles, allowed addresses, unique outputs, seed values, and nine local
arithmetic residuals. Sixteen-cell chunks bound Lean's reduction cost.

`Alias8CompleteModeledTrace.direct_spelling_check` admits a simple
producer-only spelling against the exact normalized bytes;
`GeneratedNativeSourceCells.case07_source_to_native_cells` separately admits
the alias source and canonical IR and matches its eight source cells to native
fixed rows. `complete_address_check` checks the exact 512-cell address
multiplicity ledger, including the nine modeled public feeder addresses.

`Alias8CompleteModeledTrace.complete_modeled_trace` then gives, for **every**
four-lane input, an alias-denotation result and a synthetic 512-row trace.
Each row has its required fixed cell; all installed local arithmetic roots
vanish; the selected output is the packed source result; and the trace's
ideal Gate events balance. The theorem's producer-only spelling check remains
an explicit premise of the reusable alias bridge.

## Boundary of this result

The JSON base rows are diagnostics produced by `writeBase`. They are not
authenticated PCS openings. The Lean theorem does not identify its synthetic
trace with the rows committed in an accepted native proof, and it does not
prove native LogUp, FRI, or the Zig compiler correct. The separate native
acceptance and main-root regression checks are evidence for those specific
fixture bytes; they do not close that general correspondence gap.
