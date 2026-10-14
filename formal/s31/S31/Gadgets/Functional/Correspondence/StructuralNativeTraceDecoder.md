# Structural native trace decoder

[StructuralNativeTraceDecoder.lean](StructuralNativeTraceDecoder.lean) accepts
the independently parsed S31 source bytes, a canonical effectful SSA
certificate, and a bounded projection of the Zig
`s31-structural-m31-exact-native-graph-v2` JSON export. It is an executable
Lean bridge from **supplied source and graph bytes and concrete values** to the
`NativeTrace` premise of
[StructuralNativeGateCertificate.lean](StructuralNativeGateCertificate.lean).

## Hand calculation

Take one active M31 lane and the source step `z = x - y` with `x = 1`,
`y = 0`. A graph has source IDs `0, 1, 2`, packed addresses `0, 1, 2`,
and four-coordinate values

| Address | Coordinates | Source ID |
| --- | --- | --- |
| 0 | `[1, 1, 1, 1]` | `x` |
| 1 | `[0, 0, 0, 0]` | `y` |
| 2 | `[1, 1, 1, 1]` | `z` |

The gate roster contains `Sub(in0=0, in1=1, out=2)`. `checkGates` checks
`wire[2][j] = wire[0][j] - wire[1][j]` for **each** physical coordinate
`j = 0, 1, 2, 3`. `checkNativeStep` checks that the SSA step has fresh
source ID 2, reads prior IDs 0 and 1 from the selected addresses, and appends
the computed active-lane value. The decoder checks the two input ports, the
selected public result, and every source assertion. For a source step whose
compiler output is an alias or fold, the same value equation can pass without
requiring a newly emitted gate.

`checked_exported_graph_trace` proves that successful checking constructs
`NativeTrace` for **any admitted step list**. With a certificate accepted by
`checkEmittedSSA`, `checked_exported_graph_sound` concludes that the supplied
claim equals the modeled source result and that modeled assertions hold.

`checkSourceNativeGraph` composes those checks with the independent source
parser and canonical SSA certificate decoder. It requires 1–4 lanes and
compares the complete ordered `source_map` name list with the parsed SSA input
and node names. `checked_source_native_graph_sound` proves that every accepted
claim belongs to the parsed S31 source denotation for **any step list admitted
by this bounded grammar**. The theorem's admission premise is successful
execution of the composite checker on the supplied bytes and values.

The module includes a hand-written JSON projection fixture with all required
top-level keys. Its ignored fields are placeholders, so it is not claimed to
be a full Zig-emitted graph. A mutation that changes
`x`'s source-to-wire address from 0 to 1 is in range and parses, but the
port/step check rejects it. Changing the output coordinates from 1 to 2 also
parses as canonical M31, but violates the subtraction gate equation. Out of
range canonical IDs and noncanonical M31 coordinates fail in the decoder.
The [runtime control](../../../Audit/StructuralNativeTraceDecoderCheck.lean)
accepts actual Zig-exported graphs for a commutative common subexpression and
two erased identity steps. In both cases, exchanging the same-length source-map
names of the two inputs while preserving IDs, addresses, gates, and values is
rejected specifically by the new source-map name check.

## What the checker reads

The decoder requires the exact top-level field **names** and schema tag of
the v2 export, canonical four-word values, in-range add/sub/pointwise-mul gate
addresses, and a source-map-to-canonical-node-to-one-packed-wire chain. The
composite checker also binds the complete ordered source-map names to the
independently parsed SSA. It
bounds input bytes to 8 MiB, variables to 262144, and projected gates to
262144. It does **not** validate the deeper content of other fields, including
full QM31 multiplication, Eq, input conversion, finalization, or padded AIR
rows. The separate Python topology/witness audit handles those fields for
bounded assignments, including source-pinned input packing, source-node,
assertion, public conversion, and constant-finalization replay. Lean JSON
parsing does not establish that the exporter
emitted these particular bytes or rule out alternate JSON spellings with the
same parsed object.

## Remaining proof boundary

Theorems in this module establish a semantic statement about supplied bytes
and values. A production correspondence result still needs to show that:

1. the installed Zig compiler and its source-map export produced the bytes
   checked here, with exact input, source-node,
   assertion, public binding, and finalization spans independently replayed
   by the bounded Python audit;
2. each projected wire value and fixed gate cell is authenticated against the
   committed AIR trace, including the source-to-gate ownership of compiler
   aliases and folds; and
3. the installed verifier, PCS/FRI checks, and Fiat–Shamir transcript establish
   those AIR premises for a proof.

The module does not claim those joins or a native soundness level. Its tests
exercise fresh Zig exports, but the theorem itself makes no installed-binary
provenance claim and has no compiler fingerprint dependency. The export-custody
guard elsewhere is a local-process guard with a no-concurrent-writer assumption;
it does not establish a universal compiler refinement theorem.

Focused check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake build \
  S31.Gadgets.Functional.Correspondence.StructuralNativeTraceDecoder \
  s31-structural-native-trace-check
python3 tests/audit/structural_native_trace_decoder.py
```
