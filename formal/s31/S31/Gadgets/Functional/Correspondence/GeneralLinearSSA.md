# General linear M31 SSA correspondence

[`GeneralLinearSSA.lean`](GeneralLinearSSA.lean) is the machine-checked semantic
kernel for the `linear-ssa-m31-v1` source/relation certificate profile. It
covers any finite count of inputs, any fixed M31 array length, any finite
sequence of `add`, `sub`, and `mul` nodes, and any selected output. Source
sharing is represented by reusing a prior node ID. An unused instruction
still has to be valid and gets a row witness.

The checker starts with input IDs `0` through `inputs - 1`. Each instruction
must use the next ID and must read existing IDs. It rebuilds the selected
output as an independent `Term` and checks equality with the supplied source
term. Failed checks return `none`; they cannot be used as a premise for the
soundness theorem.

## Worked five-lane example

Source meaning, with two private arrays `a` and `b`:

```s31
let delta = a - b;
let doubled = delta + delta;
doubled
```

The corresponding positional certificate is:

| ID | Operation | Left ID | Right ID | Meaning |
| ---: | --- | ---: | ---: | --- |
| 0 | input | | | `a` |
| 1 | input | | | `b` |
| 2 | `sub` | 0 | 1 | `delta` |
| 3 | `add` | 2 | 2 | `doubled`, selected output |

`EmittedSSA` mirrors the emitted certificate's `ssa` object: `lane_count`,
indexed named inputs with visibility, indexed named nodes with string opcodes,
an assertion list, and an output ID. `checkEmittedSSA` accepts the example
with `lane_count = 5`. It rejects nonconsecutive input IDs, duplicate or empty
names, unknown visibilities or opcodes, assertions, zero lanes, invalid node
references, and an output that disagrees with the independent source term.
`emitted_ssa_air_sound` and `emitted_ssa_air_complete` are the direct theorems
over this certificate data shape.

[`GeneralLinearSSABytes.lean`](GeneralLinearSSABytes.lean) additionally uses
Lean's JSON parser to decode the *complete certificate byte string*, including
the schema, capability, profile, digest spelling, complete SSA object, and
empty `unmodeled_features`. It rejects unknown decoded fields. Its
`certificate_bytes_air_sound` theorem starts from the executable byte
checker result. The digest check covers lowercase hexadecimal syntax; it
does not recompute SHA-256 or bind the digest to source/relation file bytes.
Canonical JSON spelling and duplicate-key rejection remain package-checker
obligations because the decoded JSON object loses those raw-byte distinctions.
The JSON parser's runtime result for a concrete file is checked by executing
the checker, not by `decide` in the Lean kernel.
The byte decoder compares the entire input to the canonical, sorted,
two-space-indented JSON encoding used by the production package checker.
It rejects duplicate keys, extra fields, alternate whitespace, and alternate
key order. Runtime mutation controls exercise each case.

Each five-lane operation uses two packed rows: one for lanes 0–3 and one for
lane 4. The final row's other three input limbs may contain any M31 values;
the AIR equation still fixes the active fifth output lane. The theorem proves
that **every** accepted row witness has
`doubled[i] = (a[i] - b[i]) + (a[i] - b[i])` for all five lanes. It also
constructs honest row witnesses for every input. The graph theorem equates
these rows with the executable normalized `evaluateNode` calls, including the
node's M31 kind and array length.

The kernel checks example mutations: a wrong selected output, a forward
reference, and a changed subtraction opcode are rejected. These are theorem
fixtures, not substitutes for the production package tests.

## What this proves and what it does not

The principal theorems are `emitted_ssa_air_sound`,
`emitted_ssa_air_complete`, `air_iff_normalized_trace`,
`checked_normalized_sound`, and `checked_normalized_complete`.
They quantify over arbitrary *witness* values,
so the result is not merely a test of honest evaluation. `#print axioms` for
the principal theorems reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; the module contains no `sorry`, user
axiom, opaque trusted shortcut, or unsafe declaration.

This module models typed homogeneous M31 array arithmetic. The admitted
fragment excludes records and tuples, other integer widths, casts, constants,
Boolean operations, conditionals, control flow, assertions, static loops,
library calls, hashes, dedicated chips, private chip boundaries, and recursion.
It does not parse `.s31` bytes or prove
the production Python parser/specializer emits this certificate, prove the
production Zig backend emits these packed rows, or authenticate committed
trace cells with PCS/FRI. It checks declared names for uniqueness and
visibility spelling but does not prove name resolution against source text.
The emitted certificate's hashes and exact source/relation comparison are
separate package-checker obligations. A generated Lean literal admitted with
`by decide` proves the literal graph fits this kernel; if the same Python code
generated the source term, that alone is **not** an independent proof of
source-byte semantics.

For the older public four-lane add/mul source grammar, `GeneralLinearSSAJoin`
proves an exact intersection. If both byte checkers accept and their graphs
are equal after the explicit positional lift, they assign the same value to
every input. With the older modeled topology and `AuthenticatedRows` premises,
the row witness also has that value. Neither theorem derives native row
authentication from a PCS/FRI verifier.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSA
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSA
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes \
  S31.Gadgets.Functional.Correspondence.GeneralLinearSSAJoin \
  s31-general-linear-certificate-check
python3 tests/audit/general_linear_ssa_certificate.py
```

The full `S31` library imports this module, and the proof inventory records
its exact Lean bytes.
