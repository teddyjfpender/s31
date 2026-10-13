# Record v2 source, evaluator, and fixed-row admission

`GeneralRecordV2ProgramAdmission.lean` closes a specific source-to-typed-program
gap for the exact-byte bounded record grammar. The earlier record checker
reconstructs the complete version 2 relation, ordered record boundary, and
typed structural tree from the original `.s31` bytes. This module then erases
the already checked `public_abi` metadata, decodes the remaining version 1
core with `S31.Json.program`, and requires equality with a `Program` built
independently from the parsed source. `Static` carries a Lean proof that those
four exact byte inputs passed the source checker. Its `aligned` proof gives
`Program.evaluate` equality for every assignment, including private inputs
and aliased result fields. No compiler-produced graph is an axiom here.

For example:

```s31
struct Box { value: [m31; 1] }
circuit double(public x: Box) -> public Box {
    let y = x.value + x.value;
    Box { value: y }
}
```

The source-derived normalized input is `_s31_abi_input_0`, the node is
`y = add(_s31_abi_input_0, _s31_abi_input_0)`, and the unique public output is
`y`. For `x.value = 7`, the canonical record statement claims `result.value =
14`; the Lean executable constructs its assignment from those two public
leaves and runs the actual typed `Program.evaluate`, yielding
`[7, 14, 0, 0, 0, 0, 0, 0]`. Changing the result to 15 is rejected before
native verification. The statement check is deliberately limited to one
public input field, one arithmetic node, and one distinct result wire. The
static source-to-program theorem covers the wider bounded record grammar.

The opt-in [`record_v2_lean_release.py`](../../../../../../scripts/release/record_v2_lean_release.py)
path narrows further to the exact shape above: one public `[m31; 1]` field and
one `x.value + x.value` result. It takes external SHA-256 pins for the Lean
checker, source relation, source text, key, prover, and verifier; snapshots
those bytes; runs Lean on the same public statement passed to the verifier;
and independently reconstructs the Gate schedule from source. The
release checker constructs every fixed row and all eight fixed columns from
the source-derived Gate schedule, compares their hashes to the component
manifest, and asks the pinned prover to recommit those supplied columns. The
recomputed root must equal the pinned verification key root. The worked `double` package has 512
fixed rows: 505 add, 1 subtract, 4 multiply, and 2 pointwise multiply. Its
first source add row uses addresses `(11, 11, 14)`; the remaining rows handle
public packing, field constants, extraction, and padding. The source add row
is one small part of the complete fixed schedule, not the entire circuit.

This check gives a concrete record v2 source-to-native-fixed-rows admission,
subject to the native fixed-column recommitment, key, verifier, and PCS
correctly binding the preprocessed root. It does **not** prove the native AIR interpreter
or PCS/FRI in Lean. The version 2 key uses the existing direct-record key and
component manifest v1; this gate requires external key and binary pins.
Private record fields, multiple fields, aliases in the public statement,
other operations, and general record programs remain outside this release
gate. In particular, the checked static source-to-program equality alone
does not authenticate a native AIR trace for those wider cases.

Run the focused corpus with a regular, pinned checker binary:

```sh
python3 formal/s31/scripts/check_record_v2_program_admission.py \
  /path/to/s31-general-record-v2-program-admission-check \
  /path/to/package /path/to/proof.bin /path/to/statement.json
```

The corpus checks three exact-source accepted record packages and five
source/tree/relation/ABI mutations. With a real package it also accepts a
native proof and rejects a changed public result, source-derived Gate row, and fixed
root. The checker executable is declared in `formal/s31/lakefile.toml`.
