# Public ABI for checked M31 SSA certificates

[`GeneralLinearSSAPublicABI.lean`](GeneralLinearSSAPublicABI.lean) checks the
public statement for both `linear-ssa-m31-v1` and
`linear-ssa-m31-effects-v1`. It derives field names, visibility, array width,
and output name from the decoded certificate. It also parses and validates the
exact canonical normalized relation JSON, requiring the relation's ordered
input names, visibilities, M31 shapes, and selected output name to agree with
the certificate. The supplied `public-abi.json`
must be canonical, byte exact, and equal to that derived layout. A separate
canonical assignment JSON must contain every named public and private input,
each with exactly the declared number of canonical M31 values, and one named
public output. The raw statement file must contain exactly eight little-endian u32
words, 32 bytes total. Each word is a canonical M31 value. Public inputs
appear in **source declaration order**, then the output; unused words are
zero. Private inputs contribute no public words.

## Handwritten example

```s31
circuit ordered(public x: [m31; 2], public y: [m31; 2],
                private salt: [m31; 2]) -> public [m31; 2] {
    let sum = x + y;
    sum
}
```

For `x=[1,2]`, `y=[3,4]`, `salt=[99,100]`, the exact assignment is:

```json
{
  "private_inputs": {"salt": [99, 100]},
  "public_inputs": {"x": [1, 2], "y": [3, 4]},
  "public_outputs": {"sum": [4, 6]}
}
```

The public statement words are `[1, 2, 3, 4, 4, 6, 0, 0]`. For example,
word `4` is the four bytes `04 00 00 00`. Although JSON object keys are
sorted canonically, the **ABI's input list** and raw word file preserve `x`
then `y`. Swapping those two entries or their raw word blocks fails the Lean
gate. The certificate's `salt` visibility is private; the assignment must
still supply it, while the public word file omits it.

The [pure fixture], [effects fixture], and [ordered fixture] exercise private
only, mixed, and two-public-input layouts. The effects certificate additionally
contains an assertion involving its private input. Each comes with canonical
ABI and assignment JSON and an exact 32-byte public-word file.

`pure_relation_public_abi_sound` and `effects_relation_public_abi_sound`
compose the relation-layout check with the ABI byte gate and arbitrary
modeled packed AIR rows. They prove that accepted public word bytes encode
the ordered public inputs and the independently checked source term's output.
The effects theorem retains every assertion polynomial. The proofs also
derive the exact ABI descriptor, lane-count equality, and accepted named
assignment bytes. `private_input_erasure` proves the public-input word prefix
is unchanged when only private input values change.

`pure_air_public_abi_sound` and `effects_air_public_abi_sound` are the inner
theorems without normalized relation bytes. They start from the
executable certificate/ABI/assignment/word gate and arbitrary modeled packed
AIR row witnesses. All theorems use no `sorry` or custom axioms.

These theorems are conditional on a separately supplied typed source term.
The normalized relation check binds its public layout, but it does not compare
every relation arithmetic node or assertion with the certificate. They do not
independently derive the typed term or circuit name from `.s31` source bytes,
recompute the certificate's source/relation hashes, prove that native
Zig gates own these public pins, or prove that native PCS/FRI verification
authenticates the modeled AIR rows. The production source-fragment checker
does derive the certificate and ABI from source, but its Python implementation
is not proved equivalent to this Lean decoder. The exact ABI JSON and public
word bytes here are checked as provided; a native verifier must separately
bind them to its statement and proof.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAPublicABI \
  s31-general-linear-public-abi-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAPublicABI
python3 tests/audit/general_linear_public_abi.py
```

[pure fixture]: ../../../../fixtures/correspondence/public_abi/pure.abi.json
[effects fixture]: ../../../../fixtures/correspondence/public_abi/effects.abi.json
[ordered fixture]: ../../../../fixtures/correspondence/public_abi/ordered.abi.json
