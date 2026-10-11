# Mixed boundary command acceptance

`source_pinned.py` builds the experimental fixed N=3 mixed binaries from a
source file. It checks an honest proof, the generated component manifest,
changed public claims and proof fields, a separately built verifier with
changed embedded source, and build rejection of a valid two-call program.

Run from any directory:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
```

This is a black-box command test. The AIR equations and STARK core have their
own focused tests and review; passing this script does not establish a general
mixed boundary or witness confidentiality.

`arithmetic_chip_input.py` exercises every admitted four-lane arithmetic
feeder (`add`, `mul`, `add_const`, `mul_const`) with independently computed M31
claims, native proofs and mutation controls. Its source-pin check uses a
whitespace-only change, checks that the compiled IR, endpoint calls and fixed
root are identical, then reseals both statement and proof-envelope identities.
The old one-to-eight-call proof-byte compatibility procedure is in
[PROOF_BYTE_COMPATIBILITY.md](PROOF_BYTE_COMPATIBILITY.md); its baseline has
not yet been recorded.
