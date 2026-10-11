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

`source_pinned_general.py` builds and proves the experimental mixed roster for
each count from one through eight. Its independent source/manifest projection
checks that each inspected call has the source repeat's ID, input node,
round count and constant; that consecutive calls use the preceding call's
four output addresses; and that circuit, chip and bridge slots carry the
declared Gate/chip relation IDs. It rejects eleven manifest mutations and a
changed source constant per checked count. Run the projection alone during a
short edit loop:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static
```

The projection is an independent check of the public inspection report for
this chain family. Native source reinspection, fixed-column commitments and
proof verification still carry the authority for a package. The Python
check does not authenticate trace values or prove the source-to-Lean event
correspondence.
