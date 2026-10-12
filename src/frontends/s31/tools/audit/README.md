# Pinned public trace audit

`public_trace.py` checks one proof for a program admitted by the strict
public four-lane `direct-gate` release checker. It accepts both the v2 source
certificate and the opt-in v3 common-subexpression certificate. The caller
must supply five SHA-256 pins obtained outside the package.

```sh
python3 src/frontends/s31/tools/audit/public_trace.py \
  PACKAGE PROOF.bin --statement STATEMENT.json \
  --source-sha256 SOURCE_JSON_DIGEST \
  --key-sha256 KEY_DIGEST \
  --prover-sha256 PROVER_DIGEST \
  --verifier-sha256 VERIFIER_DIGEST \
  --text-sha256 SOURCE_TEXT_DIGEST
```

The tool copies the proof, statement, and package before checking them. It
reparses the exact `.s31` source through the independent release checker,
checks the sealed fixed Gate schedule and key, and runs the generated native
verifier on the captured proof and statement. It then evaluates the admitted
arithmetic graph from the four public input words, derives every fixed and
main Gate cell, and compares all 6,144 expected main words with the native
public trace export. Its digest must match the native main-root report, whose
root must equal commitment 1 in the accepted proof. A changed main cell is
rejected by the source-derived comparison. Both native inspection commands
must reject a synthetic assignment with a nonempty private input map.

The JSON report identifies the admitted source, canonical IR, fixed root,
main root, full main-column digest, proof digest, and public words. This is a
diagnostic for an accepted proof under the supplied pins and native PCS
implementation. It does not prove collision resistance, arbitrary opening
authentication, FRI, LogUp, or the correctness of every S31 language form.
Programs outside the bounded release fragment fail admission.

The CI acceptance cases run this audit on a pure named helper, its optimized
v3 spelling, and the basic square helper. They compare each functional form
with handwritten direct source and require equal AIR geometry.
