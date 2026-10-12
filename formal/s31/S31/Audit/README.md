# Optional Lean source/relation/IR audit

`AliasRelationCheck.lean` exposes the proved bounded alias-fragment checker as
an executable. It reads **exact file bytes** from a `.s31` source and its
normalized `.s31.json` relation, plus optional compact canonical IR bytes.
It calls `SSAAliasTextBytes.checkAliasRelation` or
`AliasCanonicalIrBytes.checkAliasCanonical` directly, then prints one JSON line.
On acceptance, that line includes the certificate's arithmetic gates and
output wire; exit status is zero. Rejection has `"accepted": false` and exit
status one. Usage or file errors return status two.

From `formal/s31`:

```sh
lake build s31-alias-relation-check
.lake/build/bin/s31-alias-relation-check source.s31 normalized.s31.json
.lake/build/bin/s31-alias-relation-check source.s31 normalized.s31.json canonical-ir.json
python3 -m unittest discover -s tests -p 'test_alias_relation_check.py' -q
```

The supported source subset is one public four-lane M31 input and output,
one to sixteen distinct canonical add/multiply producers, and optional alias
lets or redundant parentheses. Aliases add no gates. The normalized JSON
must match the Lean encoder byte for byte, including formatting and names.
When provided, the compact canonical IR must also match its Lean encoder byte
for byte, including optional null fields and producer output name and ID.
The focused test compares the handwritten alias fixture with production
lowering, then checks generated 1–16-gate sources with exact normalized and
compact IR bytes. It also rejects the independent checker's 25 reserved
builtin circuit names and overlong relation names. These are differential
regressions, not a general parser equivalence proof.

This is **optional audit evidence** for the Lean theorems
`checked_alias_relation_sound` and `checked_alias_canonical_bytes_sound`.
The native release verifier does not execute
this adapter or independently replay its proof. Acceptance here alone does
not establish AIR/PCS soundness or production compiler correspondence.
