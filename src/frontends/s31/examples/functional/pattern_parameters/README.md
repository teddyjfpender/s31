# Product parameters

[`weighted.s31`](weighted.s31) accepts a pair in a named helper and binds its
components in the parameter list. The pair is a source-only value. The
compiler checks its type, then specializes the helper and emits the same
two-node relation as [`weighted_manual.s31`](weighted_manual.s31):

```text
product = x * y
result  = product + x
```

For the checked-in assignment, `x=7`, `y=9`, and the public result is `70`
in M31. Each field position is a lane; this example has one lane. The native
acceptance gate compares the complete AIR geometry of both sources, proves
the claim, and rejects a changed public result. The pattern adds no witness
cell, AIR row, or verifier constraint. Both sources use 277 raw QM31 operation
rows and 512 padded rows under both `gate` and `direct-gate`; the profiles
have different preprocessing and proof sizes because their AIR layouts differ.
