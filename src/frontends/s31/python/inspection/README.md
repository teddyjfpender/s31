# Package inspection

`reports.py` turns an already verified package into two audit reports:

- `explain` maps normalized nodes and source spans to builder gate counts and
  selected AIR geometry. Counts are not a claim that each node owns physical
  AIR rows.
- `equations` writes source-level field equations and operation notes for
  every normalized relation node. It identifies equations that omit internal
  hash or profile-specific AIR details.

The public `s31.explain` and `s31.equations` functions pass the package
verifier into this module. Every report verifies the package first. This code
is included in the CLI fingerprint and formal source identity inventory so
changes to audit output require a reviewed package rebuild.
