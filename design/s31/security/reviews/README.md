# Scoped security reviews

These are dated snapshots of a reviewed implementation and its evidence.
They are grouped by the primary proof boundary:

- [Compiler and Gate rows](compiler/README.md): source, physical trace,
  fixed commitments, and AIR/lookup joins.
- [Mixed component proving](mixed/README.md): multi-component scheduling,
  manifests, private endpoints, and mixed verification.
- [Types and records](types/README.md): fixed-width arithmetic, range
  constraints, and public record ABI.
- [Release and soundness checkpoints](release/README.md): broad independent
  reviews and selected-schedule checkpoints.

Review conclusions do not inherit later code changes. Consult the live
[blocker matrix](../pcs-fri-v01-blockers.json) for current release status.
