# S31 security evidence

This directory records claims, implementation boundaries, and release blockers. A
passing fixture is evidence for its stated source and input; it does not turn
the native PCS/FRI verifier into a proven sound protocol.

Start with the [v0.1 blocker matrix](pcs-fri-v01-blockers.json), the
[remediation status](REMEDIATION_STATUS.md), and the
[profile soundness notes](PROFILE_SOUNDNESS.md). The
[PCS/FRI papers and implementation ledger](PCS_FRI_PUBLISHED_BOUND_AUDIT.md)
explains the missing theorem joins. Dated, scoped reviews live under
[reviews](reviews/README.md), grouped by the implementation boundary they
inspect. Keep new reviews there, with explicit source revision, checks run,
and limitations; keep live release policy and machine-readable gates here.

The `evidence/` directory contains pinned diagnostic artifacts. Its files
are inputs to specific audits, not independently trusted statements.
The [accepted sparse Gate H3 row example](PCS_FRI_SPARSE_GATE_H3_ACCEPTED_ROWS.md)
shows one authenticated circle row, its two OOD quotient calculations, and
the boundary between a checked row equation and a whole-oracle degree test.
The [three-height paper ensemble map](PCS_FRI_SPARSE_GATE_PAPER_ENSEMBLE.md)
itemizes conditional Protocol 3/4 function widths for the accepted two-point
claim roster and explains why the selected verifier's batch width remains unknown.
The [conditional two-Q degree join](PCS_FRI_SPARSE_GATE_TWO_Q_DEGREE_JOIN.md)
proves the coefficient-level shared-source implication and lists its native
and probabilistic premises.
The [recursive circle-basis proof](PCS_FRI_CIRCLE_RECURSIVE_BASIS_DEGREE.md)
derives the Laurent radius for every coefficient slot in the native-shaped
half-split evaluator.
The [multiproof byte-collision join](PCS_FRI_MULTIPROOF_BYTE_COLLISION_REDUCTION.md)
shows that a wrong row accepted by the modeled full decoder against a
constructed column tree gives two distinct messages with the same plain hash.
