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
