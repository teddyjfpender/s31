# General mixed manifest: live geometry audit fields

The `direct-mixed-general` manifest command now prints three facts from the
source-rebuilt native geometry: `tree_lifting_log_sizes`,
`mask_points_sha256`, and `local_air_dependency_sha256`. The selected-schedule
digest already covers these facts. Publishing them lets an auditor see which
PCS tree heights, mask-point schedule, and local chip/bridge AIR dependency
closure the verifier reconstructed. It does not change the proof envelope,
the registry-manifest digest, or the native transcript.

The independent acceptance checker verifies that each tree height agrees
with its PCS configuration, that fixed/main/interaction column counts agree
with the component roster, and that the local AIR dependency digest equals a
fresh SHA-256 over the seven exact engine source files in their registered
order. Four static mutations exercise these checks. It also requires a
well-formed, nonzero mask-point digest. The complete mask-point bytes are not
in the JSON report, so this checker cannot independently recompute that
digest from the report alone. The source-pinned verifier still reconstructs
the native handles and PCS schedule before decoding and verifying a proof.

This closes a manifest visibility and local dependency audit gap. The JSON
report remains a diagnostic artifact, not a verifier key or a proof of
source-to-native compiler correspondence, AIR soundness, or PCS/FRI soundness.
