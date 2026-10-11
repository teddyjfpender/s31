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
order. Four static mutations exercise these checks. A separate Python audit
decodes the pinned Gate bytecode's ordered per-column offsets, applies the
closed pair/many chip and bridge masks, derives the deterministic circle
point and canonical step over M31, and hashes the exact little-endian point
limbs in native tree/column order. It rejects a well-formed but incorrect
`mask_points_sha256`. The source-pinned verifier still reconstructs the native
handles and PCS schedule before decoding and verifying a proof.

The focused N1 black-box native run matched the independently recomputed
digest and accepted a 70,105-byte proof. A subsequent N3 run exercised the
`many` chip and bridge masks as well as the `pair` masks, matched the live
manifest, accepted a 101,122-byte proof (SHA-256
`fcad0c86e6e48341e9742a43ba3bf283d6ef712b7143becb2e41c741edf2a799`),
and passed the existing changed-source, changed-claim, and malformed-proof
rejection controls. Static source/slot projection and mutation cases cover
N1, N3, and N8. These observations are local acceptance evidence rather
than a proof for every possible source or challenge.

This closes a manifest visibility and digest-recomputation gap for the bounded
mixed roster. The audit trusts the installed AIR bundle, the checked Gate
bytecode decoder, and the stated circle generator and pair/many mask policies.
It does not derive those policies from the native implementation or prove the
Zig field arithmetic correct. The JSON report remains a diagnostic artifact,
not a verifier key or a proof of source-to-native compiler correspondence,
AIR soundness, or PCS/FRI soundness.
