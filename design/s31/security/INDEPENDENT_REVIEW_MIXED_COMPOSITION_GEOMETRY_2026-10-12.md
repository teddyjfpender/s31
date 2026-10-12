# Independent review: mixed composition tree geometry

Date: 2026-10-12. Reviewed commit: `b2c7417f1869706fcc1aee71a2780646fb494060`.
Scope: `runtime/mixed_boundary/registry_manifest.zig` and its N1–N8 focused test.

## Result

No blocking discrepancy found. The new local check agrees with the native
composition commitment shape for the admitted one-through-eight-call sources.
The QM31 secure extension has four base coordinates. The core verifier's
`compositionColumnCount(split, 4)` returns `4 × 2^split`; the mixed live
inspector obtains `split` from the actual ordered AIR handles and uses that
same function to set `tree_columns[3]`. All current mixed handles use split
one, hence eight composition columns. The new equality rejects an arbitrary
fourth-tree width, and the `max_tree_width` bound prevents an oversized label.

The PCS config defines `trace_lifting_log_size` as the already blown-up
commitment height for trees one through three. The live inspector computes
`composition_log_size = compositionLogDegreeBound() - split`, forms each
composition column's extended log by adding the FRI blowup, and calls
`pcs.treeHeight(3, ...)`. That API returns the configured trace height only
if it dominates every extended column log. The new equality to the PCS trace
height and checked `composition_log_size + blowup <= height` reproduce these
two necessary conditions. The core verifier also uses the configured lifted
height when committing the composition tree under this protocol revision.

## Negative controls and scope

`zig build test-mixed-registry -Doptimize=ReleaseFast` passed in an isolated
worktree at the reviewed commit. The test constructs genuine source-derived
geometries for every N from one through eight. Each accepted geometry passes
`requireNativeGeometry`. For each N, changing only `tree_columns[3]` to zero
fails the width equality; increasing only `tree_lifting_log_sizes[3]` fails
the PCS-height equality; and setting `composition_log_size` above the PCS
trace height fails the extended-log bound. Each directly returns
`InvalidMixedLiveManifestBinding`, before a selected-schedule digest check.
These are structural mutation controls, not forged-proof tests.

This change strengthens the **local manifest-to-live-geometry check**. It does
not make a caller-supplied manifest or geometry a verifier key. In particular,
the local check alone does not establish that `composition_split` or the
composition degree bound came from the actual AIR handles; a coordinated
alternate split, width and in-range degree can satisfy its three new checks.
The source-embedded package reconstructs the schedule before proof decoding,
and the engine independently rebuilds exact geometry from the source plan and
AIR handles, comparing the complete geometry before accepting a proof. Native
PCS verification then checks the actual commitment and openings. Thus this
patch closes a local structural admission gap without changing the underlying
cryptographic proof-admission argument or proving PCS/FRI soundness.
