# Independent review: mixed manifest lifting geometry

Reviewed `457c879` against the native `direct_mixed_schedule.inspect` and
`PcsConfigV2.treeHeight` implementations. Focus: the local
`requireNativeGeometry` check for all four PCS trees.

The fixed-tree check is consistent with the native schedule: eight fixed
columns have the circuit trace log size, and their extended log size equals
the configured preprocessed lifting height. The three other tree-height
equalities and the recomputed maximum base-column log size also match the
source-derived native geometry on the admitted N=1 through N=8 fixtures.

I found one local admission gap. `treeHeight` requires **every extended
column log** (base log plus FRI blowup) to fit the configured tree height.
The reviewed check compared `trace_lifting_log_size` against the maximum
*base* log and checked the extended composition log separately. A coordinated
candidate with a smaller composition log and a trace lifting height equal to
the largest main or interaction base log passed those inequalities, even
though its extended main or interaction column cannot be committed at that
height. I added a checked `maximum base log + blowup <= trace lifting height`
condition. It also ensures the trace lifting height dominates the fixed-tree
height when the fixed column is the largest. The focused adversarial case
lowers composition log and trace lifting height together, keeps all three
trace-tree heights equal to the PCS value, and verifies rejection.

`zig build test-mixed-registry -Doptimize=ReleaseFast` passed with the fix.
The test accepts authentic source-derived geometries and rejects the existing
N=1 through N=8 mutations plus this coordinated under-lifting mutation.

This is a local consistency result. A caller can still invent a self-consistent
geometry or change a diagnostic digest. Proof admission must reconstruct the
selected source and AIR handles, compare complete geometry, and verify PCS
openings and FRI. This review does not prove those cryptographic checks or
general compiler correspondence.
