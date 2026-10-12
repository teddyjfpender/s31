# V19 new-claims/current-revision cost replication: local pass

**Frozen outcome: PASS.** This was one preregistered native attempt, following
pre-native commit `39122a2` and protocol SHA-256
`70adc15315812a206c0d41fdb6521dff8a84131ecb970693ba208845cc845977`.
It reused V18's exact `calls6_log13_b8` source and V18 prediction, but ran 20
fresh claims on S31 base revision `aa15b22ca817485599cda160b0e50ea5bc35f3cf`.
The host and `stwo-zig` gitlink match V18; five pinned S31 compiler/ABI files
changed: `build.zig`, bounded-call admission, record ABI, relation compiler,
and Python ABI binding. This is a **version and claim-sample replication**, not
an unseen-topology or cross-host test.

The current native manifest passed the frozen exact admission before proofs:
six ordered chip calls, 13 slots, 125 constraints, tree columns
`[8,114,176,8]`, and trace logs
`[13,12,4,10,4,8,4,6,4,11,4,9,4]`. All 22 honest proofs, including the
first post-build claim and its immediate repeat, were externally verified.
All 22 exact changed-result controls were rejected at
`InvalidMixedInteractionNonce`. The independent audit checked source,
assignment, statement, proof, binary, manifest, stage, and timing hashes and
replayed every honest and changed-result verifier call.

| Frozen warm metric | Predicted | Observed | Result |
|---|---:|---:|---|
| Verified process wall median, 20 claims | 222.02 ms | 230.29 ms | 3.59% observed-relative error; 16/20 one-draw band hits |
| Non-PoW process wall median | 147.27 ms | 145.68 ms | 1.09% error |
| Proof-size median | 227,381 B | 226,973 B | 0.18% error; 20/20 proof-band hits |
| Prover / verifier peak RSS median error | — | — | 3.98% / 0.054% |
| Largest of four native package-stage median errors | — | — | 3.28% |

The warm sample median was inside its frozen sample-of-20 band. All
prespecified warm gates passed, including the exact manifest, proof controls,
wall center and intervals, non-PoW wall, proof size, RSS, and package stages.
The V18 same-source warm median was 214.94 ms, so the V19 observed median is
7.14% higher than that previous observed sample; two samples on one host do
not isolate an effect of the compiler change from claim/PoW variation.
V17's N8 log13 failure remains a failure and is not rescored here.

## Whole-workload accounting

The protocol deliberately had **no build or cold-start prediction gate**.
V19's one package build took 81.85 s; the first post-build verified proof
took 1.212 s; its immediate same-claim repeat took 217.69 ms. Relative to the
20-claim warm median, those are 355.4×, 5.26×, and 0.945×. Summing measured
process durations for the build and all 22 proofs gives 88.12 s, or 4.005 s
per proof at that batch size; the build is 92.89% of that sum. This sum
excludes idle gaps between invocations and is not an elapsed end-to-end
workflow measurement. It makes the missing build/cold model visible: a warm
proof prediction alone substantially understates small-batch use.

The canonical result, score, and audit SHA-256 digests are
`8bd8d6f72345c2dc443bbd9b451fc17b3787ad0502c49a680231a9993a431a17`,
`0fd231823a27809b55a89a94755ec561f20e20a86bb465ce83acac8e271b1444`,
and `95c3d613abf4aba861e88f1add36153286580ad4f0f4aae523b54139f3cbc8b9`
respectively. The canonical protocol, one-attempt marker, result, score, and
audit live under `design/s31/measurements/language/`. Raw proofs, binaries,
manifests, native reports, and control files remain in
`/tmp/s31-v19-revision-holdout-aa15b22-artifacts`; long-term native replay
requires archiving that directory separately.

This local pass supports the frozen V18 warm prediction for one existing
source, one compiler revision, one host, and a fresh 20-claim sample. It does
not establish whole-prover cost reliability across circuit topologies, hosts,
build states, or future compiler revisions, and it does not measure a Cairo
speedup.
