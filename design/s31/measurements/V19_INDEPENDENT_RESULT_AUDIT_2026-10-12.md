# Independent V19 cost-result audit (2026-10-12)

**Finding: the recorded local PASS is reproducible from the frozen protocol and raw artifacts.** I recomputed the score with a separate Python standard-library script, without importing the V18 or V19 scoring code or running a new timing study. I found no discrepancy in the reported warm metrics, admission geometry, proof controls, or build/cold accounting.

## Freeze and artifact identity

- Commit `39122a2` contains the exact canonical protocol bytes (SHA-256 `70adc15315812a206c0d41fdb6521dff8a84131ecb970693ba208845cc845977`), and its commit timestamp is 00:29:25 UTC. The one-attempt marker records its start at 00:34:14.947575 UTC, before the saved build and proof artifacts; it has exactly one start and one completed record. This checks the available evidence of pre-native freezing, although repository timestamps and a marker cannot themselves prove that no unrecorded trials occurred.
- All 31 protocol-pinned files match `aa15b22` byte-for-byte by Git blob SHA-256. Relative to the V18 result commit `23e60d2`, exactly five of those pinned files differ: `build.zig`, bounded-call admission, record ABI, relation compiler, and Python ABI binding. The source hash and `stwo-zig` gitlink agree with V18. The 21 frozen assignment and statement hashes are individually distinct and have no collision with V18's corresponding claim hashes.
- Canonical result, score, and audit digests match the report: `8bd8d6f72345c2dc443bbd9b451fc17b3787ad0502c49a680231a9993a431a17`, `0fd231823a27809b55a89a94755ec561f20e20a86bb465ce83acac8e271b1444`, and `95c3d613abf4aba861e88f1add36153286580ad4f0f4aae523b54139f3cbc8b9`. The saved result is byte-identical to the raw result. Source, manifest, and prover/verifier/manifest binary hashes match their recorded identities.

## Native admission and controls

The saved manifest has the six frozen ordered calls, 13 frozen slot layouts, 125 constraints, tree columns `[8, 114, 176, 8]`, and frozen slot trace logs. I compared every frozen call and slot field with the manifest and reproduced the manifest executable's output hash (`074b41f26dbb3b92a49bd7b2eec79e2e971a7fa9ad0bee0375754450bd4a3ad1`).

For all 22 rows, I checked claim order; frozen assignment and statement hashes; proof size and hash; emitted statement equality; a one-word changed-result mutation; tagged stage/phase reports; monotonic duration arithmetic; and saved `verified` / `InvalidMixedInteractionNonce` verifier outputs. I also independently replayed one honest proof and its changed-result control (`a07r0`) with the saved native verifier: exit 0 / `verified`, then exit 1 / `InvalidMixedInteractionNonce`. The existing V19 audit artifact reports native replay of all 22 pairs; my fresh native replay was a spot check, not a second full replay.

## Independent score and lifecycle arithmetic

| Measure, scored on 20 fresh claims | Recomputed observation | Frozen prediction | Recomputed error / coverage |
|---|---:|---:|---:|
| Verified prover + verifier process wall median | 230.289208 ms | 222.021711 ms | 3.5900%; 16/20 one-draw hits; median within sample-of-20 band |
| Process wall after reported PoW subtraction | 145.677791 ms | 147.271854 ms | 1.0942% |
| Proof-size median | 226,973 B | 227,381.25 B | 0.1799%; 20/20 interval hits |
| Prover / verifier peak RSS median error | — | — | 3.9816% / 0.0540% |
| Four package-stage median errors | — | — | 1.0936%, 1.4557%, 2.0463%, 3.2808% |

Every frozen warm threshold passes when applied directly to these recomputed values. The one package build is 81.852226 s; the first post-build verified proof is 1.212335 s and its immediate same-claim repeat is 217.694 ms. Build plus all 22 recorded proof-process durations sums to 88.116412 s, or 4.005291 s per proof; build accounts for 92.891% of that sum. These are process durations, so the sum omits idle gaps and is not an end-to-end stopwatch measurement.

**Scope:** This validates one source, a changed compiler revision, fresh claims, and one host. Build/cold figures are descriptive because the protocol preregistered no build or cold prediction gate. The result does not establish a reliable whole-prover cost model across topologies, revisions, or hosts, and it does not measure a Cairo speedup. Raw artifacts remain under `/tmp/s31-v19-revision-holdout-aa15b22-artifacts`; preserving native replay requires archiving that directory.
