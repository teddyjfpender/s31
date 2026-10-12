# Independent V18 result audit — 2026-10-12

**Verdict:** the single frozen V18 prospective run at `23fa49d` passes its declared local gates. This does not repair V17's failed N8 cost prediction or establish a general whole-prover model. The V18 35% wall gate and 1.5× sample-median band were explicitly chosen after V17 and frozen before V18 timing.

The canonical [model](language/mixed-cost-v18-topology-transfer-model.json), [protocol](language/mixed-cost-v18-topology-transfer-protocol.json), [result](language/mixed-cost-v18-topology-transfer-result.json), [score](language/mixed-cost-v18-topology-transfer-score.json), and [artifact audit](language/mixed-cost-v18-topology-transfer-audit.json) have SHA-256 digests `97a1a02ebd1a69022fe9e810ec392078d7eb4450aa4573d51582f98953c05058`, `07dab408bad90494613a8d67d5b5240cb8bb746398a07b59df4ea87503ad4840`, `3a5d20ef644581bf02dd17cc0b4c3b580cbbd6783ef89f33b70329a96bca9a91`, `e7defea74f7403e772344431a4cfd46d89d41836aba7629a6a19f9d4f154eafc`, and `8691e05f25b1ccaabe8d8d0d7ab5d1865e58ad107db4058ea306aa88d92f05cf`. The fixed attempt marker contains one `started` and one `completed` record with the score digest and `all_gates_pass: true`.

I recomputed all 60 scored rows directly from canonical result/protocol JSON with Python's standard `json`, `statistics`, and `hashlib`; I did not import the study/model/audit scoring functions. For every source I recomputed medians, relative errors `abs(observed - predicted) / observed`, inclusive interval hits, four native-stage errors, and all 11 source gates. All **33 source gates plus 2 aggregate gates** match the frozen score. All 66 cold and scored rows have positive FRI and interaction PoW durations and strictly positive measured process-wall residuals after subtracting them.

| Frozen source | Observed / predicted verified wall median | Relative error | Wall band hits | Proof band hits | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| `calls6_log13_b8` | 214.944 / 222.022 ms | 3.293% | 19/20 | 20/20 | pass |
| `calls6_log14_b8` | 338.652 / 321.025 ms | 5.205% | 19/20 | 20/20 | pass |
| `calls7_log14_b32` | 314.256 / 322.562 ms | 2.643% | 19/20 | 20/20 | pass |

The pooled wall interval has 57/60 hits; all three sample medians lie in their frozen bands. The maximum wall-center error is 5.205%, well within the exploratory 35% gate. Proof intervals cover 20/20 per source.

I independently checked all three saved native manifests against source-derived ordered repeat calls, constants, feeder/source node IDs, every frozen slot field and constraint vector, tree columns, PCS 20/26 PoW bits, and four-lane address continuity. Recomputing the registry-manifest SHA-256 from its specified binary encoding matched each native manifest. Saved source, package binary, manifest, assignment, statement, and proof hashes match the result. Direct M31 evaluation of all 66 assignments matches every public output and exact typed statement; the changed statement modifies only its first result word by `+1 mod p`. All saved honest logs say `verified`, all changed logs say `error: InvalidMixedInteractionNonce`, and the 60 scored prover timestamps match the frozen interleaving. All 66 prover and verifier timing/RSS endpoints have positive durations and reported OS peak RSS.

The committed audit ledger records `native_replay: true` and 66 proof pairs. Its [audit code](../../../src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/audit.py) invokes the saved verifier twice per pair, once for the honest statement and once for the exact changed statement. I additionally invoked one saved honest/changed pair directly and observed `verified` / `InvalidMixedInteractionNonce`.

**Limits:** the raw proofs and binaries live in `/tmp/s31-v18-mixed-topology-e9be79a/.v18-artifacts` and need separate archival for later replay. The passed warm score excludes package builds and first-use costs (one package build per source took roughly 75–80 seconds). Three related sources on one Apple M5 Max host, wide PoW bands, and the looser post-V17 gate do not establish host-independent reliability, AIR/PCS soundness, or a Cairo speedup.
