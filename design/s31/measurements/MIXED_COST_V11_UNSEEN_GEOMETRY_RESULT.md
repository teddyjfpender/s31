# V11 unseen-geometry transfer: frozen extrapolation fails 2 of 16 gates

The single prospective V11 run **failed 2 of its 16 prespecified gates**.
All four fresh sources reached their exact native component geometry, all 88
honest proofs verified, and all 88 ABI-valid changed public results were
rejected at the proof layer. The independent audit reconstructed every exact
source, claim, changed-result file, proof, phase report, and score, then
replayed all 88 honest and 88 negative native verifier calls. No source was
selected, prediction adjusted, or scored claim rerun after observing results.

V11 tests extrapolation to **previously unseen** circuit/chip trace log 11
and to a two-call log-11 profile. V9 previously failed 6/12 gates when the
older V8 model first met log-10 geometry. V10 then passed 12/12 gates on
fresh sources at log pairs already used for V10 fitting. The V10 holdout and
paired direct/mixed study were excluded from V11 fitting. The first V11
pre-native freeze (`63ec190`) was corrected before any V11 native build or
proof because 512 packed mul nodes did not guarantee circuit log 11. The
eligible superseding freeze (`d85fe72`) uses 1,024 live packed mul nodes; its
exact manifest prediction was confirmed by the native packages.

| Source | Native slot trace logs | Wall p50 observed / frozen | Wall error, gate ≤30% | Wall 90% coverage, gate ≥80% | Proof p50 observed / frozen | Proof error, gate ≤10% | Proof coverage, gate ≥80% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `chip_surge_n1` | 9, 11, 4 | 84.93 / 88.45 ms | 4.14% ✓ | 19/20 ✓ | 101,525.5 / 100,732.25 B | 0.78% ✓ | 20/20 ✓ |
| `gate_surge_n1` | 11, 4, 4 | 200.32 / 107.44 ms | **46.37% ✗** | **15/20 ✗** | 105,891 / 104,852.25 B | 0.98% ✓ | 19/20 ✓ |
| `joint_surge_n1` | 11, 11, 4 | 141.30 / 107.59 ms | 23.86% ✓ | 18/20 ✓ | 107,618.5 / 104,852.25 B | 2.57% ✓ | 20/20 ✓ |
| `serial_surge_n2` | 9, 11, 4, 4, 4 | 96.33 / 89.04 ms | 7.56% ✓ | 18/20 ✓ | 118,166.5 / 115,278.5 B | 2.44% ✓ | 19/20 ✓ |

Each source has 20 scored claims plus a first post-build claim and its
immediate repeat. Package builds took 73.78–74.35 seconds each and were
reported separately, with no inclusion in the scored process wall. The
compact [result](language/mixed-cost-v11-unseen-result.json) SHA-256 is
`7f11dde96bb20b4867ceec2f708e627c4aef70671da763914da2d5801e4f67fc`;
the [score](language/mixed-cost-v11-unseen-score.json) SHA-256 is
`c2781790db89c14ec21fd3e395922d6cb95c3bce86a653cfd8b0d1488d83d0b5`;
the native [audit](language/mixed-cost-v11-unseen-audit.json) SHA-256 is
`ac29e05d7b6871e7d76394e2f3c207bc85c8ffc946ee28a3b0ddb31bd72311c5`.
The frozen [model](language/mixed-cost-v11-unseen-model.json) SHA-256 is
`4572e0948914594993bade611bedbce18b77a9761bd6e5f486add641cebd33c0`,
and the [protocol](language/mixed-cost-v11-unseen-protocol.json) SHA-256 is
`125ab8cbf07d7906f344e19b8251b541c5ca1d54615e505666f71998470f5977`.
The 46 MB raw package/proof corpus is local at
`/tmp/s31-v11-unseen-d85fe72`; native replay needs that corpus.
The runner checked the frozen compiler/runtime/tool pins before and after
timing. Subsequent work in the shared workspace changed a pinned manifest
source file, so current-worktree `protocol.py check` is no longer a valid
reproduction check for this scored package. The saved source-pinned binaries,
exact source/claim/proof hashes, frozen commit, and completed native audit
remain the evidence for this run.

The failed gate-only source had median reported FRI PoW of 129.77 ms, versus
73.89 ms for the joint log-11 source. Their median verified wall after
subtracting native reported FRI and interaction PoW was nearly equal:
67.69 versus 67.27 ms. Their external verifier medians were 33.45 versus
32.75 ms. This decomposition is consistent with stochastic PoW nonce-search
variation as the major source of the gate-only wall miss, but two source
blocks with 20 claims each do not identify a causal effect or rescue the
frozen score. The gate-only wall failure remains a failure.

**Wall measurement method changed:** V11 wraps each fresh prover and verifier
process with `/usr/bin/time` to collect peak RSS, while the V10 wall fit used
bare subprocess timing. The wrapper contributes launch and reporting work to
V11 process wall. It is common to all four V11 cases and does not alone
explain why the gate-only case missed while the joint log-11 case passed.
Peak RSS medians were 9.66–13.15 MB for provers and 6.68–10.44 MB for
external verifiers; these were descriptive and had no frozen predictive
gate. A separately labeled post-hoc matched-invocation check can quantify
wrapper overhead without altering this prospective score. That
[post-hoc check](MIXED_COST_V11_POSTHOC_METHOD_CHECK.md) measured roughly
12–13 ms of combined process-method shift on the saved gate-only and joint
binaries, far below the gate-only 92.88 ms observed-versus-predicted wall
gap. Its new proof samples did not enter V11 scoring or fitting.

The result is one host, one engine/compiler pin, and four related sources.
It shows a useful proof-size extrapolation on this small set and a wall-time
failure. It does not establish a generally reliable whole-prover predictor,
an AIR cost law, or any speedup against Cairo.
