# Independent review: V12 unseen log-12 cost transfer

Reviewed the prospective freeze at `0ae51bde` and the scored result/native
replay at `f9daa2f`. SHA-256: model
`66b4c1720386705bd8d983cf09cc31136fa9fa58a48300f5e2e02f89bed1ff97`,
protocol `93c14e4a6d72a75dcf289d2d09f396f064b1b6ec5cf35133f1b5c7f3ab7d839f`,
result `1e46156fcdc5e04039e5ffb5880c7d8e2ad3de0061854fd539289d1a3b1efb80`,
score `7da0dfb4c47ed21f8e4347ed8fca019ebcc4f0c1cc228620c88fe7ce8c069bc2`,
and native audit `9ca68ef6847c18a6a9fd837ff0f950b117673f73e1d2ad17e91e21f5a9f19da4`.
This reviewer performed read-only source and raw-ledger checks; the separate
V12 auditor performed native verifier replay.

## Freeze and scoring integrity

- The five declared V10/V11 fit-input hashes match their committed files.
  V11's failed 14/16 score is explicitly classified as V12 training. No V12
  measurement was available to the fit. The four V12 source hashes and 168
  assignment/statement hashes are unique and disjoint from V4–V11 rosters.
  All four expected component geometries reach log 12, absent from the fit.
- The frozen proof, RSS, and wall prediction centers and bands match the
  model coefficients and stored simulation quantiles. The simulation fixes
  seed `202610122121`, 100,000 one-draw samples, and 10,000 samples of 20.
  The scored schedule exactly matches seed `202610122241`: 20 shuffled claim
  rounds with all four sources shuffled once per round.
- The runner admits all four source-pinned packages and exact native
  manifests before proving; any missing build, proof, statement, changed
  result rejection, RSS measurement, or geometry aborts the run. It records
  two descriptive claim-0 trials, then one scored claim at each index 1–20
  per source. There is no silent source/claim exclusion or score adjustment.

## Raw result check

From all 88 saved trials, independently checked source, assignment,
statement, changed-result, proof, binary, and manifest hashes and bytes; exact
source geometry; and every prover-plus-verifier process-wall identity. The
physical prover start order matches all 80 frozen scored schedule positions.
Recomputed every source median, relative error, coverage count, RSS metric,
and aggregate gate from the ledger. All **24 per-source checks and both
aggregate checks pass**. Wall median errors are 0.98–2.02%; the pooled
one-draw wall interval contains 78/80 scored claims, and all four observed
20-claim medians lie in their frozen median bands. The committed native audit
reports exact reconstruction and native honest/changed-claim replay for
88/88 proofs.

V11 and V12 used the same Darwin `/usr/bin/time -l` process-wall/RSS method,
the same host, engine gitlink, Zig executable, ReleaseFast build, and mixed
lowering. Their broad compiler fingerprints differ: between the V11 freeze
and V12 source-base commit, the only production-code diff adds three
diagnostic geometry fields to the generated manifest executable. Prover and
verifier runtime files did not change in that interval.

This is a successful **bounded prospective transfer** to these four log-12
programs on one host. It does not establish reliable prediction across
programs, hosts, or compiler revisions. The PoW forecast assumes exponential
nonce-search times with source-level rate uncertainty fitted from only four
V11 blocks; the proof-size and RSS log-step rules are also fragile. Native
honest/changed-claim replay does not itself prove compiler or AIR soundness.
