# Independent review: V11 unseen geometry cost test

Reviewed the superseding prospective freeze at `d85fe72` and the one scored
result. Frozen model SHA-256: `4572e0948914594993bade611bedbce18b77a9761bd6e5f486add641cebd33c0`;
protocol: `125ab8cbf07d7906f344e19b8251b541c5ca1d54615e505666f71998470f5977`;
result: `7f11dde96bb20b4867ceec2f708e627c4aef70671da763914da2d5801e4f67fc`;
score: `c2781790db89c14ec21fd3e395922d6cb95c3bce86a653cfd8b0d1488d83d0b5`.
This reviewer performed static and raw-ledger arithmetic checks, without
building or running native proofs.

The separate native replay audit (SHA-256
`ac29e05d7b6871e7d76394e2f3c207bc85c8ffc946ee28a3b0ddb31bd72311c5`)
reports 88/88 honest verifier acceptances, 88/88 changed-result rejections,
and exact reconstruction of all 88 claim/proof files. Those native checks
were performed by the V11 collector/auditor, not by this reviewer.

## Freeze and admission

The model reads only V4 model/training and V5/V7/V8/V9 results through the frozen
V10 fit. V10 scored holdout and the paired direct/mixed result are absent from
its fit inputs. The four V11 call/log tuples `(1,9,11)`, `(1,11,4)`,
`(1,11,11)`, and `(2,9,11)` are absent from the fit geometry. All four source
hashes and all 168 assignment/statement hashes are unique and disjoint from
V4–V10 rosters. The correction from 512 to 1,024 live mul nodes for the two
circuit-log-11 sources changed source and claim hashes **before native V11
collection**; the numeric model, scoring gates, and sample count stayed fixed.

The collector checks the frozen model, source, compiler, host, and tool pins;
requires exact native manifest logs, slot/column/constraint counts, chip
rounds, source digest, registry digest, and interaction/FRI PoW bits before
timing; and aborts on any missing or rejected proof or RSS measurement. It
scores every claim index 1–20 for each source, after two descriptive claim-0
runs. There is no code path that silently removes a failed source or claim.
The independent auditor reconstructs claims, files, timing identities, and
scores and can replay all native verifier controls.

## Independent score calculation

The frozen proof centers and interval endpoints match the stated coefficient
formula. From the 88 result rows, the first-verified process wall equals
prover plus external verifier wall on every row. Recomputed medians, relative
errors, interval coverage, RSS medians, and wall-minus-reported-PoW residuals
match the committed score exactly. **Fourteen of sixteen prespecified gates
passed.** The gate-only log-11 source failed its two wall gates: observed
median 200.32 ms against 107.44 ms predicted (46.37% relative error), and
15/20 claims inside the nominal 90% wall interval (75% versus the required
80%). Its proof-size median error was 0.98% and its proof coverage was 19/20.

The gate-only and joint-log-11 median wall-minus-reported-PoW residuals are
similar (67.69 and 67.27 ms), while their FRI PoW medians are 129.77 and
73.89 ms. This is consistent with random PoW search contributing heavily to
the gate-only wall miss; medians of separate terms cannot establish a causal
decomposition. V11 also wraps timed processes in `/usr/bin/time` for RSS,
unlike V10's wall training method. That method shift can affect wall
prediction, although a common wrapper effect alone does not explain why the
gate-only case failed while the other three passed. Fixed source-block and
ascending-claim order leave temporal host drift as another possible influence.
The failed gates remain failures under the frozen protocol; these caveats do
not justify a scored rerun or refit.

The result establishes a bounded falsification of the wall extrapolation on
one host and four related programs. It does not establish cost-model
reliability, a general chip speedup, or equal proof-system soundness.
