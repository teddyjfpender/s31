# Independent review: paired direct Gate versus mixed chip study

Reviewed the protocol frozen at `06a837b` and the result committed at
`cb92808`. The committed protocol, result, summary, and replay-audit SHA-256
values are, respectively, `e1a703de522b13f322964607b892149962b0911f7cc2f8920f897dc0754f5c02`,
`e65ac68f054f0c0786a9b4a34b420c93e52526390dfcb4e2f8b5a7991438a34f`,
`1dd4ad7872eefc3353f33c62f8cb7740d323353d93bacd066f2b88aee821a356`,
and `1f2fedba9812688629bf62061251dcdde6243081196037833dfa56e6a83a3578`.
This review did not run proving or compilation.

## Checks performed

- Independently recomputed all 39 assignment outputs with the field recurrence
  `v ← v² + 13 + call_index (mod 2³¹−1)`, the between-call input additions,
  and the final input addition. Direct and mixed assignment and canonical
  public-record statement bytes agree for every warmup and scored claim;
  each statement contains the expected input and output words.
- Checked every frozen source and assignment hash, all 78 saved proof and
  statement hashes and proof lengths, and all saved source-pinned binary/key
  hashes against the raw `zig-out/s31-paired-mixed-vs-direct-v1` evidence.
  Each changed statement differs in exactly the first result word.
- Checked that all 72 scored rows follow the frozen shuffled schedule exactly,
  with 12 assignments and six trials in each arm-first order per source.
  The 78 rows contain every case, assignment, and profile identity once.
- Recomputed every summary median, paired ratio, direction count, and RSS
  median directly from the raw rows. Each first-verified wall equals prover
  process wall plus verifier process wall; each diagnostic residual subtracts
  the recorded interaction and FRI proof-of-work durations. The reported
  proof-size and RSS percentages agree with the underlying medians.
- Read the native command paths: `prove-for-external-verification` skips the
  direct Gate prover's internal verification; the mixed prover also emits
  before external verification. The collector invokes a fresh generated
  verifier for each arm and requires the altered claim to reach a proof-layer
  interaction-nonce rejection. The separate replay audit reports 78 honest
  acceptances and 78 changed-claim rejections; this review inspected its
  evidence and code but did not rerun native verification.

## Judgment and limits

No arithmetic, identity, order, or report calculation mismatch was found.
The study fairly compares the two *shipped first-verified workflows* for the
same source and claims, with package builds excluded. It does not isolate chip
arithmetic: source-specific witness construction, component geometry, proof
envelope, and process startup differ between lowerings. Both use 70 FRI
queries and 26-bit FRI proof of work, but matching visible parameters does
not establish equivalent soundness for the different AIRs. Random PoW search
is large relative to the short process runs; subtracting its measured duration
is useful diagnostic arithmetic, not a controlled no-PoW timing experiment.
The result supports a high-round proof-size and prover-RSS benefit for mixed
on this source family. It does **not** establish a whole-workflow speedup or
an automatic lowering rule.
