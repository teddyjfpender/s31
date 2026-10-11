# Independent V17 mixed-call audit — 2026-10-12

**Verdict:** the frozen V17 result is a valid failed prospective local cost test. Its sole failed gate is the `calls8_log13` verified-wall median error: `0.3052161627` exceeds the frozen `0.30` limit. This result does not establish a general whole-prover cost model or a cryptographic soundness claim.

## Frozen evidence and independent method

The canonical [protocol](language/mixed-cost-v17-mixed-calls-protocol.json), [result](language/mixed-cost-v17-mixed-calls-result.json), and [score](language/mixed-cost-v17-mixed-calls-score.json) have SHA-256 digests `c4402bff32a5b24db6e6e32fa26ea5137aff1170bcd1ba9e99dbed747d479329`, `c84ebaeba603a9ca7f9cf6572c3eac09cfc81b7ae092ecf1b371a6c7af5f4a59`, and `aba4eb8a6516c9da7a7b674500a90a087cf0bc1f4d07daa07988fa91f1e01bdd`. The fixed attempt marker contains one `started` and one `completed` event; the latter records `all_gates_pass: false` and the score digest. The prospective study is recorded at `a720b0f` and summarized in the roadmap at `f829c1b`.

I separately read the canonical JSON and saved artifacts using Python's standard `json`, `hashlib`, and `statistics` modules. I did not call the study or its artifact auditor's scoring functions. For each of the 60 scored rows, I recomputed the observed medians, relative errors `abs(observed - predicted) / observed`, inclusive interval hits, the four native-stage errors, and each frozen gate. All **33 source gates plus 2 aggregate gates** match the score. All 66 cold and scored rows have positive FRI and interaction PoW durations and a strictly positive process-wall residual after subtracting both. The scored minimum residuals are 135,969,334 / 229,265,458 / 142,757,125 ns in the source order below.

| Source | Observed wall median (ns) | Predicted median (ns) | Relative error | Wall band hits | Proof band hits | Gate result |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `calls4_log13` | 218,298,521 | 218,883,691.748 | 0.002681 | 19/20 | 20/20 | pass |
| `calls4_log14` | 288,440,625 | 316,621,588.248 | 0.097701 | 20/20 | 20/20 | pass |
| `calls8_log13` | 171,934,624.5 | 224,411,850.832 | **0.305216** | 17/20 | 20/20 | **fail: wall median error** |

The pooled wall band has 56/60 hits, and two of three observed sample medians fall in their frozen sample-median bands. Both aggregate gates pass. All other source gates pass.

## Source, manifest, and claim checks

For each of the three native packages, the saved source bytes match the frozen source file and SHA-256. Independently walking the source's ordered nodes reproduces the frozen repeat-call IDs, feeder/source node IDs, rounds, and recurrence constants. The native manifest matches the saved manifest bytes and digest, every frozen slot field and per-slot constraint count, total constraints, tree columns, PCS PoW bits, and four-lane call-address continuity. Package manifest/prover/verifier binary digests match the result. The four-call packages each have 9 slots and 87 constraints; the eight-call package has 17 slots and 163 constraints. Native source geometry is respectively 4,149 / 8,245 / 4,153 source nodes.

I independently evaluated all 66 public assignments from the saved source operations over M31, including every repeated square-plus-constant chip call. Each input follows the frozen claim seed, and each output, assignment SHA-256, statement SHA-256, emitted statement, proof size, and proof SHA-256 matches the saved row. The changed statement alters exactly the first result word by `+1 mod p`; saved logs contain `verified` for the original statement and only `error: InvalidMixedInteractionNonce` for the changed statement. The 60 scored prover start times follow the frozen interleaved schedule exactly.

**Limits:** these are checks of the saved bytes and logs. I did not rerun 132 native verifier invocations, rederive the registry digest algorithm, or prove that a saved success log authenticates arbitrary trace openings. The native study and its [artifact auditor](../../../src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/audit.py) are the executable replay path. The observed cost failure must remain a failure in any summary or downstream calibration record.
