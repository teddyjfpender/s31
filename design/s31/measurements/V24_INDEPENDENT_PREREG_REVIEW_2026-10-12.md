# V24 independent preregistration review — 2026-10-12

Scope: the pre-native V24 conditional-repeat protocol introduced at `98bf2c5`, its source generator, frozen forecasts, runner, lifecycle scorer, and independent audit. This review was performed before the V24 native timing attempt. It does not count as a cost-model pass.

## Findings

- The source and 21-claim roster are frozen by canonical SHA-256 identities. The source has four 1,280-operation branches, eight ordered repeated-square calls, and the frozen log-13/17-slot/163-constraint manifest expectation. The protocol pins a source SHA-256 of `9755a1005c8533607e2457b3c900f6d0d81cb4dabfed3b02697c57d0357ee5f9`.
- The prediction uses the pre-existing V18 model's log-13 eight-call non-PoW center, `150,345,958 ns`. Each repeat's PoW prediction uses only the **first proof of the same claim**, measured before the repeat. The repeat's own PoW does not enter its prediction. This is a prospective online same-claim prediction, not an unconditional out-of-sample repeat prediction.
- I independently recomputed the V18–V20 five-record build median (`78,172,015,042 ns`), first-use median (`1,212,335,333 ns`), and the frozen build-plus-42-process forecast (`88,613,278,793.3421 ns`). The three prior result SHA-256 pins match their files; the 20 fresh claim indices form exactly `1..20`.
- The runner's quiet-host preflight precedes an `O_EXCL` attempt marker; a failure after that marker consumes the one native attempt. It builds and checks the native manifest before proving, requires 42 honest verifications and 42 changed-result rejections, and saves proof hashes, process endpoints, and phase reports for replay. A static test covers both preflight snapshots. No native timing was run during this review.
- The original independent audit trusted three saved V24 extra-gate booleans without recomputing them. Commits `c6ca124` and `334b951` fix that gap and add a static test that flips each independently scored metric while the saved flags remain true. Seven V24 static tests pass after the fix. These changed tool hashes must be included in the final pre-native protocol amendment and pushed before the attempt.

The repeat forecast is deliberately conditional on an already observed proof of the exact same assignment and statement. A V24 pass would support that narrow online prediction on this source and host; it would not erase the failed V17 or V23 unconditional repeat gates, establish cross-host calibration, or show a Cairo speedup.
