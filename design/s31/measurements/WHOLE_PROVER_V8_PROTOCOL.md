# Prospective V8 whole-prover cost study

Status: **the frozen V8 fit gate failed before a model was produced; no V8
accuracy result or held-out observation exists**. A separately versioned V8r1
repair must be frozen before any new native data is collected.
The machine-readable [prospective design](language/whole-prover-cost-v8-prospective.json)
and its [static inventory generator](../../../src/frontends/s31/benchmarks/cost/v8_design.py)
fix the workload menus, disjointness rule, uncertainty method, and gates. The
[baseline runbook](WHOLE_PROVER_V8_RUNBOOK.md) describes the implemented
collector, fitter, independent gate checker, native artifact publisher, and
portable replay. The baseline [frozen protocol](language/whole-prover-cost-v8.json)
has SHA-256 `dff9ed804a9a5c50189f569adceae0ba68a25cebcfa4d98c899065f2ab769abd`
and committed anchor `cdfe86cf7047a630c945cca7f8b8706295bc3623`; both
were recorded externally on 2026-10-11 at 05:22:10 UTC before native
training. An interrupted overlapping first build was quarantined with no
completed package or timed corpus, then training restarted from clean
evidence paths as recorded in the runbook. The general mixed profile must be
packaged as an equivalent generic/mixed pair before the paired comparison
can be frozen or measured.

The clean V8 training restart built all 23 packages and verified 100 proofs
per program, with corpus SHA-256
`6de6546243f81d80bf862d99f8acd191dd6fa828bb92d17b5fe6a25daa475d95`.
The frozen fitter then rejected the program roster: its inherited V3 check
read `signed_128_output`, while the V8 protocol used `signed_128_result` and
the corpus correctly contained `signed_quotient_128`. It exited before model
output. No held-out package was built. The V8 training data and failed gate
remain preserved as diagnostic evidence; they are not an accuracy result and
must not be silently reused by a repaired protocol.

## Why V8 is a new study

[V7r1](WHOLE_PROVER_V7_RUNBOOK.md) failed its frozen RSS coverage gate:
chip-family coverage was 75.2% against an 80% minimum; `chip_8192` and
`hash_13` had 0% and 3% coverage against a 70% per-program minimum. Its
wall-time, proof-byte, process-stage, saved native proof, changed-claim, and
portable integrity checks passed. The [V7r1 audit](language/whole-prover-cost-v7r1-audit.json)
is diagnostic context only. Inspecting that failure motivated a training-only
absolute/relative uncertainty envelope with a fixed 2 MiB floor and more
size-stratified training programs. This is a disclosed design response to a
known validation failure: V7r1 is **not** an independent test of the V8 method.
No V7r1 validation trial, measured RSS, fitted coefficient, interval, or
gate result enters V8 fitting or calibration. V7r1 is never rescored.

V8's independent accuracy test uses fresh source and assignment bytes in a
new held-out split. Arithmetic/chip/hash shapes can repeat historical shapes;
source and assignment byte disjointness is the claim. The generator checks
both splits against V6, the V6 transfer study, the aborted V7 protocol, and
V7r1 before native work. It rejects any collision. The final frozen protocol
must commit the resulting SHA-256 inventory. No program or trial can move
between splits after freeze.

## Workloads and measured quantity

The ordinary cost model retains four V7 families and predicts a fresh prover
process plus a fresh native verifier process, proof bytes, and prover peak RSS.
Package build time, native prover stages, unattributed process time, and native
verifier time are separate recorded targets. Every program has 100 distinct
assignments; all use the same pinned 26-bit interaction/FRI PoW configuration
as the final source profile. The static menus are:

| Family | Train | Held out |
| --- | --- | --- |
| Direct-gate arithmetic repeat rounds | 16, 80, 320, 1280, 5120, 12288 | 32, 120, 480, 1920, 7680 |
| Direct-chip repeat rounds | 16, 32, 64, 256, 1024, 8192 | 128, 512, 2048, 4096, 16384 |
| Gate Blake2s chain depth | 2, 3, 5, 7, 10, 14 | 4, 6, 8, 11, 13 |
| Signed width division | 8, 16, 32, 64, 128 | 8, 16, 32, 64, 128 |

The signed widths below 128 expose quotient and remainder limbs together.
The eight-word public ABI requires the 128-bit training program to expose the
quotient and the 128-bit held-out program to expose the remainder. Source names
and assignment index ranges are distinct across splits. There are 23 training
and 20 held-out programs, or 4,300 baseline trials. A pinned independent
value oracle checks generated assignments before packaging, and native
verifiers check each saved proof and a changed public claim.

For a training family, use the same V7 point-fit form but fit all coefficients
from **fresh V8 training** observations. RSS interval calibration uses
leave-one-program-out training residuals. For each excluded training program
`j`, fit the center on the other training programs; let `r_j` be the larger
absolute value of the 5th and 95th percentile trial residuals for `j`, and
let `c_j` be its positive out-of-fold center. For a new feature vector `x`:

```text
A = max_j r_j
R = max_j (r_j / c_j)
radius(x) = max(A, R * center(x), 2,097,152 bytes)
RSS interval(x) = [max(0, center(x) - radius(x)), center(x) + radius(x)]
```

This rule and the floor are chosen before V8 observations. The floor is a
predeclared absolute uncertainty allowance, not a correction computed from
the V7r1 held-out errors. It may still fail on V8 held-out data; no widening
after inspection is permitted. Wall and proof-byte interval methods and all
V7 accuracy thresholds remain unchanged. In particular, RSS must meet 80%
trial coverage per family and 70% per program, with the existing interval
width and median error bounds. Each program must also pass the prover
unattributed-time and native-verifier process-stage error gate. Passing on
one host does not establish cross-host or future-revision transfer.

## Paired authenticated mixed versus generic costs

This is a **conditional, separately reported** companion experiment. The
[bounded general mixed profile](../language/MIXED_GENERAL_NATIVE_PROFILE.md)
has local N=1..8 native acceptance, but its paired generic/mixed package gate
has not passed. It has no paired cost result and is absent
from the ordinary V8 model. The admission gate requires a reviewed and
native-tested N=1..8 source-pinned verifier, sealed generated component
manifest, source-equivalent generic and mixed packaged CLI lowerings, a
representative workload, independent public-output oracle, and wrong-source,
wrong-claim, wrong-component, and wrong-witness negative controls. Both
packages must be built from one committed semantic S31 source per pair, on
the same compiler, engine, host, FRI settings and optimization mode. Different
AIRs and proof profiles are recorded explicitly; neither verifier can borrow
the other's source or component manifest.

The current generic CLI verifies its freshly created proof inside the prover
process before writing it; the general mixed CLI does not. Their raw prover
process wall times therefore include different work. A paired speed claim
requires aligned phase instrumentation or an explicitly matched self-check
policy before freeze. Until then, any exploratory wall times must be labeled
as those two different CLI behaviors and cannot establish a prover speedup.

The prospective train call counts are 1, 2, 4, 6; the held-out counts are
3, 5, 7, 8. Each pair uses 100 fresh assignments and public claims. Both
lowerings run on each assignment, with a deterministic balanced order: 50
generic-then-mixed and 50 mixed-then-generic, recorded before measurement.
Build each arm separately and record build time. Save full native proof and
verification artifacts for both arms. Compare paired prover time, verifier
time, their sum, proof bytes, and prover peak RSS. Report absolute costs and
the per-pair median of `log(generic / mixed)` with a 95% paired bootstrap
interval; the pairing unit is one assignment. Do not convert the result into
an automatic lowering choice. No speedup threshold is assumed. The intended
sample is eight pairs, 16 packages, and 1,600 arm trials in addition to the
ordinary study, conditional on admission and resource review.

The final executable protocol must pin the exact pair source and assignment
digests, generic/mixed CLI commands, profile IDs, component manifest hashes,
balanced order seed, bootstrap algorithm and seed, and native artifact paths
**before** either arm is built. If the general profile cannot meet this gate,
publish the ordinary V8 study as an ordinary study only and explicitly mark
the paired experiment unrun. Do not infer mixed performance from direct-chip
or fixed N=3/N=4 profiles.

## Freeze and release sequence

1. Admit and package the general mixed profile, or explicitly exclude the
   paired experiment. The baseline V8 runner, train-only fitter, independent
   gate implementation, native publisher, and content-addressed portable
   replay are implemented. Review the source and existing static tests before
   freeze. A paired runner and both mixed/generic verifier controls remain a
   separate admission requirement.
2. On a clean committed S31 checkout and clean engine checkout at the gitlink,
   generate both inventories. Freeze exact source-base commit, compiler
   fingerprint over every source byte it reads, engine revision, transitive
   benchmark/Python tool path and SHA inventory, host identity, FRI/PoW
   configuration, package build mode, every source and assignment digest,
   split menus, uncertainty algorithm, and gates in a **new** immutable V8
   protocol. Pre-freeze `null` pins in the prospective design are deliberate
   blockers. Reject source, tool, host, package geometry, or engine drift.
3. Commit the protocol and its anchor. Externally timestamp the full protocol
   SHA-256 and anchor commit before the first training native build. Build and
   prove only training packages; retain raw proof, manifest, process-stage,
   assignment and negative-verifier evidence. Fit the model from training
   alone; commit model and anchor, then externally timestamp their full hashes
   before the first held-out package build.
4. Build, prove, and evaluate the untouched held-out programs and any admitted
   paired held-out experiment. Run independent gate recomputation, saved
   native verifier controls, and relocated portable replay with native
   verification and `--require-pass`. If accuracy fails, preserve its failed
   evaluation and audit/replay integrity without `--require-pass`; never refit
   or silently soften a gate.

The final runner must refuse native work unless all committed and externally
recorded pins are supplied, both anchors have the required ancestry, at least
8 GiB remains free before each native phase, and the source/host/tool identity
matches the protocol. The prospective design alone is not a frozen source
fingerprint and authorizes no native observation. The separately frozen
baseline protocol authorizes the pinned ordinary V8 run. Automatic lowering remains disabled
until a passing pinned study and a separate soundness-equivalence review.
