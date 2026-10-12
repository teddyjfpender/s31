# Independent review: stage-resolved cost transfer v1

I audited the published [protocol](STAGE_RESOLVED_COST_V1.md),
[result](STAGE_RESOLVED_COST_V1_RESULT.md), frozen
[plan](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/plan.json),
calibration, runner, second-source scorer, original local trial evidence,
and compact publication. I found **no concrete flaw that invalidates this
local holdout**. All ten predeclared diagnostic gates passed. That pass does
not make the raw whole-wall estimate precise enough for one-shot scheduling.

## Freeze and data separation

The original local `plan.json` has SHA-256
`90b9369a734a30d8f6295e15762d9bde5e5e91a044c6aa62b9a9a6216b9b8446`.
Its local mtime is 19:25:51 on 2026-10-11, before the first new package
manifest at 19:28:38; the other two package manifests followed at 19:29:34
and 19:30:29. The held-out report and score were saved at 19:30:33, and
native replay audit at 19:30:45. These mtimes are supporting **local**
chronology, not an external timestamp or immutable pre-phase commit. The
runner rejects an existing output directory for planning and checks the
whole plan against freshly derived source, assignment, calibration, code,
compiler, engine, oracle and host identities before the first new build.
The plan pins the prospective scorer and its diagnostic limits. The later
publication and historical calibration replay were written after the new
measurement and correctly mark themselves post hoc.

The [historical ledger](../../../src/frontends/s31/benchmarks/stage_resolved_v1/historical-stage-ledger.json)
contains nine complete 12-trial programs. Alternating and all-add programs
at 96, 256 and 448 gates form the **six-source, 72-trial fit**. Three
all-multiply programs, **36 trials**, calibrate intervals only; no trial
from them enters a point center. The three new lagged-alternating source
hashes are distinct from all nine historical hashes. The frozen
[calibration](../../../src/frontends/s31/benchmarks/stage_resolved_v1/calibration.json)
pins both ledger and model-source hashes. I reran the independent, post hoc
[calibration replay](../../../src/frontends/s31/benchmarks/stage_resolved_v1/posthoc_calibration_audit.py)
read-only: it reproduced 21 stage records (including distinct first/later
process residual centers), 24 phase-specific target centers and eight ratio
bands. That replay checks arithmetic consistency; its code
was **not** prospectively pinned.

## What the 36 trials show

Each new source was built once; sample 0 was the first proof process after
that build, then samples 1–11 ran in order. The original saved files have
strictly increasing trial-report mtimes at each size. The seven measured
terms reconstruct `prover process wall + external verifier process wall`:
witness, setup, native proving excluding reported PoW, reported PoW,
remaining native runtime, prover process residual, and verifier process wall.
The residual is measured process wall minus the native package timer; it
includes unclassified startup, parsing and I/O, and is not native setup.

I reran the prospectively pinned
[second-source scorer](../../../src/frontends/s31/benchmarks/stage_resolved_v1/independent_score.py)
read-only on all 36 original local trial reports and proofs. It checked
source, assignment, report, package and proof hashes; oracle provenance;
native accepted/changed-claim flags; seven-term arithmetic; first/later
partition; saved point errors; interval coverage; and all ten gates. Its
result was **36 trials, three cases, all ten gates passed**. The saved
[native replay audit](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/audit.json)
records 36 original proofs accepted and 36 changed claims rejected. I
verified that the published plan, report, score and audit are byte-identical
to the original local files and that the compact ledger's audit hash points
to that audit. I did not run an additional independent native proof replay.

| Metric, later processes | Observed result | Frozen local gate |
| --- | ---: | ---: |
| Whole-wall interval coverage | 31/33 = 93.94% | at least 75% |
| Wall after reported PoW coverage | 30/33 = 90.91% | at least 80% |
| Proof-byte coverage | 30/33 = 90.91% | at least 80% |
| Peak RSS coverage | 32/33 = 96.97% | at least 80% |
| Maximum program-median error after reported PoW | 2.95% | at most 15% |
| Maximum program-median error, proof bytes / RSS | 2.75% / 0.88% | at most 10% each |

First-use whole-wall coverage was 3/3 against a 2/3 gate. Observed first-use
process residuals were 420–432 ms; later program medians were 14.90–18.50
ms. The model accounts for that phase change. Later raw whole-wall **point**
errors were 18.41–19.35% across the three programs; no wall point-error gate
was predeclared. The later wall interval is 0.349–3.201 times its center,
and its 3.201 upper ratio passes the permissive 8× width gate. That wide
interval can cover PoW variation while giving little precision for a
single scheduled proof. The after-reported-PoW upper ratio is 1.083× and
passes 1.5×, but subtracting a measured PoW timer from the same proof is
an accounting view, not a faster proving mode. Three first-use calibration
points and three new first-use observations cannot support a tail guarantee.

## Scope and auditability

The committed [compact ledger](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/compact-trials.json)
preserves all 36 stage records, key hashes, shapes and control outcomes.
Raw proofs, statements, package binaries and original trial reports remain
only in the ignored local `zig-out/s31-stage-resolved-v1` directory (about
28 MB). Therefore another reviewer can recompute the published arithmetic
and inspect hashes from Git, but cannot rerun native verification from the
committed files alone. The local audit supplies evidence for this run;
durable third-party native replay would require preserving the raw bundle.

This is one host, compiler, engine, `direct-gate` lowering and held-out
dependency graph at three sizes. Package build time (about 52–53 seconds)
is outside the paired proof-process target, as are Python orchestration and
audit replay. The sources exceed the 1–16-gate bounded compiler
correspondence certificate. These measurements support neither chip or
cross-host transfer nor a formal proof of compiler or STARK soundness.
Automatic lowering remains disabled.
