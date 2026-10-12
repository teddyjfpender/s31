# Paired public-record v2 direct-gate versus mixed-general study

Status: **anchored study complete**. The [result](PAIRED_RECORD_V2_RESULT.md)
reports native-audited train and held-out measurements. The protocol SHA-256 is
`c1177e83d3e0fb7f37fc232601cc3d20ea6ebe06eda229bee34950968d4cd302`,
and its anchor commit is `6091a0773a02e9445946402df0435ab38e1f06a9`.
Untimed generic N=1 and mixed N=1/N=8 admission controls passed. The first
unanchored protocol candidate (`2d5914a8f8f6436b9fca57515e42cae0979b235a`)
was withdrawn after review found missing train and report gates. Its successor
(`5797738098e828390399e4bd2bfde89a73cc64c3`) was withdrawn when review
found incomplete disk mount and cache override coverage. The corrected protocol
received a new source/tool digest, independent review, and an external
timestamp before the first timed build. This study is separate
from the V8r1 ordinary whole-prover baseline. Automatic lowering remains
disabled regardless of this study's eventual result.

## Question and fair measurement boundary

For the same version-2 public-record S31 relation and assignment, how do the
`direct-gate` and authenticated `direct-mixed-general` lowerings compare as
shipped native executables? Eight normalized relations have 1 through 8 live,
dependent 16-round `square; add constant` calls followed by a public four-lane
result. Each has 100 distinct public inputs, or 800 assignment pairs and 1,600
arm trials. Train call counts are 1, 2, 4, 6; held-out counts are 3, 5, 7, 8.
The [prospective design](language/paired-record-v2-prospective.json) fixes the
menu, seeds, build mode, balanced order, and bootstrap rule before native
measurement. Each arm in a pair is built from **the same normalized source
bytes** and checked against **the same canonical typed public statement**.

The ordinary direct-gate `prove` command self-verifies internally. The mixed
prover does not. Comparing those prover process times would charge direct-gate
for an extra verifier. This study uses the explicit v2 direct-gate
`prove-for-external-verification` command, which writes an **unverified** proof
and omits only that internal verification. The runner accepts a trial only
after the separately installed, source-embedded generic verifier accepts it.
The mixed arm likewise runs its prover followed by its separate source-embedded
native verifier. Each timed arm therefore has one prover process, one verifier
process, and one native verification. `first_verified_wall_seconds` is the
sum. It includes both process startups, native setup and PoW; it excludes
package compilation, Python orchestration, independent oracle, and negative
controls. It is the **sum of two measured process wall times**, excluding
Python's gap between the processes. Prover and verifier process times, peak
RSS, proof bytes, and build times remain separate. Generic native
witness/setup/prove timers are saved
when available; the mixed CLI currently exposes only process wall time, so
native stage-by-stage speed comparisons are unavailable. The ordinary
self-verifying `prove` behavior is unchanged.

The mixed prover also evaluates the relation twice in its shipped workflow.
The paired ratio therefore describes these **complete shipped prover and
verifier workflows** for this source family, not pure AIR or chip arithmetic
speed. The pinned Python collector and host monotonic clock/resource reports
are trusted measurement inputs. The ledger and external phase anchor detect
later evidence edits; they cannot prove collector or clock honesty.

The study estimates the median of paired `log(generic/mixed)` ratios per call
count, with a 95% assignment-paired percentile bootstrap interval. Ratios
above one favor mixed. It reports absolute medians too. There is no chosen
speedup gate, automatic dispatch policy, cross-host performance claim, or
proof-system soundness claim from timings. The two AIRs have different
component geometry, and that difference is part of the comparison. Even
matching visible PCS/FRI/PoW settings would not establish equal soundness;
the cost result remains profile-specific with separate soundness analyses.
Intervals are descriptive per count and metric; they do not correct for
looking across eight call counts and five metrics.

## Freeze and admission

The v2 direct-gate generic package uses the existing sealed key and typed
record ABI. The mixed arm is currently an **attested source-embedded Zig CLI
bundle**, not a general `s31 build` package. Its native manifest reports the
source digest, canonical IR digest, call roster, slot roster, registry digest,
and circuit identity. The runner independently recomputes the registry digest
and records binary, saved inspection, and manifest file hashes. A fresh run
of the source-embedded inspector must reproduce the saved inspection exactly.
This is a narrow study admission,
not general mixed package support.

After all code and engine gitlink changes settle, in a clean S31 checkout:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/test_static.py
python3 src/frontends/s31/benchmarks/paired_record_v2/design.py
python3 src/frontends/s31/tests/acceptance/paired_record_v2_gate.py
python3 src/frontends/s31/tests/acceptance/mixed_boundary/record_general_v2.py
python3 src/frontends/s31/benchmarks/paired_record_v2/protocol.py draft
git add design/s31/measurements/language/paired-record-v2-protocol.json
git commit -m 'Freeze paired record v2 protocol'
```

Create `design/s31/measurements/language/paired-record-v2-freeze.json` with
schema `s31-paired-record-v2-freeze-v1`, the **full** SHA-256 of the protocol
file, and a real UTC `recorded_at_utc`; commit it. Record the full protocol
hash and full anchor commit in an independent timestamped message **before
the first paired measurement package build**. The untimed native acceptance
builds above are disclosed prefreeze checks; they produce no paired timing
corpus. The runner requires both exact values and
checks the anchor's ancestry, committed bytes, source, tool and compiler
fingerprints, engine gitlink, host, design, and regenerated inventory.
An uncommitted or merely prospective design cannot authorize measurements.

`build` rejects an existing evidence directory. `prove` rejects absent or
changed build attestations and any existing partial or completed corpus. The
build phase records monotonic start/end nanoseconds for each exact package
workflow in a separate fsynced hash-chain ledger. Its canonical build root
binds the ledger, every `build-times.json` byte sequence, and every package
attestation. The later externally anchored proof phase root binds that entire
build root and repeats its per-case hashes. `prove` and `audit` require the
build ledger's exact generic-then-mixed roster; `audit` rederives each duration
and rejects any saved build-time mismatch, even if a local build root was
recomputed. The package identities are independently regenerated from the
current generic binaries/key/manifest and source-embedded mixed inspector
before this replay.

`audit` additionally requires a committed, externally timestamped phase-root
anchor. It rejects absent proofs, changed bytes, failed native replay, changed
public claims accepted by either verifier, same-geometry alternate-source
proofs accepted, a modified proof-header manifest digest accepted, altered
valid public claims mishandled, and mismatched protocol or trial order. The
runner checks at least 8 GiB free on the evidence, Zig local/global caches, and
temporary-file filesystems at phase start, before each build arm, before each
proof arm, and before audit control builds. It does not poll during an
individual native process; a failed unit leaves partial evidence that must be
discarded. The build gate requires an exact live `FriConfigV2`
and matching interaction PoW bits across arms, while preserving and reporting
each arm's full PCS configuration, including potentially different lifting.
The collector also requires supported `/usr/bin/time` RSS output and fails
if the raw resource report is missing or unparseable. No timing may be
interpreted if any gate fails.

Run the two native phases only with exclusive access to the host and at least
8 GiB free. Use a fresh evidence directory and never reuse failed paths:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase build --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit>
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase prove --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit>
```

The `prove` phase prints the full SHA-256 of `phase-root.json` but emits **no
analysis**. For each arm it durably stores separate native stdout/stderr,
the raw `/usr/bin/time` RSS report, combined logs and proof bytes. It appends
one canonical, fsynced hash-chain event after the external verifier accepts
and changed-claim controls reject. The event records the exact source, claim,
package, executable, proof, process argv, monotonic start/end nanoseconds,
raw RSS evidence, output hashes, and exit status. The phase root binds the
complete ledger and corpus. A failed or partial proof phase must be discarded,
not resumed.

Create `design/s31/measurements/language/paired-record-v2-train-phase-anchor.json`
with schema `s31-paired-record-v2-phase-anchor-v1`, split `train`, the full
`phase_root_sha256`, the full `protocol_sha256`, and a real UTC
`recorded_at_utc`; commit it. Record the full phase-root hash and full phase
anchor commit in an independent timestamped message **before audit or any
summary**. Then run:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase audit --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit> \
  --expected-phase-root-sha256 <full-phase-root-hash> \
  --phase-anchor-commit <full-phase-anchor-commit>
```

The phase-root anchor seals the raw timed corpus, but the later audit and
analysis need their own seal. Create
`design/s31/measurements/language/paired-record-v2-train-report-anchor.json`
with schema `s31-paired-record-v2-report-anchor-v1`, split `train`, the full
`protocol_sha256`, `phase_root_sha256`, `phase_anchor_commit`, SHA-256 of the
canonical saved `audit.json` and `analysis.json` as `audit_sha256` and
`analysis_sha256`, and a real UTC `recorded_at_utc` after the phase anchor.
Commit it and externally record both full report hashes and the full report
anchor commit **before** the first held-out build. Run the read-only report
check before using any train conclusion:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase report-check --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit> \
  --expected-phase-root-sha256 <full-train-phase-root-hash> \
  --phase-anchor-commit <full-train-phase-anchor-commit> \
  --report-anchor-commit <full-train-report-anchor-commit>
```

`report-check` replays every reported trial against the anchored raw ledger,
proof bytes, process/resource logs, source and package artifacts; rederives
the analysis from the sealed corpus and build ledger; and compares the exact
audit and analysis bytes with the committed report hashes. It does not rerun
the native negative controls from `audit`: their passed result is bound by the
report hash and remains a trusted observation of the pinned collector.

For the completed study, replay from the pinned measurement worktree at
`f2f55411879319e74e08dfe078f7b440a20fdd63`, with the original
`zig-out/s31-paired-record-v2/{train,heldout}` evidence and engine gitlink
`7d544c6839497ca19b6c7ef9b982e464f10cfeed`. The protocol checks the
compiler and measurement-tool fingerprints frozen before timing. A later S31
checkout with compiler edits is expected to fail admission even if the saved
evidence is intact; use the pinned checkout for report replay.

Repeat for `--split heldout` with its own fresh `.../heldout` path and
`paired-record-v2-heldout-phase-anchor.json`, only after train phase and
report anchors are externally recorded. **Every** held-out `build`, `prove`,
`audit`, and `report-check` invocation must add:

```sh
  --train-out zig-out/s31-paired-record-v2/train \
  --expected-train-phase-root-sha256 <full-train-phase-root-hash> \
  --train-phase-anchor-commit <full-train-phase-anchor-commit> \
  --train-report-anchor-commit <full-train-report-anchor-commit>
```

The held-out build records the train admission digest in its build root; later
phases recheck the exact anchored train evidence and admission bytes. After
held-out audit, create, commit, and externally record the analogous held-out
report anchor, then run held-out `report-check` before publishing any ratio.
The runner saves proof bytes, canonical
typed statements, changed-claim controls, per-arm process times/RSS, package
attestations, the raw ledger and phase root, complete corpus, replay audit,
and analysis. Audit reconstructs every reported timing, RSS, proof size,
arm, source and statement identity from the externally anchored raw events,
compares the entire corpus exactly, and only then computes the summary.
Failed controls abort the phase; do not extract a speedup from a partial corpus. The held-out
analysis is independent of training and is not used to tune the protocol.
The prefreeze admission builds warm Zig's cache before package-build timing. Report
those build times as observed warm-cache package costs, with cache state and
host disclosed. The generic build is the full `s31.build` package workflow;
the mixed build is one direct Zig install of the source-embedded bundle. These
different shipped workflows and warm cache make the numbers unsuitable for a
pure compiler or cold-build speed comparison. The pinned collector and host
monotonic clock remain trusted inputs to build timing as well as proof timing.

## Native admission controls

Before accepting a cost claim, exercise these controls with the frozen
executables and then replay them from saved evidence:

1. The independent Python recurrence and relation oracle agree for each
   assignment. Source bytes, flattened semantics, record ABI, assignment
   bytes, typed statement, compiler, engine and build artifacts are hashed.
2. Both source-embedded native verifiers accept every saved proof against the
   same typed public claim. Changed public input and changed result are
   rejected for every proof.
3. Build alternate generic and mixed verifiers from a source differing only
   in the top-level program name. Require the same call count, ABI and native
   geometry, then require each alternate verifier to reject the original
   source's proof and accept a new proof from its own source. This isolates
   source-digest binding from a geometry mismatch. Flip the mixed proof
   header's bound registry-manifest digest byte and require rejection; this
   tests proof-header binding, not a general AIR substitution.
4. Increment a public input lane and recompute the matching output using the
   complete 16-round recurrence. The independent relation oracle must agree.
   Both provers must successfully produce a proof for the new typed claim;
   both native verifiers must accept it and reject that proof against the
   original typed claim. The mixed prover must specifically reject the valid
   changed assignment paired with the original expected statement as
   `InvalidMixedPublicStatement`. This source has **no private witness**.
5. The mixed component inspector's registry digest is recomputed independently
   from its typed slots and schedule; its canonical IR digest must match the
   generic compiler's sealed cost report. The generic package verifier checks
   its sealed key and component manifest before any trial.
   Both arms' actual PCS/FRI/PoW settings must be reported from the live
   source-embedded verifier or manifest and compared before a cost statement;
   do not infer mixed settings from a generic package default.
6. The study's direct-gate v2 admission needs focused native regression of
   ordinary v1 `prove`, ordinary v2 self-verifying `prove`, v2
   `prove-for-external-verification` plus external verifier, and mixed v2 N=1
   and N=8. The unchecked command may never be treated as acceptance by
   itself.

The generic and mixed proof systems' soundness assumptions remain those of
their native STARK verifier and pinned AIR/PCS/FRI implementation. Matching
one source and passing negative controls do not prove arbitrary compiler
correspondence. This narrow source family has no private input; general
private-boundary performance must be studied separately.
