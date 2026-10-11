# Paired public-record v2 direct-gate versus mixed-general study

Status: **prospective tooling only; no paired native timing result**. This
study is separate from the frozen V8 ordinary whole-prover baseline. Do not
run its native build or trial phases while V8 owns the machine. Automatic
lowering remains disabled regardless of this study's eventual result.

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
changed build attestations and any existing partial or completed corpus.
`audit` rejects absent proofs, changed bytes, failed native replay, changed
public claims accepted by either verifier, wrong-source/component/witness
controls accepted, and mismatched protocol or trial order. All phases fail
closed below 8 GiB free. The build gate requires an exact live `FriConfigV2`
and matching interaction PoW bits across arms, while preserving and reporting
each arm's full PCS configuration, including potentially different lifting.
No timing may be interpreted if any gate fails.

Run the two native phases only with exclusive access to the host and at least
8 GiB free. Use a fresh evidence directory and never reuse failed paths:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase build --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit>
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase prove --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit>
python3 src/frontends/s31/benchmarks/paired_record_v2/runner.py \
  --split train --phase audit --out zig-out/s31-paired-record-v2/train \
  --expected-protocol-sha256 <full-hash> --anchor-commit <full-commit>
```

Repeat for `--split heldout` with a fresh `.../heldout` path only after the
train corpus is sealed and reviewed. The runner saves proof bytes, canonical
typed statements, changed-claim controls, per-arm process times/RSS, package
attestations, complete corpus, replay audit, and analysis. Failed controls
abort the phase; do not extract a speedup from a partial corpus. The held-out
analysis is independent of training and is not used to tune the protocol.
The prefreeze admission builds warm Zig's cache before package-build timing. Report
those build times as observed warm-cache package costs, with cache state and
host disclosed; they are not cold-compiler speed comparisons.

## Native admission controls

Before accepting a cost claim, exercise these controls with the frozen
executables and then replay them from saved evidence:

1. The independent Python recurrence and relation oracle agree for each
   assignment. Source bytes, flattened semantics, record ABI, assignment
   bytes, typed statement, compiler, engine and build artifacts are hashed.
2. Both source-embedded native verifiers accept every saved proof against the
   same typed public claim. Changed public input and changed result are
   rejected for every proof.
3. A verifier built for one relation rejects a proof from another relation.
   The mixed verifier rejects a proof with a changed registry-manifest digest.
   A changed witness cannot establish the original typed statement.
4. The mixed component inspector's registry digest is recomputed independently
   from its typed slots and schedule; its canonical IR digest must match the
   generic compiler's sealed cost report. The generic package verifier checks
   its sealed key and component manifest before any trial.
   Both arms' actual PCS/FRI/PoW settings must be reported from the live
   source-embedded verifier or manifest and compared before a cost statement;
   do not infer mixed settings from a generic package default.
5. The study's direct-gate v2 admission needs focused native regression of
   ordinary v1 `prove`, ordinary v2 self-verifying `prove`, v2
   `prove-for-external-verification` plus external verifier, and mixed v2 N=1
   and N=8. The unchecked command may never be treated as acceptance by
   itself.

The generic and mixed proof systems' soundness assumptions remain those of
their native STARK verifier and pinned AIR/PCS/FRI implementation. Matching
one source and passing negative controls do not prove arbitrary compiler
correspondence. This narrow source family has no private input; general
private-boundary performance must be studied separately.
