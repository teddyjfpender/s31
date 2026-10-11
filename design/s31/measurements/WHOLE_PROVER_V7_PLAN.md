# Next whole-prover cost study: current-stack prospective gate

Status: **design, not a frozen experiment or fitted model**. The V6 model
passed its original pinned local study, then failed the [same-host transfer](WHOLE_PROVER_TRANSFER_V1.md)
on a changed compiler and engine. Its wall-time predictions must not select
lowerings on the current stack. The saved transfer observations are diagnosis,
not held-out evidence for a revised model.

## Measurement target

Predict, for one exact compiler/engine revision and host, the mean of fresh
prover-process plus native-verifier-process wall time, proof bytes, and prover
peak RSS. Report package build separately. Keep the existing 26-bit proof of
work and record its interaction/FRI stages separately where native timers
expose them. Record the wall difference between the outer process timer and
native runtime stages for both prover and verifier on every trial. This is
needed because the V6 transfer showed a stable process-level offset of about
33 ms in verification and 47–49 ms in unattributed proving at the median of
eight programs, while PoW residuals varied in sign. These are hypotheses to
measure anew, **not constants to add to V6**.

## Freeze before observation

1. Pin the exact S31 and engine commits, compiler fingerprint, host identity,
   profile/FRI parameters, target definitions, and gates. Include **all**
   benchmark and frontend Python files in a sorted path-and-content digest,
   including the RSS predictor and both independent value oracles. Pin native
   build mode and process wrapper. Source and assignment digests for both
   splits must be generated and frozen before the first native package build.
2. Commit the protocol and a UTC freeze anchor. Record the full commit and
   protocol SHA-256 externally before building any study package. The runner
   refuses a missing or mismatched anchor, dirty relevant source, changed
   engine gitlink, or a different host.
3. Collect fresh training packages and proofs. Fit all coefficients and
   intervals from **training only**. Commit the serialized model and a second
   UTC anchor, recording its full SHA externally before any validation build.
4. Collect source- and assignment-disjoint held-out packages. An independent
   publisher reopens package manifests, proof files, statements, assignments,
   trial reports, oracles, and the two anchors; it refits training and replays
   the frozen validation gate. Preserve raw evidence and provide a read-only
   native replay command. A later checkout may add tooling without changing
   the historical frozen files used by the study.

## Workloads and decision

Use at least five training and five held-out programs in each existing family:
direct-gate arithmetic, one-call direct chip, gate hash, and fixed-width
arithmetic. Use at least 100 independent assignments per program to make the
26-bit PoW contribution visible. Source bytes and assignments must differ
across the two splits and from V6 and the transfer corpus. Where the finite
chip-round menu forces a repeated *shape*, disclose it; digest disjointness
alone is not shape novelty. Add mixed-chip programs only after their native
profile and source-pinned verifier are independently reviewed, and give that
family its own training/validation split.

Keep V6's predeclared point-error and empirical-coverage gates as a minimum,
and check per-program process-stage residuals so a family-level interval
cannot hide a systematic startup miss. Any new interval form or threshold is
chosen from training and frozen before held-out packages are built. Passing
this gate would support a **local, pinned-stack** model only; cross-host and
future-revision transfer remain separate gates. Automatic lowering stays
disabled until paired semantically equivalent lowerings are compared on the
same pinned source and workload under a soundness-equivalent verifier.
