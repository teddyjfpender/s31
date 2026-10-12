# Mixed source inspection context reuse: matched local measurement

**The validated topology reuse reduced the measured profile-rebuild stage by
1.224 ms paired median (30.0% of its 4.082 ms baseline median) on one
`gate_weave_n1` program.** The measured whole-process change is smaller than
run-to-run noise, so this run does not establish a reliable whole-prover
speedup. The native proof format, source manifest, circuit identity, PCS
parameters, and proof bytes were unchanged.

## Change and safety checks

Before the change, mixed source inspection called `inspectMany`, which
compiled and validated a witness-free circuit, then discarded it. It then
called `compileManyTopology`, which rebuilt the source topology and compiled
another witness-free circuit. The new `inspectManyWithTopologyContext` returns
the already validated context to the mixed inspector. The ordinary
`inspectMany` API still discards it. The reused circuit had already been
checked against an independent source compilation for exact endpoint map,
circuit dimensions, and fixed preprocessed root. The inspector rechecks the
source SHA-256 before using that circuit for native geometry.

The focused `test-mixed-registry` regression deep-compared every Gate circuit
view field from the reused and full-rebuild contexts for N=1 through N=8,
then compared the complete selected native geometry and fixed root. The
`test-mixed-general-native` proof suite passed, including honest native
verification and changed-public-claim rejection. Both tests ran in
ReleaseFast after the change.

## Matched sample and provenance

The baseline is the saved V10 package built at commit `a4230b3`; the changed
package was built at commit `9645893`, both ReleaseFast with the same embedded
V10 `gate_weave_n1` source (SHA-256
`2b7423d2aff12c906d7ecb29343aeff38a9e292c599c23bc473c33c602cc8c14`).
The Stwo engine gitlink and production frontend files other than the two
changed runtime files are identical between those commits. The baseline and
changed prover SHA-256 values are respectively
`8b27035643d474cc027dd41299ce37ff359e15c19f90caf1ea597c10fd523660`
and `c160905be0229ef9b40553e19748c150005d94e2449285bd704576d0d9d6ef61`.
The verifier binaries are pinned in the [compact result](language/mixed-context-reuse-v1-result.json).

The [matched runner](../../../src/frontends/s31/benchmarks/mixed_context_reuse/study.py)
has SHA-256 `149accc63c72a12d3f5fd8f368531137e7db8eed8cbcef62c152bae106281cb0`.
It alternated binary order for each assignment. Claim 0 was an unscored
warmup; 40 further saved V10 assignments were scored. The 41 baseline and
changed proof pairs were byte identical. All 82 honest proofs verified in
their source-embedded native verifiers, and all 82 valid changed-result claims
were rejected at `InvalidMixedInteractionNonce`.

The raw source, assignments, and baseline V10 artifacts are at
`/tmp/s31-v10-geometry-transfer-a4230b3/gate_weave_n1/`; the new package,
matched proof bytes, and stderr are at
`/tmp/s31-mixed-context-reuse-9645893/`. For example, scored claim 1 uses
assignment SHA-256
`3ec64b19c15149a0e2a3cfbcb084eac844e8c25eed70f17f28f353aa609a519d`;
both newly saved proof files have SHA-256
`194452e87da678ac27a0356af4d205314273c8b110b20bba1f12b361ce611bb7`.
The compact result stores proof, statement, source, manifest, circuit, and
binary hashes for every pair, plus each timing record. Its SHA-256 is
`0f9d509ced57b2cad26d6a60a0a2710d6d257fc71670267253b97a5803388df2`.

## Observed timings

All numbers are milliseconds across the 40 scored assignments. A paired
delta is the median of `baseline − changed` on the same assignment; it need
not equal the difference between the two marginal medians. MAD is median
absolute deviation of those paired deltas.

| Interval | Baseline median | Changed median | Paired delta | Paired MAD |
| --- | ---: | ---: | ---: | ---: |
| Profile rebuild | 4.082 | 2.851 | +1.224 | 0.077 |
| Whole package | 77.323 | 76.475 | +0.799 | 1.325 |
| Prover process | 89.100 | 87.221 | +0.701 | 2.063 |
| Prover plus external verifier processes | 109.931 | 105.296 | +2.049 | 2.564 |
| Native prove including setup | 71.471 | 71.252 | −0.580 | 1.310 |

The profile stage saving is stable relative to its 0.077 ms paired MAD and
is the direct target of the change. Native proving and FRI proof of work were
not changed. The process and full package paired deltas are of similar size
to or smaller than their timing spread; this single local run cannot resolve
a whole-prover speedup. It does not predict other sources, machines, batch
sizes, or a Cairo comparison. The raw artifact directories are local and
must be retained for native replay; the committed compact result supports
hash and timing review without those raw files.
