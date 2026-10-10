# Whole-prover cost model V6: prospective chip RSS transfer

**Status: frozen protocol in an isolated study worktree; training package
builds are under way. No V6 timed proof, fitted model, or held-out result
exists yet.** The integrated tree retains the prospective draft protocol;
the frozen study worktree is pinned to source base
`1b04f77c87e650cd4cc24727b23d2b3d1d5718b6`, engine
`fb300ed1bcfac3299f249928fdfe18f4345deae6`, protocol SHA-256
`c839427e3651a92f07710e5fc446cfa8fb022fbe4f70245d8fa22ec01c5c5b14`,
and committed protocol anchor
`b3191bd5d9c0b7a2afc71b440e9c2e636ef1d2af`. These full pins were
recorded externally before the first native build. The
[V5 audit](language/whole-prover-cost-v5-audit.json)
is immutable. Its direct-chip RSS interval missed the frozen coverage gate.
That failure motivates another independent study; V5 held-out values are not
fit inputs, calibration inputs, or V6 gate adjustments.

The [V6 protocol](whole-prover-cost-v6.json) retains V5's wall and proof-byte
models, all accuracy thresholds, 26-bit PoW policy, and source/tool/host
controls. Automatic lowering selection remains disabled, including after a
possible local pass. Source, engine, compiler, and tool pins remain null in
this integrated draft, so it refuses every native phase. The isolated frozen
worktree carries committed pins and anchors.

## Training-only interval rule

V5 training-only leave-one-program-out chip residuals had a maximum
absolute-byte radius of about 485,000 bytes and a maximum radius relative to
its predicted center of about 5%. These are diagnostics, **not V6 model
parameters**. All V6 coefficients will be fitted anew using V6 training only.

For each V6 training chip program `j`, leave that whole program out, fit the
RSS point model on the other training programs, and predict its positive
center `p_j`. For its trial residuals `r_ij = measured_RSS_ij - p_j`, compute
`a_j = max(|q05(r_ij)|, |q95(r_ij)|)`. The frozen full-training point model
predicts `p` for a new program. Define:

```text
A   = max_j a_j
rho = max_j (a_j / p_j)
R(p) = max(A, rho * p)
RSS interval = [max(0, p - R(p)), p + R(p)]
```

This lets the uncertainty envelope grow with predicted chip RSS while
retaining an absolute floor. The three non-chip families keep V5's absolute
byte envelope. No held-out residual can alter `A`, `rho`, or any point fit.
The interval is empirical and has no guaranteed tail coverage.

## Fresh split and decision gate

V6 predeclares 23 training programs and 20 held-out programs, with 100 fresh
assignments per program: 4,300 native trials if admitted. Six training and
five validation programs belong to each arithmetic, direct-chip, and hash
family; fixed-width has five in each split. Different constants, assignment
index ranges, hash relation names, and fixed-width circuit names make V6
source and assignment bytes disjoint from V4 and V5. Static tests check the
disjointness and independently evaluate generated programs before native
work.

Chip training rounds are `32, 128, 512, 2048, 8192, 16384`; validation
rounds are `64, 256, 1024, 4096, 32768`. The largest held-out program tests
transfer beyond the largest training chip. Its source and assignments are
unseen by fitting. The other families preserve comparable scale variation
without changing their formulas. The current eight-word public ABI means the
i128 training case publishes quotient only and the held-out case publishes
remainder only.

The unchanged gate requires, per family, whole-process wall program-mean
p90 relative error at most 25%, wall trial interval coverage at least 80%,
and median upper-to-measured-mean ratio at most 8. Proof bytes and prover RSS
each require program-median p90 relative error at most 10% and trial coverage
at least 80%. Every held-out program additionally requires RSS trial
coverage at least 70% and upper-to-measured-median ratio at most 1.5. All
2,000 held-out trials must pass native verification, independent value
oracle, and rejected changed-public-claim control. Failure of any condition
fails the local gate.

## Freeze and run sequence

After integrating the V6 tooling, pin the exact S31 source commit, engine
gitlink, `s31.compiler_fingerprint()` SHA, sorted Python tool-path inventory,
and aggregate tool SHA in the protocol. Set status to
`frozen-before-any-v6-native-observation`, commit a V6 protocol-freeze JSON
with its full SHA and aware UTC timestamp, and record the protocol SHA plus
anchor commit in an external timestamped message **before any native build**.
The runner verifies current bytes against those pins and the committed
ancestor anchor. It requires at least 8 GiB of free artifact space.

The runner pins the Python compiler/tool inventory and engine gitlink, while
its S31 source-base check requires ancestry rather than byte equality for
every tracked Zig/build source. An independent prebuild diff of the frozen
worktree against the pinned source base found only protocol, anchor, documentation and
V6 test-file changes; no build/runtime source changed. Repeat and record that
diff plus worktree status before each timed or held-out phase, and stop the
cohort if a build/runtime source changes. This is a procedural integrity
control for V6, not a claim that the runner enforces a complete source-tree
digest.

Build and prove the 23 training packages under the pinned source. Fit the
model on that corpus only. Before any held-out build, commit a model-freeze
JSON containing full model SHA, training corpus SHA, and protocol SHA; record
the model SHA and anchor commit externally. The validation build and proof
phases require both anchors and reject any mismatch in protocol, model,
source, compiler, tool inventory, saved package build record, or generated
chip manifest. Evaluate the unchanged gate once, then publish passes or
failures with the saved artifact replay. Retain the raw evidence and do not
retune against held-out outcomes.

V6 predicts fresh-process prover-plus-verifier wall, proof bytes, and prover
peak RSS on one pinned host. Package-build wall is measured separately and
excluded from that prediction; Zig cache state is recorded but uncontrolled.
This study will not establish cross-host transfer, cached setup, or
compile-to-proof latency. Even a local pass does not enable automatic
lowering selection.
