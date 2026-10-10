# Whole-prover cost model V6: prospective chip RSS transfer

**Status: prospective native run complete; the predeclared local accuracy
gate passed. Automatic lowering remains disabled.** The
[V5 audit](language/whole-prover-cost-v5-audit.json)
is immutable. Its direct-chip RSS interval missed the frozen coverage gate.
That failure motivates another independent study; V5 held-out values are not
fit inputs, calibration inputs, or V6 gate adjustments.

The [V6 protocol](whole-prover-cost-v6.json) retains V5's wall and proof-byte
models, all accuracy thresholds, 26-bit PoW policy, and source/tool/host
controls. Automatic lowering selection remains disabled, including after a
possible local pass. Source, engine, compiler, and tool bytes are pinned in
the protocol; native work still requires a committed freeze anchor and its
externally timestamped full SHA.

## Measured result

The [pinned V6 audit](language/whole-prover-cost-v6-audit.json) records 23
fresh training packages and 20 source- and assignment-disjoint held-out
packages on one Apple M5 Max host. All 2,300 training and 2,000 held-out
native proofs were accepted. Each trial's changed-public-claim control
rejected, its independent value oracle passed, and the publisher matched
all saved proof, full trial report, assignment, source, package, and direct-chip
manifest digests. The publisher replayed the frozen fit and evaluation. It
did not rerun native verification or independent oracles.

| Family | Wall p90 error / coverage | Proof bytes p90 error / coverage | Prover RSS p90 error / coverage |
| --- | ---: | ---: | ---: |
| Arithmetic | 13.58% / 88.0% | 4.99% / 99.8% | 2.57% / 98.6% |
| Direct chip | 11.19% / 89.0% | 4.73% / 96.0% | 3.00% / 100% |
| Fixed width | 13.78% / 86.2% | 2.59% / 99.8% | 8.67% / 100% |
| Hash | 3.00% / 86.8% | 0.17% / 96.6% | 0.032% / 99.0% |

These are per-family p90 relative errors across program point estimates and
trial interval coverage. The gate requires wall p90 error at most 25%, wall
coverage at least 80%, proof-byte and RSS p90 errors at most 10%, and their
coverage at least 80%. Each held-out program also needs RSS coverage at
least 70% and interval upper bound at most 1.5 times its measured median.
The weakest RSS program covered 93/100 trials (`arithmetic_1280`); the
largest RSS upper-to-median ratio was 1.453 (`signed_quotient_32`). The
largest wall point error was 16.42% (`signed_quotient_64`), proof-byte point
error 6.14% (`chip_32768`), and RSS point error 9.09%
(`signed_remainder_128`). The result passes this local gate, with empirical
intervals that do not guarantee future tail coverage.

The exact measured source base is S31 commit
`1b04f77c87e650cd4cc24727b23d2b3d1d5718b6`, with stwo-zig engine
gitlink `fb300ed1bcfac3299f249928fdfe18f4345deae6`. The compiler digest
is `cf31fcb1b1b6c90bc1be1b363c778a6afdf370eba851f841cf4939f268aa6782`
and the measurement-tool digest is
`3762036a89536935231fbfe57a351172e1c835d8e2fcb226e5e1a6fa130f0079`.
The frozen protocol SHA-256 is
`c839427e3651a92f07710e5fc446cfa8fb022fbe4f70245d8fa22ec01c5c5b14`,
anchored by commit `b3191bd5d9c0b7a2afc71b440e9c2e636ef1d2af` before
the first native build. The frozen model SHA-256 is
`0f0d4356123fa6ee85e1653c4224a9abbfaf8ec011037a5aa1c47ec374876b7c`,
anchored by commit `22223af1ea5a0486ce7bcebfb66bc064cafab233` before
the first held-out build. Both full hashes and commits were separately
timestamped in the parent task conversation before those phases.
The saved training corpus, validation corpus, and evaluation have SHA-256
digests `bad7cbcd5d27f9546c2a2edad1ccdb28e8fec498f17df40e7637424b9a62a59d`,
`02bf8f9f47c8b2f548d47c0243dc7b5059c2ed5ec60a36bc3da2efe96e23e903`,
and `e51e1d332282a6d2c9b492841f445814e8f8d1fde9dfcddda18af87122310909`,
respectively. The pinned audit file hashes to
`05bac7095a4b1f82a20c52898410f7cd886020a8a4e78c26e1f768e37b2e5b01`.

The target is fresh-process prover-plus-verifier wall time, proof bytes, and
prover peak RSS on this one host and compiler revision. Package-build wall
time was measured separately for every package, with uncontrolled Zig cache,
and is excluded from the wall predictor. The 26-bit PoW policy adds variance;
the wall intervals remain broad, especially for the direct-chip family.
This check does not establish cross-host transfer, cached setup, or
compile-to-proof latency. Automatic lowering remains disabled.

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
