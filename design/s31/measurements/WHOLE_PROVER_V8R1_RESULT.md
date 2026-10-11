# V8r1 whole-prover cost study: qualified local result

The V8r1 frozen held-out evaluator failed before scoring: its inherited V3
name check expected `signed_quotient_{8,16,32,64}`, while the committed V8r1
inventory and measured cases used `signed_div_rem_{8,16,32,64}`. The original
failure is preserved in
[`whole-prover-cost-v8r1-eval-failure.json`](language/whole-prover-cost-v8r1-eval-failure.json).
An independently reviewed, versioned [roster-only bridge](../../../scripts/s31_v8r1_postfreeze_roster.py)
changes only the temporary V3 checker view for those four names. It preserves
the original case objects, prediction code, model, thresholds, and raw trials.
Consequently, the result below is **post-freeze evaluator repaired**, not an
unqualified prospective pass. No held-out observation was used to tune the
model or gate.

## Freeze chronology and scope

| Item | Exact identity |
| --- | --- |
| Frozen protocol SHA-256 | `d974d97db448e8bfbe759a57eb9f8b4e580a5a75b0d158b7572f0cd60ca3388d` |
| Protocol anchor commit | `088312c3e3b084075e3aa475da3cf445d1f4d916` |
| Protocol external timestamp | 2026-10-11 06:49:28 UTC, before native training |
| Training-only model SHA-256 | `4edadc85032dbfafd191dad838cfa5083bc7c54a509e7cdf22cc9fbb6561fc87` |
| Model anchor commit | `3e11e36a7fffb548135765423df823c35bd904d6` |
| Model external timestamp | 2026-10-11 07:27:09 UTC, before held-out builds |
| Compiler fingerprint | `12bea28f0983fd0b9ca070a81e05af96607eb88b51af5780347f9e4ed47b9425` |
| Engine gitlink | `7d544c6839497ca19b6c7ef9b982e464f10cfeed` |

The local study used an Apple M5 Max on macOS 26.7.1, Zig 0.15.2 and Python
3.14.6. Training and validation had disjoint source and assignment hashes:
23 training packages with 2,300 native proof/verifier trials and 20 held-out
packages with 2,000 trials. Each split had 100 trials per program. The
training corpus SHA-256 is
`9b2c539a3815937fd63167e35cd3b533add2bc9e3303bfd08750a3e58eb02982`;
the held-out corpus SHA-256 is
`6ea0cd38953a1b1fa7b86fdcc21bf16bd15aace52804098dd2b42738c4726c43`.
The failed V8 evidence was excluded from V8r1 fitting and calibration.

## Held-out gates

The repaired evaluator and the separate second-source gate checker agree:
`local_accuracy_gate_pass=true` for all four families. All 20 per-program
process-stage gates passed. The independent checker recomputed every target
prediction and gate from 2,000 raw held-out trials. Values below are measured
held-out family statistics; p90 error is the p90 of program relative errors,
and coverage is the fraction of trials inside the frozen intervals.

| Family | Wall p90 error | Wall coverage | Proof-size p90 error | Proof-size coverage | RSS p90 error | RSS coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Arithmetic | 10.55% | 89.6% | 5.12% | 100% | 2.94% | 100% |
| Chip | 6.63% | 90.8% | 3.45% | 100% | 3.70% | 100% |
| Fixed width | 13.25% | 88.2% | 2.98% | 100% | 8.59% | 100% |
| Hash | 3.44% | 92.8% | 0.21% | 93.2% | 0.04% | 100% |

The frozen limits included at least 80% family trial coverage, at most 25%
wall p90 program error, at most 10% proof-size and RSS p90 program error,
and per-program process-stage and RSS gates. The 2 MiB RSS uncertainty floor
was declared before training. Automatic lowering selection stayed disabled.
These gates establish local predictive accuracy for the pinned programs and
host; they do not establish cross-host transfer or source-to-circuit soundness.

## Native and portable evidence

The publisher was run with both `--native --require-pass`. It refit from the
saved training corpus, checked the saved held-out evaluation with the
independent gate implementation, and checked 4,300 assignments, statements,
value oracles, and original/changed public-claim native replay sets. It
reported 23 training and 20 held-out packages, and passed. The audit SHA-256
is `02995df1aa4dc753fef11a3b06d7e71e463ab8fddf4e7e8dc3df7c9c8e4a649f`.

A content-addressed manifest was then created over the original evidence and
its full SHA-256
`c2adc1ad69808d76953c1095c3d2b602801a64215febba5efd9bc3f324780178`
was externally recorded at 2026-10-11 08:07:22 UTC before relocation. A
single copy at a distinct path passed portable replay with both
`--native --require-pass`: 30,598 files, 4,300 proofs and assignments, 4,300
value-oracle controls, and 8,600 native original/changed claim controls.
The second-source held-out gate again passed.

| Artifact | SHA-256 |
| --- | --- |
| Repaired evaluation | `aff249527d97355bf5539c4daaaf80b8a9abcc8e41fbeecf9b98c015e6693c8b` |
| Evaluation repair provenance | `b42feb22cbf9d4beb3ac6912054f821320c2d532a90da90a8a3c4a3282cd4372` |
| Publisher repair provenance | `b4642535e3549c6d2ea16b88cc8f21c829b82dc9735971e68cf4c2c0f99d4daa` |
| Portable replay repair provenance | `836b38449573fba934088170d2a769e41254b52b7eb034e953e5c4a1bf9fb65a` |

Original raw evidence remains under `zig-out/s31-v8r1-evidence` in the
isolated measurement worktree. The distinct-path replay used a temporary
copy at `zig-out/s31-v8r1-portable-relocated`; that copy was removed after
the passing replay and externally recorded manifest hash to restore disk
headroom. The wrapper provenance files remain under
`zig-out/s31-v8r1-postfreeze`. These paths are ignored local evidence, not
repository artifacts. The frozen protocol and model remain byte-identical.
