# V6 whole-prover model transfer to the current S31 stack

**Result: the V6 wall model does not pass the predeclared same-host transfer
diagnostic.** Automatic lowering remains disabled. This is a diagnostic of a
changed S31 compiler **and** engine together; it does not identify which
revision caused the difference. It also does not establish cross-host or tail
accuracy.

The [frozen transfer protocol](language/whole-prover-transfer-v1.json) was
committed as `5fbf2fc` before the first native build. It pins the V6 audit,
current compiler and engine, host, eight generated source digests, 80
assignment digests, and accuracy thresholds. The current compiler fingerprint
is `aea630bacf2dba03f384df13ee8fdd4214cb11d9665bf557750efeda6af2cf71`;
the engine is `844f8ddf10291733b845e81a8f20026e829fc509`. The source and
assignment digests have zero overlap with the saved V6 training and validation
inventories. Some hash and fixed-width programs retain V6 validation *shapes*
under new names, so this checks cross-revision behavior, not eight unseen
semantic shapes.

The [first corpus](language/transfer-v1/first-corpus.json) and
[first audit](language/transfer-v1/first-audit.json) record 80
fresh proofs. A second fresh build and proof run used the same protocol and
assignments in a different output directory to examine host-load sensitivity;
its [corpus](language/transfer-v1/repeat-corpus.json) and
[audit](language/transfer-v1/repeat-audit.json) are also pinned.
Both runs accepted all 80 honest proofs, rejected every changed public claim,
and passed the independent value oracle on every trial. The repeated programs
and assignments make the second run a sensitivity check, **not** an independent
held-out split.

| Family | First wall: max point error / trial coverage | Repeat wall: max point error / trial coverage | Proof bytes and RSS |
| --- | ---: | ---: | --- |
| Arithmetic | 52.0% / 65% | 47.7% / 70% | Both pass both runs |
| Direct chip | 40.9% / 80% | 38.4% / 75% | Both pass both runs |
| Fixed width | 45.1% / 85% | 32.4% / 90% | Both pass both runs |
| Hash | 13.9% / 80% | 9.1% / 35% | Both pass both runs |

The diagnostic required each program's wall point error to be at most 25%
and pooled family wall interval coverage to be at least 70%; proof bytes and
prover peak RSS each needed at most 10% point error and 80% coverage. The
first run fails three families' wall point gates; the repeat fails the same
three and the hash interval coverage gate. The predeclared result is therefore
**fail** in both runs. The 10 trials per program are too few to infer a stable
tail probability, especially with 26-bit proof of work.

The stage breakdown shows a systematic fresh-process difference. Relative to
V6 predictions, native verifier process wall was roughly 28–36 ms higher per
trial and prover-process unattributed time roughly 32–77 ms higher across the
eight programs. Proof-of-work timing also moved, sometimes in opposite
directions between runs. Several local builds ran concurrently with the first
measurement; the repeat avoided other heavy local builds but did not isolate
the CPU or control OS scheduling. The unchanged overhead in the repeat is a
reason to investigate process startup and runtime changes, not a basis to
refit V6 coefficients on these validation observations.

The [stage diagnostic](../../../src/frontends/s31/benchmarks/cost/diagnose_transfer_stages.py)
recomputes those residuals from the saved corpora. Across the eight programs,
the first/repeat median verifier-process residuals are **+33.2/+33.7 ms** and
the median prover-process unattributed residuals are **+46.7/+48.7 ms**.
The measured FRI PoW residual changes sign across program sizes and runs;
the common process overhead is the more consistent signal. These medians
describe only the observed corpus and are not fitted correction constants.

## Evidence limits and next gate

Independent review found that the V1 tool digest omits the imported affine
RSS predictor and the two Python oracle files. The current files were not
changed during these runs, but the protocol does not itself enforce that
fact. The local commit preceded the native builds, yet its full hash was not
externally timestamped before observation. The runner checks trials as they
are produced; a separate saved-artifact replay is required to establish that
the copied corpus still matches proof, statement, assignment and package
files. These limits prevent this run from being called a fully frozen release
acceptance gate. They do not turn its failed wall diagnostic into a pass.

The next cost study should pin all transitive predictor and oracle sources,
externally anchor its freeze before native work, replay saved artifacts, and
separate process startup from proof work. It needs source- and
assignment-disjoint training and validation on the new stack, enough fresh
trials to characterize proof-of-work variance, and a predeclared gate before
automatic lowering can be considered.

The separate [read-only replay tool](../../../src/frontends/s31/benchmarks/cost/replay_transfer_v1.py)
now checks both saved corpora. Its native mode reopened all 160 saved proof
artifacts, accepted each original statement, rejected each changed statement,
reran the value oracle, and reproduced both failed diagnostics. It also
checked the omitted predictor and oracle source files retrospectively against
the freeze commit. That closes an artifact-integrity question for these local
files; it does not retroactively add the missing protocol pins or the missing
external pre-observation timestamp.
