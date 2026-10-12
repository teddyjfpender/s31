# V9 fixed-call geometry transfer: frozen proof-size model fails

**The single prospective V9 stress transfer fails six of twelve gates.**
All three wall-median and wall-interval pairs pass, but the proof-size median
and interval gates fail for **every** source. This is the frozen V8 model,
unchanged, evaluated on fresh one-call sources whose circuit and chip trace
heights vary independently. V8's prior success stays valid for its tested
geometry; V9 shows that call count alone is insufficient for proof-size
forecasting across these larger traces. There was no rerun or refit.

The exact [protocol](language/mixed-cost-v9-geometry-transfer-protocol.json),
[source JSON](language/mixed-cost-v9-geometry-transfer-sources/), scripts, and
numeric predictions were committed in `6ef42ec` before any scored native
proof timing. Protocol SHA-256 is
`d7f5a0c6e6ef6600878ea1857624356906f9273c619c44ce3514bde0452707f0`.
The final compiler/runtime/model/source pin check passed. The model's fixed
one-call prediction for each source was 90.29 ms warm-wall median,
34.88–335.55 ms nominal 90% wall interval, 70,006.75-byte proof center,
and 65,898–74,115.5-byte nominal proof interval. The gates were identical
to V8's: wall median error ≤30%, wall interval coverage ≥80%, proof median
error ≤10%, proof interval coverage ≥80%, independently per source.

| Fresh source | Circuit / chip trace logs | Observed wall p50 | Wall median error | Wall interval coverage | Observed proof p50 | Proof median error | Proof interval coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `chip_sweep_n1` | 9 / 10 | 95.01 ms | 4.98% | 79/80 = 98.75% | 85,369.5 B | **18.00% fail** | **0/80 fail** |
| `gate_ladder_n1` | 10 / 4 | 97.78 ms | 7.66% | 76/80 = 95.0% | 87,355.5 B | **19.86% fail** | **0/80 fail** |
| `joint_ladder_n1` | 10 / 10 | 87.02 ms | 3.76% | 78/80 = 97.5% | 87,503.5 B | **20.00% fail** | **0/80 fail** |

Every scored proof was larger than the frozen 74,115.5-byte upper endpoint;
the smallest proofs were 80,461, 80,987, and 81,874 bytes in source order.
Relative to V8's one-call observed 70,047-byte median, these medians are
larger by 15,322.5, 17,308.5, and 17,456.5 bytes. The combined source's
increase is close to the gate-only increase rather than their sum. All
three variants lift the overall max/composition log from 9 to 10 while
leaving tree column counts and constraint counts unchanged. That shared
log-size jump is a plausible major source of proof growth; this three-source
experiment cannot isolate each serialization or FRI contribution. A future
geometry-aware model needs live log sizes and a genuinely new heldout cohort.

## Whole-process and native phase observations

All manifests matched their frozen source IDs and expected per-slot trace
logs, chip rounds, three-slot component roster, `[8,29,36,8]` tree columns,
30 constraints, 20-bit interaction PoW, 26-bit FRI PoW, and registry digest.

| Source | FRI PoW p50 | Interaction PoW p50 | Non-PoW whole-wall p50 | Build wall |
| --- | ---: | ---: | ---: | ---: |
| `chip_sweep_n1` | 60.95 ms | 1.65 ms | 29.50 ms | 73.38 s |
| `gate_ladder_n1` | 57.32 ms | 1.28 ms | 38.99 ms | 75.03 s |
| `joint_ladder_n1` | 47.99 ms | 1.44 ms | 38.48 ms | 74.81 s |

The gate-heavy sources show roughly 10 ms more non-PoW work than V8's
one-call 28.84 ms median. The chip-only source is close to that baseline.
Stochastic PoW is still the largest part of each warm proof-plus-verifier
wall observation, so the broad V8 wall model happened to pass despite the
new geometry. Passing wall gates here does not imply that the deterministic
gate-cost increment was predicted by V8. Package builds and the two
claim-zero startup observations were descriptive, never scored.

## Verification and limits

The [compact result](language/mixed-cost-v9-geometry-transfer-result.json)
SHA-256 is
`866a20af8afc41feefde1e26e6ea389fb4036117a4159d1840043cce4fa17208`.
It retains all 246 proof process pairs, source/claim/proof hashes, monotonic
endpoints, native phases, manifests, and build times. All **246 honest
proofs** verified with their typed public statements and all **246 ABI-valid
changed public results** rejected at `InvalidMixedInteractionNonce`. The
independent [audit](language/mixed-cost-v9-geometry-transfer-audit.json)
checked the saved source, binary, manifest, statement, and proof artifacts,
recomputed the frozen [score](language/mixed-cost-v9-geometry-transfer-score.json),
and replayed all proofs and changed claims in the native verifier. Score
SHA-256 is
`aeea363b5c9c77b2eb8413be29d157b641b1cc43d89b96755423e6ef9bd4b53b`.
Raw replay artifacts remain locally at
`zig-out/s31-mixed-cost-v9-geometry-transfer/`; without them, committed
hashes and scoring can be checked but these stochastic proofs cannot be
replayed.

The runner's final pin check and the native replay audit passed on the
frozen stack. Later, after the quiet timing window was released, unrelated
build-source edits made a new `protocol.py check` in the shared worktree
fail by design. Rechecking V9 requires the pinned source bytes from the
protocol; it does not change the already committed result or score.

This is one-host, one-stack evidence for three related one-call shapes.
The feasibility probes were unscored and have different source identities.
V9 does not determine a general geometry coefficient, coverage on other
profiles, or a speedup against Cairo. V9 remains a failed transfer score.
