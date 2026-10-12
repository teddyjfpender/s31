# Current fixed-integer whole-process evidence

`paired_tune.py` builds the two native lowerings once, warms each with an
unmeasured separate process, then proves each distinct assignment under both
profiles. The order alternates by assignment: direct then sparse for even
indices, sparse then direct for odd indices. This balances a simple order
effect while keeping identical statements and visible FRI settings. Each
measured proof still starts a fresh prover process and builds its own native
setup. Package build is recorded separately and is not part of the paired
proof latency.

The checked-addition and checked-multiplication runners call `evidence.py`
after producing their reports. To inspect one saved run again:

```sh
python3 src/frontends/s31/benchmarks/fixed_integer_cost/evidence.py \
  zig-out/s31/benchmarks/fixed-add-u32-n20
```

The gate requires the current compiler fingerprint, current host instance and
toolchain, exact source text and assignment hashes, identical program and
canonical relation hashes, sealed package manifest identities, the balanced
schedule, matching visible FRI settings, proof file hashes and sizes, honest
native acceptance, changed-claim rejection, and independent value-oracle
results. It checks the saved public statement and every trial's native stage
timers against process wall. It checks the raw tune medians and observed-cost
summaries by recomputing them from saved trials. Multiplication additionally
requires the runner's recorded native overflow rejection. The gate does not
rerun the native verifier; the original trial and prover controls remain in
`tune/` for replay.

The gate also revalidates sealed package artifacts and matches the cost-report
geometry, visible FRI settings, and public ABI to the saved profile. It
reconstructs the exact one-word changed public statement and checks that the
trial names that changed word. The schedule matches the runner's alternating
order, but saved trials have no independent timestamp or order witness; an
offline check cannot prove the processes actually ran in that order.

For each assignment, whole-process wall is measured prover-process wall plus
measured native-verifier-process wall. The prover side is accounted as:

```text
witness + cold setup + proving excluding PoW + interaction PoW + FRI PoW
  + other native runtime + process residual
```

The process residual is measured prover wall minus the native runtime total.
It includes startup, allocation and the resource-meter wrapper. The native
timers print six decimal places, so small rounding differences are accepted.
The output gives medians per component, but component medians need not sum to
the median of per-assignment whole-process totals. Proof bytes, padded rows,
and preprocessed cells are reported separately. RSS is available in the raw
trial and tune reports; process peaks cannot be added across prover and
verifier as a whole-process memory number.

This is a one-host, one-source, one-compiler observation. Alternation does not
remove host load, OS cache, thermal changes, or transcript-dependent PoW.
Twenty distinct witnesses are the default; five is a smoke check. It is not
an unseen-program predictor or a claim that different AIRs have equal
soundness. The older V8r1 held-out whole-prover model remains historical for
its pinned compiler and host until a new prospective corpus is measured.
With an odd witness count, one profile necessarily runs first once more than
the other. For short runs, FRI proof-of-work variance can dominate wall time;
inspect paired samples and stage times before drawing a speed conclusion.

## Prospective current-compiler protocol

`prospective.py` is a separate, small training/calibration/holdout protocol.
Its [design brief](../../../../../design/s31/measurements/language/FIXED_INTEGER_PROSPECTIVE_COST_V1.md)
sets the split, stage equation, uncertainty bands, score thresholds, and
limits. It does not reuse historical V8r1 timing to fit this compiler.

Run on an otherwise quiet host. Keep the generated directory and pin the
plan and model hashes in commits or an external timestamp before advancing
to the next phase:

```sh
study=zig-out/s31/benchmarks/fixed-integer-prospective-v1
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py plan "$study"
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py validate "$study"
# Freeze plan.sha256 before the first native build.
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py collect-training "$study"
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py fit "$study"
# Freeze model.sha256 before any u128 build or proof.
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py collect-holdout "$study"
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py score "$study"
python3 src/frontends/s31/benchmarks/fixed_integer_cost/prospective.py validate "$study"
```

The native-free preflight is `python3 -m unittest discover -s
src/frontends/s31/benchmarks/fixed_integer_cost -p 'test_prospective.py'`.
`collect-training` verifies and skips a complete prior case on restart; it
stops on an incomplete or inconsistent case and preserves that evidence.
The `score.json` has four u128 profiles, not an unseen cross-program or
cross-host reliability claim. It is valid only with the sealed plan/model
and exact saved native proof artifacts.
