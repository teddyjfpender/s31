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
