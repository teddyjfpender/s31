# V11 prospective unseen geometry protocol

V11 tests the V10 mixed whole-prover cost fit at four profiles it has never
seen: one-call circuit log 11, one-call chip log 11, both log 11, and two calls
with a log-11 chip. The exact source generator, independently checked claims,
frozen extrapolation, manifest guards, runner, and auditor live in
[`mixed_cost_v11_unseen_geometry`](../../../src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/README.md).

The V9 transfer of V8 failed 6/12 gates on new geometry. V10 passed 12/12
only on source instances at geometry already used in the V10 fit. V11 keeps
the V10 fit fixed and extrapolates its first measured log-size contrasts one
more step. Its prediction is a falsification target, not a claim that trace
log effects are linear or that the model is reliable. V10 scored holdout
data and the paired direct/mixed study are never fitting inputs.

The protocol requires one prospective run, 20 scored claims per source,
separate source-pinned native verification of every honest proof, an exact
ABI-valid changed-result rejection for every proof, and an independent
native audit. It reports process wall, native PoW split, proof bytes, peak
RSS, and package build wall separately. The four numeric gates are scored per
source and failures remain visible. Neither a pass nor a failure supports a
Cairo speedup claim or broad extrapolation to other chips and hosts.
