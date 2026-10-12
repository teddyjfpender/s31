# Paired checked-addition costs

`paired.py` builds the same nominal integer source under `direct-gate` and
`sparse-wide-gate`, then runs both native provers on the same seeded assignment
corpus. The first five assignments cover zero, the upper bound, signed
minimum, one, and either a 16-bit carry or a small in-range value. Additional
assignments are deterministic random in-range pairs. The independent integer
oracle runs before proof construction; each native profile must accept every
honest proof and reject a changed public claim.

Run this only on an otherwise idle host when comparing times:

```sh
python3 src/frontends/s31/benchmarks/fixed_integer_addition/paired.py u32 \
  --count 20 --out zig-out/s31/benchmarks/fixed-add-u32
```

`summary.json` v2 records per-assignment proof bytes and prove times, medians,
native verifier and oracle controls, raw and padded geometry, visible FRI
settings, source/program/IR/assignment digests, compiler fingerprint, and a
hash of the host instance name. The raw `tune/tune-report.json`, package
manifests, trial reports, and proof files stay under the same output directory.
The runner checks that its compiler fingerprint and host identity are stable
across measurement.

Before using an archived measurement as **current local** cost evidence, run:

```sh
python3 src/frontends/s31/benchmarks/fixed_integer_addition/validate.py \
  zig-out/s31/benchmarks/fixed-add-u32
```

The gate checks the current compiler fingerprint and host/toolchain against
the paired report. It checks source and assignment hashes, package manifests,
all trial proof file hashes and byte counts, per-assignment timings, medians,
and recorded verifier/oracle controls against the raw tune report. A changed
compiler source, toolchain, or host makes the old report historical. This is
an archived-evidence consistency check: it does not replay native verification
or establish a cost prediction for another program or host. Each trial starts
a fresh prover with cold native setup; sequential profile order, host load,
cache state, and transcript-dependent proof of work can move timing medians.

For a ten-width edge-case proof-size and preprocessing comparison, capture
fresh reports from both acceptance lowerings on the same compiler revision,
then validate and combine them:

```sh
mkdir -p zig-out/s31
python3 src/frontends/s31/tests/acceptance/math/addition.py > zig-out/s31/add-sparse.json
python3 src/frontends/s31/tests/acceptance/math/addition.py --lowering direct-gate > zig-out/s31/add-direct.json
python3 src/frontends/s31/benchmarks/fixed_integer_addition/summarize.py \
  zig-out/s31/add-sparse.json zig-out/s31/add-direct.json \
  --out zig-out/s31/add-profile-summary.json
```

The summarizer refuses missing widths, mismatched canonical relations,
failed native controls, and a direct circuit containing unsupported gate
components. The matrix records one edge witness per width; use `paired.py`
for repeated distinct-witness timings.
