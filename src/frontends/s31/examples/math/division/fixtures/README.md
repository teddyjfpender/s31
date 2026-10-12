# Fixed-width division measurement inputs

The five assignments for each of `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, `u64`, `i64`, `u128`, and `i128` give distinct private witnesses for
comparing `direct-gate` with `sparse-wide-gate` on the same source relation.
Each file contains the independently calculated public quotient and remainder
as little-endian `u16` patterns, except `u128` and `i128`, whose eight-word public ABI
exposes the quotient while the remainder remains constrained inside the circuit.
Signed division truncates the quotient toward zero, and
its remainder has the numerator's sign.

The corpus includes zero, maximum values, negative operands in each sign
quadrant, and the legal signed minimum divided by one. The invalid zero
divisor, `MIN / -1`, and out-of-range byte are tested separately by the
[native division gate](../../../../tests/acceptance/math/division.py).

From the repository root, run a verified profile comparison for either
`u8`, `i8`, `u16`, `i16`, `u32`, `i32`, `u64`, or `i64` by replacing `u8` in this command.
For `u128` or `i128`, use the corresponding `*_div_quotient.s31` source and
its matching valid assignment:

```sh
python3 src/frontends/s31/python/s31.py tune \
  src/frontends/s31/examples/math/division/u8_div_rem.s31 \
  src/frontends/s31/examples/math/division/fixtures/u8/*.json \
  --warmup src/frontends/s31/examples/math/division/u8_div_rem.valid.json \
  --out zig-out/s31/benchmarks/u8-division-direct-vs-wide \
  --lowering direct-gate --lowering sparse-wide-gate
```

The report checks native verification, changed-public-statement rejection,
independent value evaluation, relation identity, and visible FRI settings.
Read its median stage timings along with proof bytes and fixed cells; wall
times include process startup and variable proof-of-work search.

For the larger published corpus, the [division benchmark](../../../../benchmarks/benchmark_fixed_division.py)
retains these five boundary fixtures and adds seeded distinct witnesses:

```sh
python3 src/frontends/s31/benchmarks/benchmark_fixed_division.py u16 \
  --count 20 --seed 21264 --out zig-out/s31/benchmarks/u16-division-20
```

Replace `u16` with any of the other supported kinds. The benchmark writes the
generated assignments, complete `s31 tune` report, and a short summary.
