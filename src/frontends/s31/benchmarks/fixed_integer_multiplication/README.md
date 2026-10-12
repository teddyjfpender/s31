# Paired checked-multiplication costs

`paired.py` compiles one `std::int::mul_checked` `.s31` circuit under
`direct-gate` and `sparse-wide-gate`. Both native provers receive the **same
20 distinct seeded assignments** by default, in the same order. These cover
zero, one, the integer bounds, a product near the bound, and a cross-limb
product where the width permits; the remaining pairs are deterministic
in-range samples. The script
checks the full integer product and an independent relation oracle before any
proof run. Both profiles must accept every proof, reject a changed public
claim, pass the trial value oracle, and reject a checked-overflow witness.

Run on an otherwise idle host for meaningful timing comparison:

```sh
python3 src/frontends/s31/benchmarks/fixed_integer_multiplication/paired.py u32 \
  --count 20 --out zig-out/s31/benchmarks/fixed-mul-u32
```

For a fast source, corpus, and oracle check without building a native package:

```sh
python3 src/frontends/s31/benchmarks/fixed_integer_multiplication/paired.py u8 \
  --count 20 --prepare-only --out zig-out/s31/benchmarks/fixed-mul-u8-plan
```

The minimum count is five, suitable for a native smoke run. A report with
fewer than 20 witnesses is a smoke result, not the default 20-witness
benchmark. `summary.json` contains source, normalized program, canonical IR,
compiler, and assignment digests; each profile's raw/padded geometry,
preprocessing cells, visible FRI settings, per-assignment proof bytes and
prove times, median prove/verify times, and all verifier/oracle controls.
The complete per-trial reports and proofs are under `tune/`.

`direct_over_sparse_*_ratio` is a descriptive local ratio. Every measured
process performs cold native setup. Profiles run sequentially, so host load,
thermal state, process startup, OS cache, and transcript-dependent proof of
work may affect timings. Matching visible FRI settings does not establish
equal soundness across different AIRs. A run on one source and one host does
not establish a general speedup or whole-prover cost model.
