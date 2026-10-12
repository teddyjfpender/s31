# Checked gate sharing

`functional.s31` spells `a + b` twice, once in reverse order as `b + a`,
then uses **both** results in `e = c + d`. The direct-gate optimizer sorts
commutative operands and reuses the earlier gate. Its five source lets
therefore lower to the same four arithmetic gates as `manual.s31`. The
independent v3 correspondence checker verifies
the source, normalized relation, native gate topology and fixed root.

For each input lane, `e = 4x + 2x²` in M31. The acceptance test builds both
packages, compares their AIR geometry, checks the v3 certificate, and proves
and verifies `[0, 6, 16, 126]` for input `[0, 1, 2, 7]`.

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/functional/release_optimized4/functional.s31 \
  --out zig-out/s31/reverse-share --lowering direct-gate \
  --correspondence optimized
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/optimized_release.py
```

The optimization is an explicit build choice. The default conservative
certificate does not admit this source. The certificate and native test do
not constitute a proof of the entire Python compiler or the PCS/FRI system.
The [Lean byte and AIR example](../../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/LiveOptimizedRelease.md)
checks this exact source, its generated relation and compact circuit bytes,
then states the conditional modeled AIR claim for arbitrary satisfying rows.
