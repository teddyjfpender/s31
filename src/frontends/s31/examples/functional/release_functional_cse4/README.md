# Repeated pure calls share one circuit

`double`, `square`, and `mix` are pure source functions. `mix(x)` is called
twice; both results feed `e`. Specialization emits seven named arithmetic
nodes into the normalized relation: three for each call and one final add.
The explicit v3 correspondence checker independently reconstructs that
relation, checks the native gate topology, and verifies canonical sharing:

| Source step | Source nodes | Compact circuit gates |
| --- | ---: | ---: |
| First `mix(x)` | 3 | 3 |
| Second `mix(x)` | 3 | 0 new gates |
| `e = c + d` | 1 | 1 |
| **Total** | **7** | **4** |

The compiled AIR has the same geometry as `manual.s31`, which writes the
four gates directly. For each M31 lane, `e = 4x + 2x²`; input
`[0, 1, 2, 7]` gives `[0, 6, 16, 126]`.

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/functional/release_functional_cse4/functional.s31 \
  --out zig-out/s31/repeat-mix --lowering direct-gate \
  --correspondence optimized
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/functional_optimized_release.py
```

The v3 certificate is opt-in and currently bounded to the public four-lane
direct-gate fragment. The native regression checks this program, not every
possible helper body or the cryptographic soundness of PCS/FRI.
