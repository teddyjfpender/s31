# S31

S31 is a typed circuit language and compiler for Stwo proofs. Its source,
standard and math libraries, specialized SHA and Bitcoin proving code,
examples, native verification packages, tests, and design records live here.
The proof engine and shared circuit machinery remain in
[`stwo-zig`](https://github.com/teddyjfpender/stwo-zig).

This repository preserves the original `src/frontends/s31` path so existing
source maps, commands, proof records, and documentation remain reviewable
through the extraction. The S31 source history is retained; the additional
design and editor trees were imported from the extraction source commit
`2c8d90865b00a6670d0a9bbd4fb7012c2a7716b2`.

## Getting started

Clone the pinned engine submodule and use Zig 0.15.2:

```sh
git clone --recurse-submodules https://github.com/teddyjfpender/s31.git
cd s31
cd src/frontends/s31 && zig build test -Doptimize=ReleaseSafe -j2 && cd ../../..
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py' -q
python3 src/frontends/s31/docs/check.py
```

To build and check a proof with the generated native verifier:

```sh
python3 src/frontends/s31/python/s31.py trial \
  src/frontends/s31/examples/hashes/preimage4.s31 \
  src/frontends/s31/examples/hashes/preimage4.valid.json \
  --lowering gate --out zig-out/s31/preimage-trial
```

The [language and proof documentation](src/frontends/s31/docs/README.md)
starts with handwritten examples. The [S31 package README](src/frontends/s31/README.md)
lists the compiler, prover, verifier, benchmarks, and acceptance gates. The
[design dossier](design/s31/README.md) records architecture and measurements.

## Dependency boundary

`deps/stwo-zig` is a Git submodule pinned to an exact engine commit. S31's
[`build.zig.zon`](src/frontends/s31/build.zig.zon) imports its circuit CPU
package; the build uses the same checkout for the RISC-V SHA/Poseidon provider,
postcard codec, and official circuit AIR assets. The compiler fingerprint
includes the engine commit and pinned asset hashes. Local modifications to the
engine submodule are rejected when building canonical S31 packages.

Update the engine deliberately: advance the submodule, run the Zig and Python
tests, documentation check, library MVP acceptance, native proof acceptance,
and inspect source/key/proof identity changes before committing the new pin.
No proving engine source is copied into S31.

The `src/core`, `src/frontends/circuit`, `src/frontends/riscv`, `formal/riscv-refinement`,
and `vectors` symlinks are read-only paths into that pinned submodule. They keep
the reviewed source names in formal inventories and older record tooling stable;
the Zig build imports the dependency directly.

S31 proof blinding, private witness handling, and recursive verification have
profile-specific limits. Read the corresponding docs before interpreting a
proof as confidential or deploying an application.
