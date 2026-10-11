# Old-family mixed proof-byte gate (2026-10-11)

**Result: pass for the pinned candidate `6ab7917`.** The one-to-eight-call
old-family mixed program produced exactly the same proof length and SHA-256 at
the pre-extension baseline `96a95c6` and after the arithmetic-chip-input and
single-evaluation changes. The baseline was run twice, sequentially; its two
receipts were byte-for-byte identical. All three runs completed the native
acceptance script, including external verification and negative controls.

| Calls | Proof bytes | Proof SHA-256 |
| ---: | ---: | --- |
| 1 | 70,105 | `ddd3a36ceade6b4abaa2a84133193b7ef18a2ac8371a6a006ad259cc128e2a40` |
| 2 | 83,726 | `7eabd5d70c8e95f78f240f3ad19d9283a0acf4829f66d9a050ba46186d82b0d2` |
| 3 | 101,122 | `fcad0c86e6e48341e9742a43ba3bf283d6ef712b7143becb2e41c741edf2a799` |
| 4 | 114,672 | `190da7b798b13860d99fd5926103f07e6b4ad227047f9e6423421dd1b624c16f` |
| 5 | 131,862 | `9daa34d25e8749f3c6302dac85a7fb50ec0795313c02ee9fb6395b72d89a3a5b` |
| 6 | 141,267 | `ed2d55f425065bcaf6446f57209c50f7acbe735088ab89a4b060d5fb62b7b6ea` |
| 7 | 153,622 | `fbaf156b0f84dfda9b0d27fd615b11c27ee1e44d71791b874241cc947889397c` |
| 8 | 164,528 | `55e2eb091f296a63ab79e3d537d9d081c6465669d0ecf9425d4279d5279962c6` |

The raw [first baseline](../../../src/frontends/s31/tests/acceptance/mixed_boundary/baselines/2026-10-11/baseline-first.json),
[repeated baseline](../../../src/frontends/s31/tests/acceptance/mixed_boundary/baselines/2026-10-11/baseline-repeat.json),
[candidate](../../../src/frontends/s31/tests/acceptance/mixed_boundary/baselines/2026-10-11/candidate.json),
and [machine-readable provenance](../../../src/frontends/s31/tests/acceptance/mixed_boundary/baselines/2026-10-11/provenance.json)
are versioned together. Their three receipt file SHA-256 values are all
`34aa0d5041b91fc3b7c688baa56e1186ebb8d01e3125aedd4b89bf0064fa8c99`.
The `proof_byte_regression.py` gate reported: “old-family proof bytes unchanged
for all eight call counts”. All three stderr logs were empty.

The baseline and candidate used the same macOS 26.7.1 arm64 host, Zig 0.15.2
(binary SHA-256 `5c57faf6de2baa001be8cc3084d32ded7daf5a227ede514ca7f1161515aafa76`),
the same acceptance script (SHA-256
`898c027b5b575708bf943ad602725440b975304dbd1fd1727581bb967c0da8f6`),
`ReleaseFast`, and the same engine gitlink
`7d544c6839497ca19b6c7ef9b982e464f10cfeed`. The baseline engine checkout
was a clean, sparse detached Git worktree at that exact commit; it contained
`src`, `build_support`, `third_party`, and `vectors/circuit/official`. Every
engine path referenced directly by the S31 build file was present. The
candidate used the clean initialized engine submodule at the same commit.

This result locks the eight existing proof envelopes for this host/toolchain
and candidate commit. It does not cover newly permitted arithmetic-fed chip
inputs or establish prover soundness. Any later mixed runtime or build change
requires a fresh candidate receipt against this frozen baseline, with any
intentional byte change reviewed rather than silently refreshing the fixture.
