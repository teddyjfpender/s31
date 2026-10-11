# Square4 native fixed root and Lean fixture binding

## Checked chain

The direct-Gate compiler lowers `functional_square4_manual.s31` to 512 physical
Gate rows. The native `inspect-topology` command exports eight fixed columns
from its constructed `PreprocessedCircuit`; the package carries their SHA-256
digests in its generated component manifest and the corresponding preprocessed
PCS root in the source-bound verification key. `fixed_columns.native_fixture`
checks source bytes, source instruction schedule, column order, all 4,096
canonical M31 cells, manifest digests, and equality of the topology, component
manifest, and key roots.

`native_fixed_root_binding.py` adds the cross-artifact checks that were missing
from that chain:

1. Every cell in the native binary fixture equals the physical report and the
   512×8 Lean literal used by `PinnedFullFixedRoster`.
2. The physical output addresses are exactly a permutation of 0..511. Each
   address-indexed four-limb output equals the Lean
   `PinnedSquare4ConstantValues.nativeValues` literal. The literal's source
   SHA-256 matches the complete physical report.
3. The Lean main-witness fixture's `preprocessedRoot` string equals the native
   fixed-column fixture root. Four altered fixed/value/root artifacts are
   rejected by the static checker.
4. With `--native`, a fresh compiler build must reproduce the fixture. Its
   generated native verifier accepts a real square4 proof. The checker locates
   the unique serialized preprocessed root after the direct-Gate proof header,
   changes exactly one root byte, and requires `InvalidPreprocessedRoot` from
   the same verifier and statement.

Run the short static check first, then the native check:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py --native
```

On 2026-10-12 the static check matched 4,096 fixed cells and 512
address-indexed values, and rejected four altered artifacts. The fresh native
check produced and accepted a 54,831-byte proof. The pinned root was
`c0ea49c8f9027d5bdf9ce7a59ded3fb3a1f6b541a0ed1bb6c65b3c7d1175570a`;
its unique serialized occurrence began at byte 39. A one-byte change there
returned exactly `InvalidPreprocessedRoot` from the generated verifier.

The native root mutation exercises the actual verifier branch at
`src/frontends/s31/runtime/native_verifier.zig` where decoded commitment zero
is compared with the root reconstructed from its sealed source/key. The root
has 32 bytes; the mutation preserves the proof length, envelope, interaction
claim, other commitments, public statement, and verification key.

## Exact limit

The fixed roster and physical report are uncommitted diagnostic exports. The
Lean fixed-row/value theorems are about those pinned literals. This evidence
links those literals to the native package's root and demonstrates that the
native verifier rejects another root. It is **not** a Lean proof that the
native PCS verifier authenticates every queried opening or that the committed
main/interaction trace equals the exported diagnostic trace. Completing that
step requires a refinement theorem for the native PCS opening/FRI verifier and
the generated direct-Gate AIR evaluator, or an independently checked proof
object establishing those premises.
