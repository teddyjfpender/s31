# Generated source to native proof samples

`generated_native_subset.py` selects four sources from the pinned 384-source
mutation corpus: one gate; eight alias-spelled gates with an earlier return;
fifteen gates with a final return; and sixteen comment-spelled gates with an
earlier return. It evaluates the generator's positional DAG independently of
both S31 parsers, compares every generated instruction (including eager dead
ones) to the certificate and package, builds each source through the production
direct-Gate path, proves the computed claim, verifies it natively, and requires
rejection of a changed public word.

The fast `--static` path also requires rejection of ten changes to the
generator's operations, returned gate, or eager dead suffix. It checks the
production parser against the independently enumerated positional instructions
before starting a native build.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/generated_native_subset.py --static
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/generated_native_subset.py
```

Use `--work PATH` to retain packages, proofs and trial reports for inspection.
The full corpus remains a fast parser, normalizer and exact-schedule comparison
in `tests/python/generated/test_source_mutation_correspondence.py`. These
samples test the native path; they do not prove parser or emitter refinement in
Lean, nor the underlying PCS/FRI soundness assumptions.

## Pinned square4 fixed-root binding

`native_fixed_root_binding.py` checks the complete 512-row, eight-column
direct-Gate fixed roster against the binary native fixture, the physical-row
report, and Lean's `PinnedFullFixedRoster` literal. It also checks that all 512
address-indexed output values in `PinnedSquare4ConstantValues` agree with the
physical main rows, and that the Lean main witness names the pinned native
preprocessed root. Four one-cell/root controls must fail.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py --native
```

The second command builds a fresh source-bound native package in a temporary
directory. It rechecks the package's exported fixed cells and key root against
the pinned fixture, proves the square4 claim, verifies it with the generated
native verifier, changes one byte in the proof's serialized preprocessed root,
and requires `InvalidPreprocessedRoot` from that verifier. The comparison and
mutation are reproducible diagnostics. They do not independently recompute the
Blake2s PCS root from circle evaluations or prove that all authenticated proof
openings equal the uncommitted physical-row export.
