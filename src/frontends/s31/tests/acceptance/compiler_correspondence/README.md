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

## Complete modeled direct-Gate roster on two other programs

`full_native_roster.py` checks the 1-gate direct multiplication and a 16-gate
comment-spelled program that returns gate 8 while later gates are still
computed. For each program it evaluates the generator's positional source DAG
and uses the host-side `package.direct_gate_schedule` model to construct all
512 fixed rows. That schedule is also used by the package correspondence
checker; it is separate from the Zig native emitter, but is not a second
independent host-side implementation. The diagnostic separately reconstructs
the source, input, and output row roles using the finite witness checker in
`formal/s31/scripts/check_early_return_nonvacuity.py`, which also supplies
its host-side nine-root arithmetic model. It checks that the remaining
constant/padding rows partition the physical trace; verifies every fixed cell,
all 4,608 local arithmetic roots, seed/basis/inverse values, a single coherent
address-to-QM31 value map, public copy values, and exact Gate event balance
with the native direct profile's nine public feeder uses. The checked-in
diagnostic exports are cross-checked against the earlier source-cell snapshot's
fixed-column digest and preprocessed root. Seven export/key mutations plus
one extra-feeder ledger control per program must be rejected.

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --native
zig build --build-file src/frontends/s31/build.zig test-public-physical-guard
```

`--native` builds both source-bound packages, checks each package certificate,
compares `inspect-topology` with the sealed topology and verification key,
then compares fresh `inspect-physical-rows` output byte-for-byte with the
checked-in diagnostic exports. `--native --write` is only for intentional
fixture refreshes after inspecting compiler changes. `--work PATH` retains
packages and assignments for debugging. The fresh-native path also invokes
each prover with a nonempty private assignment and requires the CLI to return
`PrivatePhysicalRowsUnavailable` before writing diagnostic rows.

The physical-row command is limited to transparent, public-only four-lane M31
programs with 1–16 add/multiply source nodes and no assertions. It exports
uncommitted fixed and main evaluations from `writeBase`. Even if a native
proof verifies, this export does not authenticate PCS openings, prove LogUp
soundness, or establish a verifier-to-trace correspondence theorem.
The Zig guard tests require rejection of a private input, a nonempty private
assignment, wrong input and output shape, assertions, constant/repeat nodes,
and a 17-node source.
