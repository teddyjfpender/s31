# Mixed-general prover stage diagnostic v1

The anchored [paired record v2 study](PAIRED_RECORD_V2_RESULT.md) found no
whole-workflow mixed speedup on its pinned 1–8-call relation family. This
diagnostic was added **after** that study. It does not revise its frozen
protocol, binaries, raw ledgers, analysis, or reported ratios. Run it on new
proofs to locate where time is spent before changing the lowering.

The source-embedded `direct-mixed-general` prover now emits one JSON line on
stderr, prefixed `S31_MIXED_STAGE_V1 `. It is emitted only after the proof
and statement files are written. The line names the source hash, typed
registry manifest hash, circuit identity, byte lengths, and seven monotonic
package intervals in nanoseconds. Six disjoint intervals add exactly to
`package_total_ns`:

| Field | Measured work |
| --- | --- |
| `profile_rebuild_ns` | Inspect source and official AIR; select the registered live component schedule. |
| `semantic_evaluation_ns` | Parse and evaluate the source against the assignment, then canonicalize expected public words. |
| `topology_compile_ns` | Compile the source topology used by the witness compiler. |
| `witness_compile_ns` | Compile the assigned circuit and its witness values. |
| `native_prove_including_setup_ns` | The complete engine `proveSourceBound` call, including its setup, preprocessing, witness commitment, interaction, FRI, and PoW work. |
| `envelope_and_serialization_ns` | Check native proof identity/public outputs and serialize the bounded mixed envelope. |

The Zig timer starts inside `proveSealedAndInspect`. CLI source parsing,
assignment parsing, public claim projection, record statement validation,
process startup, and file writes in the CLI are outside `package_total_ns`.
The difference between the measured prover process wall and that package
timer includes those operations, scheduling, teardown, and timer overhead.
It is **not** a measured setup stage. The native engine currently does not
expose a separate setup/preprocessing or PoW timer on this path, so the
diagnostic reports `engine_setup_preprocessing_ns` and `engine_pow_ns` as
`null`, never zero. The corresponding generic direct-gate stage labels are
not directly comparable to the mixed native opaque interval.

For a record ABI v2 assignment, run the separate diagnostic collector with
the three executables from the **same** source-embedded mixed build:

```sh
python3 src/frontends/s31/benchmarks/paired_record_v2/diagnose_stages_v1.py \
  --prover /path/to/bin/s31-NAME-mixed-general-prover \
  --verifier /path/to/bin/s31-NAME-mixed-general-native-verifier \
  --inspector /path/to/bin/s31-NAME-mixed-general-manifest \
  --assignment /path/to/assignment.json \
  --typed-statement /path/to/typed-statement.json \
  --out /path/to/new-diagnostic-directory
```

The collector measures complete prover and external native verifier process
wall times with the host monotonic clock. It accepts a report only after the
verifier exits successfully, the prover copied the canonical typed statement
exactly, the stage line matches the inspector's source/registry/circuit
identity, all stage intervals partition the package timer, and the named
executables have unchanged SHA-256 digests across the run. The report binds
assignment, statement, proof, binaries, and raw logs by SHA-256. Its
`first_verified_process_wall_ns` is the sum of the two process wall times;
it excludes the Python gap between processes, just like the paired study.

The source-embedded native verifier and its underlying proof-system review
remain the authority for proof acceptance. The collector checks the chosen
executable's exit status; it cannot prove that an arbitrary path supplied as
`--verifier` contains a correct verifier. Inspect the recorded binary hashes
against the intended build. These timings are diagnostic observations, not
new prospective comparative evidence or a speedup claim. The stage line is
ordinary stderr and is outside the proof transcript and serialized proof.

To split the opaque native call later, add an optional, write-only timing
observer to the engine's
`deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig`
`proveSourceBound` path. Measure preprocessed circuit construction and fixed
commitment before `direct_trace.writeBase`; main trace generation/commitment,
interaction trace/commitment and interaction grind; and the final
`Engine.prove` call, which owns STARK quotient/FRI work and FRI PoW. Record
unclassified residual time instead of attributing it to a stage by
subtraction. Require the same source-bound proof identity and external native
verification, and check transcript/proof-byte parity under controlled
deterministic inputs before using those finer timers in a model.

Static checks: `python3 -B
src/frontends/s31/benchmarks/paired_record_v2/test_diagnose_stages_v1.py`.
A native source-bound smoke test and proof-byte compatibility run remain
required before treating the new Zig timing code as validated.
