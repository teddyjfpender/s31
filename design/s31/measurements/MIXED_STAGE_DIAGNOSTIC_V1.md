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
Executable paths are resolved to absolute paths before hashing and execution,
so a bare filename cannot hash a cwd file while running a different file from
`PATH`.

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

## Native smoke, 2026-10-11

The post-timing-change eight-profile [proof-byte gate](OLD_FAMILY_PROOF_BYTE_GATE_2026-10-11.md)
passed at S31 `6d5edb7`: every old-family mixed proof length and SHA-256
matched the twice-repeated baseline. New ReleaseFast builds at S31 runtime
commit `51d9554` and engine `7d544c6` then proved and externally verified
one assignment each from the frozen paired-record v2 N3 and N8 held-out
sources. The only uncommitted change during those builds was regenerated
`formal/s31/proof-inventory.json`, outside the runtime/compiler source set.
The exact report, binary, source, assignment, statement, proof, and log hashes
are in the [N3](language/mixed-stage-diagnostic-v1-n3-smoke.json) and
[N8](language/mixed-stage-diagnostic-v1-n8-smoke.json) reports.

| Calls | Package timer | Opaque native prove | Prover process | External verifier process | First verified process sum | Proof bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 132.4 ms | 126.3 ms | 703.7 ms | 406.8 ms | 1,110.5 ms | 96,861 |
| 8 | 310.7 ms | 303.1 ms | 725.0 ms | 423.8 ms | 1,148.8 ms | 174,746 |

These are two **single-witness smoke tests**, not an estimator or a new
paired comparison. They validate the stage line, source/manifest/statement
binding, saved proof, and external verifier path. The opaque native call
dominates the package timer in both cases, while process overhead and native
verification are material parts of first-verified wall time. Repeated,
predeclared runs are required before fitting a mixed whole-prover cost model.
