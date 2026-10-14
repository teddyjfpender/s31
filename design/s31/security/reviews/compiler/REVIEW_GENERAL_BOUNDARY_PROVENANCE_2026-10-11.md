# Independent provenance review: bounded mixed circuit-to-chip boundary

Reviewed S31 commit `29a9ebc` and the pinned `deps/stwo-zig` engine at
`7d544c6839497ca19b6c7ef9b982e464f10cfeed`. This is a static review of
the experimental `direct-mixed-general` source-embedded proof path for one to
eight square/add-constant calls. I read the admission, compiler, endpoint,
manifest, bridge, chip, envelope, and verifier paths. I did not run a native
build or proof in this review. No concrete false-public-statement admission,
source/proof substitution, or unbounded proof decode was found in those paths.

## What is authenticated

1. [`bounded_call_admission.zig`](../../../../../src/frontends/s31/language/bounded_call_admission.zig)
   accepts only one to eight live, distinct canonical repeat nodes with a
   four-lane M31 predecessor and `square; add_const` body. The predecessor
   may be an input, previous chip result, or a permitted arithmetic/select
   node. The source limit is 1 MiB; canonical IR is limited to 65,536 nodes;
   total chip rounds are limited to 262,144. The ordinary relation validator
   limits the entire public statement to eight M31 words.
2. [`relation_compiler.zig`](../../../../../src/frontends/s31/language/relation_compiler.zig)
   compiles the same canonical IR in witness-free and value-carrying modes.
   For an arithmetic-produced chip input, it unpacks the packed QM31 result
   into four constrained scalar Gate producers once at the source node.
   Repeated uses of that source share those four addresses. Each chip result
   gets four newly guessed, M31-constrained scalar output producers.
   [`bounded_compiled_binding.zig`](../../../../../src/frontends/s31/runtime/bounded_compiled_binding.zig)
   checks source IDs, call order, exact endpoint addresses, row count,
   variable count, unique producers, and the preprocessed fixed root against
   separately compiled topology and witness circuits. The mixed projection
   [`inspection.zig`](../../../../../src/frontends/s31/runtime/mixed_boundary/inspection.zig)
   additionally rejects an output address repeated within a call or aliased
   to that call's input; input aliases and a later call's use of an earlier
   output remain valid.
3. The engine's [`direct_arithmetic.zig`](../../../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig)
   adds one Gate use for **each endpoint occurrence** before committing the
   eight fixed columns. This includes a fork where two calls consume the same
   arithmetic result. The [`tagged_pair_bridge.zig`](../../../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig)
   and [`tagged_many_bridge.zig`](../../../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig)
   AIRs constrain their eight endpoint values constant across bridge rows,
   consume the matching Gate tuples, and connect tagged chip step zero and
   final-step tuples. The chip AIR constrains `next = current² + constant`
   for each lane. Gate and chip relations use separate relation IDs.
4. [`inspection.zig`](../../../../../src/frontends/s31/runtime/mixed_boundary/inspection.zig)
   projects the V4 source manifest and live handles into one ordered circuit,
   then chip/bridge pairs for calls 0–7. It binds the source SHA-256, canonical
   IR digest, fixed root, endpoint coordinates, component source/program
   digests, offsets, constraints, lookup relations, PCS geometry, mask-point
   digest, and local AIR dependency digest. The
   [`registry manifest`](../../../../../src/frontends/s31/runtime/mixed_boundary/registry_manifest.zig)
   hashes that projection plus the typed descriptor. It is a generated audit
   artifact, not a caller-provided verification key.
5. [`general_package.zig`](../../../../../src/frontends/s31/runtime/mixed_boundary/general_package.zig)
   rebuilds the profile from embedded source and official AIR before decoding
   the proof. Its header checks call/slot count and source, registry, and
   circuit identities. The engine's
   [`direct_mixed_general_arithmetic.zig`](../../../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig)
   mixes a distinct profile tag, a digest of source plus generated registry
   manifest, ordered call data, fixed commitment, circuit identity, eight
   canonical public words, main/interaction commitments, nonce, and claimed
   sums into one transcript. It checks the fixed commitment, selected AIR
   program binding, full lookup-sum closure, runtime AIR handles, PCS config,
   and STARK proof. The public engine adapter accepts a caller-selected
   schedule; only the S31 source-embedded verifier is an admission API.

## Input, proof, and resource observations

The V1 prover takes public claims from the assignment, evaluates the source
independently, and checks the native proof's eight output values against that
evaluation before writing its flat statement. The V2 prover compares the
canonical record statement's projected eight words with assignment claims;
the verifier performs the same typed projection before native verification.
Changing an embedded source byte changes the transcript source digest even if
canonical IR and fixed columns remain identical.

The verifier reads at most 16 MiB of proof and 1 MiB of statement, checks the
envelope before allocating proof objects, runs a geometry-aware postcard
preflight, allocates at most 64 MiB for postcard decode, requires exact byte
consumption, and then invokes native verification. The source compiler and
native plan also impose circuit row, variable, round, and committed-cell
limits. These are per-invocation limits; an embedding service still needs its
own concurrency and request budget. The CLI reads proof and statement files
once each into memory, so verification uses those snapshots; it does not
authenticate a filename or filesystem identity.

## Focused regression controls to add or retain

| Boundary | Focused control | Current evidence |
| --- | --- | --- |
| Feeder value | For each of `add`, `mul`, `add_const`, `mul_const`, and both private selector branches, compare all eight public words with an independent integer-mod-\(p\) oracle. | [`arithmetic_chip_input.py`](../../../../../src/frontends/s31/tests/acceptance/mixed_boundary/arithmetic_chip_input.py) covers arithmetic variants; native Zig tests cover selector branches. |
| Alias and multiplicity | At N=3, fork one four-lane arithmetic result into two calls; require equal input addresses and two additional bridge uses at each shared producer above its ordinary circuit use count. Mutate one endpoint address and require source reconstruction rejection. Keep negative duplicate-output and output-equals-input controls without forbidding input reuse. | The fork and fresh-output unit controls exist; an independent full fixed-column multiplicity assertion for this exact fork would make the PCS-bound count auditable. |
| Statement binding | Mutate each of the eight V1 public words individually, including a word that only depends on a later call. For V2, mutate every input and output leaf, path, nominal type and ABI digest. | V2 N1/N8 tests cover all words. V1 black-box tests change the whole word array or word zero; per-word V1 coverage is still useful. |
| Manifest and transcript | At N=1, 3 and 8, mutate each active claimed-sum slot, a compensating pair of sums, slot order/role, source byte with otherwise identical IR, and all three envelope digest fields. Reseal cleartext digests where possible to ensure native transcript rejection rather than only header rejection. | Existing general and arithmetic black-box controls cover most of these; preserve the resealed whitespace-source case and compensated-sum case. |
| Wire bounds | Feed truncated, trailing, oversized and structurally nested proof bytes to the embedded verifier under a time and memory cap; assert rejection before PCS work where preflight can decide. | Exact trailing-byte and 16 MiB limits are in code; a bounded black-box corpus would give direct resource evidence. |

## Limits of this conclusion

This review is source inspection, not a cryptographic proof. It assumes the
committed Gate/bridge/chip AIR constraints, LogUp compression, PCS/FRI, and
Fiat–Shamir transcript implementation are sound. The existing lookup budget
is a conditional algebraic term, not total proof-system security. A formal
source-to-native compiler correspondence theorem and a complete end-to-end
soundness bound are still outstanding. `private` marks language visibility;
the committed mixed trace does not provide witness confidentiality.
