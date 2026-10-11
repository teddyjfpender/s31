# Independent review: sealed mixed N=3 proof profile

Reviewed S31 `043fb4745a021391d0228fc44d8383fd989502b4` with engine
`807530990cdb9c8fc346801e6f1f44611e9f47dc` on 2026-10-11. This was an
independent source and test review of the experimental three-call profile. I
found no concrete false-proof admission through its sealed verifier. I did not
independently rerun the long native proof suites.

## Findings

### P2: the engine adapter remains caller-authorized for S31 source semantics

The engine hashes the caller's `source_bytes` and `manifest_sha256`, then
rebuilds live geometry, the fixed root, and the bound circuit AIR from the
caller-supplied circuit and plan
([`direct_mixed_arithmetic.zig:51-76`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_arithmetic.zig#L51-L76),
[`direct_mixed_arithmetic.zig:201-225`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_arithmetic.zig#L201-L225)).
It cannot parse S31 or establish that those inputs came from the literal
source. Its public in-process `verifySourceBoundBorrowed` must therefore not
be exposed as a standalone source-authenticating proof-byte verifier.

The sealed S31 entrypoint supplies the missing authority: `verifyEmbedded`
receives compile-time source and AIR bytes; before postcard allocation it
recompiles the source with `inspectSource`, derives the plan and manifest digest,
checks the envelope's source, manifest, and circuit-identity hashes, then
recompiles the verifier circuit
([`package.zig:115-167`](../../../src/frontends/s31/runtime/mixed_boundary/package.zig#L115-L167)).
It applies source-derived geometry to bounded preflight and the engine verifier
([`package.zig:168-213`](../../../src/frontends/s31/runtime/mixed_boundary/package.zig#L168-L213)).
The engine independently recomputes selected live geometry, the circuit AIR
binding, fixed root and PCS config before core verification
([`direct_mixed_arithmetic.zig:459-570`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_arithmetic.zig#L459-L570)).
This P2 boundary is documented and does not yield a false proof through the
sealed entrypoint.

### P3: focused acceptance is narrower than general composition soundness

The source-level proof test uses one three-call program with independent
repeats over a shared private input. It checks an honest proof, each of seven
claimed-sum positions, a compensating chip/bridge sum pair, resealed changed
call order and endpoint source, changed source/manifest headers, wrong public
words, trailing bytes, and V4 cross-profile replay
([`package.zig:215-322`](../../../src/frontends/s31/runtime/mixed_boundary/package.zig#L215-L322)).
The engine test also changes main and interaction commitment roots and rejects
nonzero unused in-memory sum slots
([`direct_mixed_arithmetic.zig:578-684`](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_arithmetic.zig#L578-L684)).
The source inspector separately rejects altered relation IDs, program bindings,
PCS geometry and local AIR dependency hashes
([`experimental_mixed_admission.zig:365-444`](../../../src/frontends/s31/runtime/experimental_mixed_admission.zig#L365-L444)).

These controls exercise the selected roster and admission path. They do not
establish independent pair/many AIR equation soundness, a cryptographic
LogUp/PCS/FRI proof, full compiler correspondence, or arbitrary mixed call
counts. A changed source can fail at its fixed-root or public-statement check,
so the resealed endpoint case alone is not a standalone bridge-equation proof.
The deterministic mask-point digest inspects one audit point; the live verifier
still derives masks at its transcript challenge. The profile note accurately
states these limits and makes no witness-confidentiality or speedup claim
([`MIXED_NATIVE_N3_PROFILE.md`](../language/MIXED_NATIVE_N3_PROFILE.md)).

## Checks and decision

I inspected the source and mutation controls above and ran `git diff --check`
over the S31 and engine increments; both were clean. The integration agent
reported passing combined S31 N=3 Debug and ReleaseFast focused runs (2/2
each), engine ReleaseFast focused tests (3/3), V4 counts 2–8 ReleaseFast with
N=8 byte equality at 173,058 bytes, formal checks (56/1,344), docs checks,
and 306 Python tests. Those run results are reported evidence, not tests I
independently executed. The combined engine retains the checked prover and
verifier exceptional-OODS-seed paths and the earlier Linux configure fixes.

- **Go** for the source-pinned, proof-backed **experimental N=3** profile through
  `verifyEmbedded` only.
- **No-go** for treating the engine adapter as a standalone S31 source verifier,
  for a general mixed-chip release, or for claims of witness confidentiality,
  full formal soundness, or measured proving speedup from this increment.
