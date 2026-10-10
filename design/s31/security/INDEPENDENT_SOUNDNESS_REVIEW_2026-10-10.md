# Independent S31 soundness review — 2026-10-10

Scope: the source/statement/key boundary, the direct-M31 circuit-to-chip
private bridge, package admission, and the fixed SHA component roster. This
is an adversarial implementation review, not a proof of STARK or compiler
soundness. It excludes application protocols. The reviewer did not edit the
compiler, prover, verifier, key builder, or formal proof sources.

## Threat model and findings

| ID | Priority | Finding and evidence | Consequence and status |
| --- | --- | --- | --- |
| S31-SEC-01 | P1 for untrusted package distribution | A package can replace its executable native verifier with `#!/bin/sh\nexit 0\n`, update the verifier's SHA-256 in its own `manifest.json`, and pass `verify_package()`. The [control](controls/package_trust_probe.py) reproduces this on an existing valid package. | `verify_package()` establishes internal consistency, not publisher authenticity. A relying party that executes an untrusted packaged verifier can accept anything. This limit is [already documented](../../../src/frontends/s31/docs/proofs.md); it is not a break of a trusted installed native verifier. Require an externally pinned verifier/key digest, a trusted signed release, or a reproducible build from trusted inputs. Do not describe package hashes alone as an authentication root. |
| S31-SEC-02 | P2, ABI-consumer integrity; fixed in the working tree | Before the targeted fix, replacing only `public-abi.json` with a forged output name/shape and updating its manifest hash passed `verify_package()`. `verify_package()` checked the sidecar's hash but did not derive its meaning from the sealed relation. The same [control](controls/package_trust_probe.py) is now a passing rejection regression gate. | Software using `public-abi.json` could display or serialize the wrong named claim. The native verifier still parses the embedded source and requires its original statement, so this was **not** a demonstrated proof forgery. Package admission now recomputes `abi(source, lowering)` and compares the entire object. The external trust-root limitation in S31-SEC-01 remains. |
| S31-SEC-03 | P1 if witness secrecy is required | The direct private bridge writes each of the eight endpoint values into all 16 rows of its committed main trace ([bridge `writeBase`](../../../deps/stwo-zig/src/integrations/circuit_cpu/private_boundary_bridge.zig)). STARK opening queries can expose those values. | The profile omits endpoints from the **public statement**, but it does not provide witness confidentiality. This distinction is correctly stated in the [private-boundary guide](../../../src/frontends/s31/docs/private-boundary.md). Any release or API that promises secret endpoints needs a blinded bridge and a separate privacy analysis. This is a product security gate, not a contradiction of the currently documented semantics. |
| S31-SEC-04 | P1 before generalized chip admission | The private bridge currently admits one four-lane square/add recurrence with a hardcoded component set. The [profile note](PROFILE_SOUNDNESS.md) itself lists missing formal bounds for lookup tuple compression, LogUp, degree bounds, and out-of-domain masks. The bridge uses 16 copies of each Gate lookup with coefficient `1/16`; its AIR does not directly assert that the 16 rows carry the same endpoint values. | No forged proof was found. Equality of the row values follows only from the shared random lookup argument under its collision and denominator assumptions. Generalization must keep the closure proof explicit for every relation, address and multiplicity; a generated component manifest must reject missing/extra components and inconsistent claimed-sum order before transcript admission. |
| S31-SEC-05 | P1 for full-language correctness claim | The installed verifier re-lowers its embedded normalized relation into a value-free circuit and compares the resulting root/hash and boundary addresses with the embedded key ([`validateCompiledKey`](../../../src/frontends/s31/runtime/mvp_runtime.zig)). The [formal README](../../../formal/s31/README.md) explicitly excludes a full text/Python → Zig circuit → AIR → native verifier correspondence theorem. | The strong key check binds the verifier to **this compiler output**, not to independently proved source semantics. The parity corpus and local Lean gadget theorems are valuable evidence, but their test pass percentage is not a soundness coverage percentage. Until a full refinement chain is checked, phrase correctness claims as scoped to reviewed operations and tested profiles. |

### Reproduce the two package controls

From the repository root, supply any already-built, valid package with a
`public-abi.json`, for example a direct arithmetic record package:

```sh
python3 design/s31/security/controls/package_trust_probe.py zig-out/s31/records/record
```

The script copies the package twice to a temporary directory and leaves the
input untouched. Its JSON fields are `forged_abi_accepted` and
`replaced_verifier_accepted`. It exits nonzero if the forged ABI is accepted,
so it can serve as a regression gate. The replaced-verifier result is
observational because no check against an attacker-controlled manifest can
authenticate that same manifest. Before the ABI fix, both fields were `true`
on `record_square_sum`. An optional `--observe` prints the pre-fix behavior
without enforcing ABI rejection.

### External pin admission control

The new [pin checker](controls/pinned_package.py) requires exact SHA-256 pins
for the relation source, verification key, native prover, and native verifier. Those four
digests must come from a trusted release or another channel independent of the
package. After checking the pins, it checks the package's internal consistency.

```sh
python3 design/s31/security/controls/pinned_package.py PACKAGE \
  --source-sha256 SOURCE_DIGEST_FROM_TRUSTED_RELEASE \
  --key-sha256 KEY_DIGEST_FROM_TRUSTED_RELEASE \
  --prover-sha256 PROVER_DIGEST_FROM_TRUSTED_RELEASE \
  --verifier-sha256 VERIFIER_DIGEST_FROM_TRUSTED_RELEASE
```

The adversarial package control now records
`pinned_replaced_prover_accepted=false` and
`pinned_replaced_verifier_accepted=false` alongside the observation that an
attacker-controlled manifest accepts either replaced executable. On the
existing valid record package, the control returned
`forged_abi_accepted=false`, both unpinned replacement results `true`, both
pinned replacement results `false`, and all four wrong-pin results `false`.
This is a point-in-time admission
check, not a signed publication protocol or an execution sandbox. The trusted
channel and installed checker remain outside the package.

## Checks that held in the reviewed code

- The installed native verifier compares an externally supplied key's **exact
  bytes** against the embedded key before parsing it, and recompiles the
  value-free topology to check the fixed root, circuit identity and private
  addresses. This prevents a caller from nominating a different boundary via
  a statement or key file under that trusted executable.
- The direct private verifier rejects a wrong proof envelope, noncanonical
  public M31 word, changed circuit identity, nonzero combined lookup sum, and
  a changed preprocessed root before accepting the STARK proof. The existing
  focused proof tests cover changed public words, source digest, and boundary
  addresses. Independently rerunning
  `python3 src/frontends/s31/tests/acceptance/acceptance_private_boundary.py`
  accepted one honest 69,978-byte proof and rejected its six package, key,
  statement, witness, source, and proof mutations. These observations are
  code review and test coverage, not a cryptographic proof.
- For the fixed SHA joint profile, the verifier reconstructs the component
  order and tree geometry, checks the pinned circuit AIR bundle digest,
  validates the canonical profile, and checks both Gate and SHA lookup
  closures. This is a profile-specific roster; it is not a general generated
  manifest.

## Explicit proof obligations for the next implementation wave

1. Model the bridge's eight weighted Gate fractions and two chip endpoint
   fractions as rational functions over the actual challenge field. Bound the
   probability that a wrong endpoint, row-varying bridge value, collision, or
   zero denominator passes. The 16-row averaging argument needs the field
   characteristic, unique addresses, and transcript timing as premises.
2. Prove that the chip's indexed row multiset, local transition equations,
   authenticated start/end, and `R < p` imply one complete length-`R` path,
   including no leftover cycles. Check the exact AIR degree declaration,
   masks, trace/log sizes and quotient evaluator against this model.
3. Generate a component manifest from compiled topology, bind its canonical
   digest to the key and transcript, then reject reordered, omitted,
   duplicated, or unbound components and lookup relations. Test this for
   circuits with zero, one, and multiple chip calls.
4. Establish a commuting refinement diagram from typed text source through
   normalized relation, witness generation, circuit gates, AIR rows, and
   native public-claim acceptance. Separate a trusted compiler theorem from
   a verifier theorem and state each cryptographic assumption explicitly.
5. Bind the record ABI v2's canonical layout and leaf paths to the relation,
   key and statement. Its currently isolated codec is a useful preparatory
   artifact; it does not yet authorize record-valued circuit boundaries.

No false proof acceptance was demonstrated in this review. The package
controls show precisely where artifact self-consistency ends and the relying
party's trust in executable code and claim metadata begins.

## Addendum: direct-gate manifest and affine private step

This pass reviewed the newly generated `direct-gate` manifest and the three
private step shapes (`square → add`, `add → square`, and one square with static
affine maps on both sides). It did not run a competing package build while
the private-boundary acceptance suite was active.

### Direct-gate manifest

[`component_manifest.directGate`](../../../src/frontends/s31/runtime/component_manifest.zig)
parses the pinned AIR bytes, selects and rebinds the one `qm31_ops` component,
and records its source/proof indices, ordered trace spans, preprocessed
indices, constraint count, column geometry, all eight fixed-column value
digests, and source/IR/root/circuit identities. The installed verifier parses
its embedded key with unknown fields rejected, recompiles the sealed source
without values, regenerates the fixed preprocessed circuit and manifest, and
requires an exact typed-manifest match before reading the proof. It also
requires the external key file's bytes to equal the embedded key bytes.
The package reader checks the manifest sidecar, report, and key agree.

The new manifest is **checked metadata**, not an additional Fiat–Shamir input
or an authoritative component scheduler. The existing direct profile still
selects one component, one claimed sum, and its existing transcript tag,
source digest, preprocessed root and circuit identity. A proof for the same
source, circuit, and public claim can remain valid across the old and new key
schema; the newly built verifier nevertheless requires the new schema and
rederived manifest. The documented legacy-package reader path does not let
an external key downgrade that installed verifier. This is a scope limit for
general component admission, not a demonstrated forgery.

The manifest generator uses the pinned AIR bundle bytes as the cryptographic
program identity; its `composition_plan_hash` is only 64 bits and should not
be treated alone as a security digest. The full pinned AIR digest, component
binding, fixed-column digests, and preprocessed Merkle root are checked
together in this profile. For a future multi-chip profile, the manifest must
become authoritative for the exact ordered component and claimed-sum roster,
or the verifier must continue independently reconstructing that roster.

The direct-gate package acceptance passed: one honest native proof accepted,
one changed public claim rejected, and `3/3` mutations each of the rehashed
manifest sidecar, rehashed cost report, and re-sealed native key rejected.
Those mutations changed fixed-column order, a preprocessed column index, and
a fixed-column value digest. The generator also checks the pinned AIR-bundle
hash. These controls support key/metadata consistency; they do not prove
soundness of the underlying AIR or STARK.

### Affine coordinate change and boundary

For source step `T(x)=C(Ax+B)²+D`, with nonzero `A` and `C` in M31, define
`q=C A²`, `r=C A B`, and `s=qx+r`. Then `s(T(x))=s²+k`, where `k=qD+r`.
[`privateRepeatedStepChip`](../../../src/frontends/s31/language/relation.zig)
rejects zero scales, a second square, `mix4`, and an unsupported round count.
The [compiler](../../../src/frontends/s31/language/relation_compiler.zig)
builds Gate-constrained `s₀=qx₀+r`, binds the chip's initial and final `s`
wires to eight bridge addresses, and computes each source-level final value
as `x_R=q⁻¹(s_R−r)` before downstream public-output gates. The verifier
rederives the addresses and preprocessed root from the embedded source. Its
private profile mixes the source digest, chip rounds/constant and addresses
before commitment; the public claim enters the common transcript separately.

The independent [arithmetic oracle](controls/affine_step_oracle.py) compared
all three normalized source bodies with their hand-derived chip coordinates
on seven inputs per body for all 16 rounds. It also matched each fixture's
claimed public sum. Result: `3/3` cases, `7/7` samples per case, all 16
rounds matched. This verifies the algebra on these examples; it does not
prove the compiler emits those gates or that the AIR enforces them for every
witness. Native proof acceptance and key/claim mutation controls are the
separate implementation gate.

The parallel native package acceptance completed for all three shapes:
`69,978` bytes for square/add, `68,716` for add/square, and `70,471` for the
general affine example. All `3/3` honest proofs were accepted; each case
rejected `8/8` mutations covering public claim, statement private-field
injection, both boundary address lists, chip constant, witness, source, and
proof bytes. A zero-scale affine source was rejected before packaging. The
focused Zig proof suite and docs checker also passed. These are executable
controls over the current fixtures, not a proof for arbitrary source bodies.

The confidentiality consequence is exact for this affine family. The bridge
repeats `s₀` in a committed main column; any opening exposing `s₀` reveals
the original private input as `x₀=q⁻¹(s₀−r)`, since `q` and `r` are public
source-derived constants and `q` is invertible. The revised
[private-boundary guide](../../../src/frontends/s31/docs/private-boundary.md)
states this explicitly. No claim of zero knowledge follows from omission of
the input from the public statement.

### Formal ideal-boundary increment

The new [affine boundary module](../../../formal/s31/S31/Gadgets/Air/AffineChipBoundary.lean)
proves, over an arbitrary field, that the compiler's coordinate transform
`s = (c a²)x + (c a b)` conjugates every iteration of
`x ↦ c(ax+b)²+d` to `s ↦ s² + ((c a²)d + c a b)`. It also proves
decoding is inverse when `a` and `c` are nonzero. These are algebraic facts;
they do not say the emitted gates enforce the transform.

The [generic boundary module](../../../formal/s31/S31/Gadgets/Air/GenericChipBoundary.lean)
states an ideal multi-call invariant: if circuit Gate events and tagged chip
endpoint events each have exact multiset balance against a bridge, and each
address or call tag has a unique producer, then every four-lane circuit
endpoint equals its corresponding chip endpoint. A separate lemma shows that
sixteen bridge rows must carry one common value **if** their exact event
multiset equals sixteen copies of that value. The production bridge presently
supports one call; the model's call tag is a requirement for future multiple
calls, not a property claimed of today's AIR. The actual LogUp challenge
argument, row-to-event mapping and compiler correspondence still need proofs.

The [bridge challenge lemmas](../../../formal/s31/S31/Gadgets/Air/PrivateBridgeChallenge.lean)
instantiate the existing finite-field Gate challenge bound for sixteen
potentially different bridge row values against sixteen copies of one circuit
value. If any row differs, exact event balance is impossible; a false
reciprocal closure lies in the bounded exceptional set of challenge pairs,
assuming a canonical address and multiplicities below the field
characteristic. Multiplying the bridge's `1/16` contribution by 16 motivates
this model. For eight distinct canonical addresses, the new joint Gate lemma
shows that a wrong row at any address makes the combined ideal event multiset
unequal and inherits the exceptional-pair bound. The native paired-fraction
AIR-to-reciprocal derivation and the joint Gate-plus-chip probability bound
remain unproved.

### 2026-10-10 follow-up: direct-chip roster and record ABI v2

The current one-call direct-chip manifest is regenerated inside the sealed
verifier from its source, compiled direct circuit, pinned AIR bundle and
native component parameters. Its two-component public roster and
three-component private roster follow the engine's circuit, chip, then bridge
order, with claimed sums at the same positions. The key's exact bytes must
match the embedded key before any proof is read. The manifest remains checked
metadata: it is not itself a new transcript message or proof of the chip AIR.
The native controls test rehashed sidecar and report mutations and re-sealed
key mutations, including component order, sum position, chip constant and
private bridge address. Source inspection found no proof forgery through this
binding in the current one-call profile; it does not establish an arbitrary
multi-call component scheduler. The manifest label lifetime defect below was
fixed and the cross-optimization key check passed afterward.

The output-only record ABI v2 binds a canonical typed descriptor digest to
the sealed key and source-derived IR. The native statement decoder requires
the matching ABI digest, exact canonical JSON bytes, ordered named paths,
canonical M31 words, and equal values for repeated wire aliases before it
projects to the eight public proof words. Ten focused Python record tests
passed. The native acceptance script covers an honest proof, changed claim,
field name/order, alias mismatch, digest, noncanonical word/JSON, duplicate
JSON key and re-sealed wrong key digest. After the label fix, the ReleaseSafe
verifier accepted the honest ReleaseFast key and proof, then rejected the
alias mismatch with a structured error. The independent source read found
no record-statement bypass. These controls do not prove parser-to-AIR
correspondence or cryptographic soundness of the production verifier.

An adversarial probe exposed a narrower trust-root gap in the first version
of the external pin checker: replacing the package's prover executable and
rehashing only its manifest entry passed a source/key/verifier three-pin
check. This is a private-witness execution risk if users run an admitted
package's prover, although a trusted native verifier still rejects invalid
proofs. The checker now requires the prover's externally supplied digest as
a fourth pin. Re-running the lightweight package control on the existing
valid record package showed `replaced_prover_accepted=true` under the
self-hashed package check, `pinned_replaced_prover_accepted=false`, and
wrong source/key/prover/verifier pins all rejected. A trusted channel for
these pins and the local checker remain external assumptions.

### 2026-10-10 follow-up: dangling component label (fixed)

The record acceptance run exposed a direct-gate manifest integrity defect:
a cached v2 prover's `inspect` emitted eight component-name bytes `0xaa`
instead of `qm31_ops`, and a key generated in ReleaseFast did not match the
ReleaseSafe rederived manifest. The same direct-gate component forms the
first entry of the new direct-chip manifest. This is an observed key
reproducibility and availability failure; it is **not** evidence that an
invalid STARK proof was accepted.

The lifetime path is concrete. `air.bindComponent` allocates `selected.label`;
`component_manifest.directGate` places that slice directly in the returned
manifest's `components[0].name`; its deferred `bound.deinit()` then calls
`deinitComponent`, which frees the label before the manifest is serialized.
Zig's allocator interface poisons freed slices with undefined bytes even
when an arena's underlying free cannot reclaim the allocation. The observed
`0xaa` bytes are consistent with that poisoning. The preprocessed column IDs
are static identifiers and are a separate field. The fix duplicates the
validated label into manifest-owned arena storage before `bound.deinit()`
frees its source allocation. The rerun emitted the literal `qm31_ops`, kept
raw/padded AIR geometry and the ABI digest unchanged, and passed ReleaseFast
proof verification with the ReleaseSafe verifier plus the alias and re-sealed
key rejection controls. This closes the observed reproducibility defect for
this profile, not the broader compiler or STARK proof obligations.
