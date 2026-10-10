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
3. Extend the generated one-call direct-chip manifest to zero- and multi-call
   profiles. Reconstruct the exact ordered component and claimed-sum roster
   in both native paths, bind its typed digest before witness commitments,
   and reject reordered, omitted, duplicated, or unbound components and
   lookup relations. The current one-call path has the digest and mutation
   controls; the multi-call proof path is still disabled.
4. Establish a commuting refinement diagram from typed text source through
   normalized relation, witness generation, circuit gates, AIR rows, and
   native public-claim acceptance. Separate a trusted compiler theorem from
   a verifier theorem and state each cryptographic assumption explicitly.
5. Extend record ABI v2 beyond its implemented direct-gate boundary. The
   current direct-gate path binds canonical layout and leaf paths to the
   relation, key and statement; chip and other profiles do not yet admit
   record-valued boundaries.

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
this model. For eight canonical addresses, including repeated addresses whose
circuit producer values agree, the new joint Gate lemma shows that a wrong
row at any address makes the combined ideal event multiset unequal and
inherits the exceptional-pair bound. The finite-family theorem in
[`PrivateBridgeChallengeMany.lean`](../../../formal/s31/S31/Gadgets/Air/PrivateBridgeChallengeMany.lean)
extends that ideal Gate argument to any `n` endpoints with `16n < p` and
coherent expected values at repeated addresses. Its sixteen-endpoint
specialization bounds exceptional challenge pairs by
`1,311,744 × |GateSecure|`. The native paired-fraction AIR-to-reciprocal
derivation, PCS link, and joint Gate-plus-chip probability bound remain
unproved.

### 2026-10-10 follow-up: direct-chip roster and record ABI v2

The current one-call direct-chip manifest is regenerated inside the sealed
verifier from its source, compiled direct circuit, pinned AIR bundle and
native component parameters. Its two-component public roster and
three-component private roster follow the engine's circuit, chip, then bridge
order, with claimed sums at the same positions. The key's exact bytes must
match the embedded key before any proof is read. In the current v2 profile,
the typed manifest digest is folded into the effective source digest before
the witness commitment. The manifest is still checked metadata and is not a
proof of the chip AIR or a manifest-driven component scheduler.
The native controls test rehashed sidecar and report mutations and re-sealed
key mutations, including component order, sum position, chip constant and
private bridge address. Source inspection found no proof forgery through this
binding in the current one-call profile; it does not establish an arbitrary
multi-call component scheduler. The manifest label lifetime defect below was
fixed and the cross-optimization key check passed afterward.

The record ABI v2 binds a canonical typed descriptor digest to the sealed key
and source-derived IR for named input and output records under direct-gate.
The native statement decoder requires
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

### 2026-10-10 follow-up: authenticated boundary soundness audit

This source audit separates limitations of the **implemented one-call**
direct-chip profile from release gates for the **proposed two-call** profile in
[the general boundary design](../language/GENERAL_AUTHENTICATED_CHIP_BOUNDARY.md).
It did not run native proofs or establish a new proof forgery.

#### Implemented one-call profile

1. **Private is a statement boundary, not witness confidentiality.**
   `private_boundary_bridge.zig:55-71` commits each transformed endpoint as a
   constant M31 main column over all sixteen bridge rows. Opened bridge rows
   reveal that value. For the admitted affine change of variables
   `s = qx + r` with nonzero `q`, an observer can recover `x` from `s`.
   [The user documentation](../../../src/frontends/s31/docs/private-boundary.md)
   already gives the narrower definition of private. This is a confidentiality
   limitation, not an invalid-proof counterexample.

2. **Reserve the complete Gate multiplicity with checked arithmetic.**
   `computeUses` checks that every initial count is `< p`. The direct,
   sparse, and sparse-wide arithmetic builders formerly added permutation
   and boundary uses with unchecked `+=`. In particular, sparse-wide later
   converted counts with `M31.fromU64`, which silently reduces modulo `p`.
   The current dependency worktree now calls `addCanonicalMultiplicity` at
   every such reservation, including both SHA boundary calls and repeated
   addresses; that helper rejects crossing `p` before field conversion.
   This closes the identified invariant gap if the dependency patch is
   integrated and its at-the-bound regression tests pass. No forged proof was
   reproduced from the pre-fix code: reaching the bound in the admitted
   profiles requires an enormous trace.

3. **The source-shape gate does not require a live chip result.**
   `relation.zig:243-264` requires the private input, first repeat, later
   nodes, and a public output, but does not require any public output to
   depend transitively on the repeat. A repeat followed by an unrelated
   constant output fits those local checks. The chip still proves its own
   transition; the public claim simply does not consume it. Rejecting such
   dead calls is an admission and cost gate, not a demonstrated false result.

4. **The per-component native hash has a limited code closure.**
   `component_manifest.zig:321-337` hashes the embedded chip or bridge AIR
   source file and parameters; `build.zig:646-647,670-671` embeds those files.
   Transitive imported field, AIR, and PCS implementation code is not part of
   that per-component hash. The package separately fingerprints its pinned
   engine source, and its key is sealed to the installed native verifier. No
   verifier bypass follows from this observation. A general profile should
   specify whether `program_binding_sha256` means a canonical typed
   constraint program or a reproducible full code closure.

5. **External executable trust remains a deployment assumption.** Earlier
   package controls in this review show why a self-hashed package cannot
   authenticate its own verifier or prover. The four-pin checker now rejects
   the tested substitutions; users must obtain those pins and the checker
   through a trusted channel. This is a trust-root requirement of the current
   distribution, not a defect in its lookup equations.

#### Two-call profile: release blockers, not current one-call exploits

1. **P1 — put a call tag inside every Chip lookup tuple.** The current chip
   and bridge use six-field tuples `(relation_id, index, lane0..lane3)`
   (`repeated_step_chip.zig:164-189,204-213` and
   `private_boundary_bridge.zig:124-130`). With two untagged calls, their
   index-zero start events can be swapped while the global multiset closes:
   if chip A proves `a -> A(a)` and chip B proves `b -> B(b)`, the bridge
   could associate circuit call A with `b -> A(a)` and call B with
   `a -> B(b)`. The start and end event multisets still match although
   neither circuit call has its claimed input/output relation. A call ID in
   JSON does not fix this. Constrain a canonical unique call ID in the chip
   and bridge AIR tuples and version the proof profile/transcript.

2. **P1 — derive one canonical roster for the multi-call proof path.** The
   current one-call manifest checks a two- or three-component roster and its
   v2 typed digest is folded into the effective source digest before the
   witness commitment. Prover handles and claimed-sum positions
   (`direct_arithmetic.zig`) and verifier handles and positions
   (`native_verifier.zig`) remain independently constructed in explicit code.
   For two calls, generate both sides from one typed roster and bind its
   canonical digest before the first witness commitment. Mutation controls
   must cover order, offsets, log sizes, sum positions, and code identities.

3. **P1 — prove lookup premises for the implemented AIR and transcript.**
   `GenericChipBoundary.lean:114-140` establishes an ideal tagged-multiset
   join under exact balance and unique producers, but does not derive exact
   balance from native AIR, LogUp, or PCS verification.
   `PrivateBridgeChallengeMany.lean` proves the ideal Gate challenge result
   for any finite endpoint count satisfying `16n < p`, with coherent expected
   producer values at repeated canonical addresses. For two eight-endpoint
   calls, its sixteen-endpoint theorem gives the explicit upper bound
   `1,311,744 × |GateSecure|` exceptional challenge pairs. This **does**
   cover the larger ideal Gate event set. The proposed pair profile also has
   a seven-field tagged Chip relation. Its native release argument still
   needs a derivation from committed AIR rows through paired-fraction LogUp
   and PCS to the ideal rational closure, and a joint Gate/Chip bound that
   handles zero denominators, tuple compression collisions, canonical
   multiplicities, and weighted `1/16` bridge fractions. These Lean results
   are substantive ideal-model theorems, not yet native-profile soundness.

4. **P2 — verify the cyclic bridge mask when adding row-local endpoint
   equalities.** The one-call bridge masks only current main values
   (`private_boundary_bridge.zig:168-195`) and uses the lookup argument to
   bind all sixteen rows. If the pair profile adds neighbor equalities to
   make each endpoint constant, it must compare every row with its successor
   **including row 15 to row 0**, as its design specifies. The wrap equality
   is redundant for pure constancy if the other fifteen adjacent equalities
   form one enforced path, so its omission alone is not a counterexample.
   Incorrect circle-domain masks or an inadvertently missing interior edge
   could leave disconnected segments. Native mask-point geometry, quotient
   constraints, and boundary-row mutations should test these cases.

### 2026-10-10 follow-up: record-valued input ABI v2

I read the isolated record-input implementation at
`/private/tmp/s31-record-input-worktree` (`8dc20cc`, `d3b6657`) and the
corresponding files present in this worktree. This was a source audit, not an
independent rerun of its native acceptance program. Its acceptance control
[`acceptance_record_inputs_v2.py`](../../../src/frontends/s31/tests/acceptance/acceptance_record_inputs_v2.py)
constructs a nested public `Request` and private `Pair`, checks six flattened
first-order input wires and equal direct-gate cost against a manual flat v1
relation, then expects an honest native proof to pass. It explicitly expects
rejection for changed public input/result words, swapped same-type field
paths, an injected private leaf, changed result root, changed ABI digest, and
a re-sealed key that changes the private input's visibility. It also checks
missing nested fields, a noncanonical private M31 word, a misplaced private
root, wrong tuple arity, and duplicate JSON keys before proving. These are
implementation-agent controls; this review did not establish their pass rate
independently.

The native verifier recomputes the ABI digest from the embedded relation
(`mvp_runtime.zig:3480-3487`), requires it in the sealed key, and projects a
canonical, duplicate-key-free v2 statement to the exact eight proof words
(`record_abi.zig:285-370`). The validator binds each declared leaf path,
wire, length and input visibility to the flattened relation. A private input
is absent from the public statement, but its *witness value* is still subject
to the proof system's ordinary disclosure limits, including the bridge issue
above. I found no record-ABI forged-proof acceptance in this source review.

The review initially compared Python with an older isolated worktree and
reported that it accepted a result root renamed from `result`. Current main
already rejects that in `binding_v2.py:validate_binding`, with a regression
test. A fresh control on current main found a narrower fail-closed mismatch:
Python accepted a top-level tuple result when an input root was a record,
while native `record_abi.zig:root` rejected the tuple root. The Python
validator now applies the same first-order-or-record root rule, and a focused
test rejects the mutated descriptor. This was a package-admission and
developer-experience mismatch, not a forged proof.

### 2026-10-10 follow-up: v2 manifest and staged pair AIR

An independent source pass on S31 `57a2255` with pinned Stwo `b4ace22a`
found no concrete false-proof path in the enabled one-call profile. The
installed verifier reconstructs the manifest from its sealed source and
pinned AIR before reading the proof; the v2 envelope and effective source
digest bind the typed roster in the transcript. Public and private native
proof controls, changed claims, rehashed package metadata, and re-sealed
wrong keys passed. This supports the implementation boundary, not a theorem
for the AIR, LogUp challenge argument, or PCS.

The staged two-call AIR has no exported S31 proof API. Its tagged lookup tuple,
checked Gate multiplicities, unique producer addresses, and cyclic bridge
equalities were reviewed without finding a counterexample. This review
requested a **nonzero row-varying bridge residual** test before proof
admission; a zero-residual test cannot detect a wrong next-row mask. The
actual prover/verifier transcript must be compared event by event, including
channel salt, FRI configuration, PoW nonce, five claimed sums, and both
commitments. The staged transcript-order guard does not cover all of those
events. The top-level chip/bridge `program_binding_sha256` fingerprints do
not hash transitive Zig imports or the built executable, so they are audit
identifiers rather than complete executable identities.

#### Differential correction and first pair proof prototype

The requested invalid bridge witness exposed a concrete **staged AIR
implementation defect** before pair proof admission. The bridge point mask
used the trace-log-4 circle step while the quotient evaluator used a
log-5 lifted composition mask. For a nonzero row-varying endpoint residual,
the domain quotient and verifier point evaluator disagreed. Pinned Stwo
`39f78b05` now derives both neighbor mask points from the supplied maximum
mask log. The new differential selects a nonzero composition-domain quotient
value and compares it with point evaluation at its one-fold preimage; the
focused test passed on the pinned branch. The earlier zero-residual test
could not have found this bug. This correction is necessary for pair soundness
but does not prove the other AIR or PCS obligations.

An isolated engine prototype now forms one five-component, three-tree STARK
proof for two differently parameterized chip calls and verifies it with a
source-supplied pair plan. Honest proof and mutation checks have passed in
that isolated tree. During review, its test fixture initially created two
fresh lane-1 guess wires and then changed only the plan's lane-1 address to
alias lane 0; the public output still used the unbound fresh lane-1 output.
The fixture now aliases the actual circuit `Var` objects before constructing
public outputs and the plan. This illustrates the remaining
**source-to-plan correspondence obligation**: Gate and chip proofs can
authenticate the plan they are given, but only a checked compiler can show
that plan is the intended program's call boundary. The prototype remains
unexported and has no S31 package or sealed native verifier yet.

## Independent follow-up: staged pair, bounded correspondence, and cost v3.1

This follow-up inspected the staged two-call S31 source branch at `665dc38`,
engine branch at `a6a65a2e`, bounded correspondence branch at `426fe03`, and
whole-prover cost branch at `0c35099`. These branches were reviewed as source;
native builds and adversarial proof runs were deferred during the cost timing
run. No false public claim accepted by a trusted native verifier was found.

| Priority | Finding | Release action |
| --- | --- | --- |
| P1 for pair release | The staged pair verifier accepts `source`, `air_bytes`, and `sealed_key` as arguments, then derives and checks their internal consistency ([`verifySealed`](../../../src/frontends/s31/runtime/pair_native_package.zig)). The AIR bundle input passes the compiled SHA-256 check in `component_manifest.directGate`, reached through `directPair`; a caller can still select a different valid source and generate its matching key. This API is suitable for an internal adapter; it is not a deployed verifier with a fixed program identity. | Generate a verifier that embeds the intended source and exact key bytes, or require an independently authenticated source/key digest. Keep the pair path out of the public facade until that trust root and native byte tests exist. |
| P2 for canonical proof IDs | The pair encoder describes a canonical postcard proof, but its decoder uses [`readVarint`](../../../deps/stwo-zig/src/interop/postcard.zig) through `deserializeProof`. `readVarint` accepts overlong LEB128 encodings. By source inspection, replacing the first payload byte `0x1a` (PoW bits 26) with `0x9a 0x00` should decode to the same proof and pass the full-consumption test; this exact mutation still needs a native regression run. This is proof-byte malleability, not a forged claim. | Add allocation-free canonical proof-wire preflight, or reserialize the decoded proof and require byte equality; test the overlong varint and nested length bombs. The existing 16 MiB wire cap and 64 MiB decode cap bound memory, but do not enforce a unique encoding. |
| P1 if secrecy is promised | The new tagged bridge writes each private input and output endpoint to all sixteen committed rows ([`writeBase`](../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig)). | State that “private” excludes a public-input field but does not imply zero knowledge. A confidentiality claim needs a blinded construction and opening analysis. |
| P1 for full correspondence claim | The independent checker admits only one public four-lane M31 input, one public four-lane output, and 1–16 fresh add/pointwise-multiply lets ([grammar](../../../src/frontends/s31/python/package/correspondence.py)). Its gate replay checks exact selectors, addresses, multiplicities, operation order, public lane masks, and the constant/padding island for that fragment. Its own certificate marks root binding and AIR/PCS as assumptions and admission as Python-package-only. The installed native verifier does not independently parse the original text bytes. | Call this a bounded, package-level correspondence certificate. Extend the refinement to all admitted operations and the native verifier, then prove the circuit-to-AIR and lookup/PCS steps separately. Unit test counts are not a theorem coverage percentage. |
| P1 for generalized boundary | The current source admission requires exactly two four-lane private recurrence calls, fixed output sum/product, and a version-1 normalized relation ([`privateRepeatedStepPair`](../../../src/frontends/s31/language/relation.zig)). The engine verifier independently reconstructs a fixed five-component roster and one shared lookup transcript ([pair proof path](../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig)); the typed manifest is checked against source-derived fields. This is stronger than an unbound metadata sidecar, but remains a special case. | Keep arbitrary call count, arbitrary chip signatures, text-to-pair lowering, and record ABI on the pair path gated. Add cross-call alias and omitted/duplicated/reordered component controls when generalizing. |
| P1 for cost reliability claims | The v3.1 protocol records that v3 failed fitting on training-only degenerate chip features before any validation build or timing. The amended chip features come from sealed manifest component geometry, and the runner requires one host and compiler fingerprint, fresh packages, native acceptance, changed-claim rejection, and an independent output oracle ([protocol](../measurements/whole-prover-cost-v3.json); [runner](../../../src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v3.py)). At this review checkpoint the fresh v3.1 held-out measurements and predeclared gate result did not yet exist. | Publish the frozen training model, all held-out outcomes, and any failed family gate without tuning on held-out data. Scope any pass to this host/compiler/profile set; the experiment does not establish cross-host prediction or comparative proving speed. |

The pair AIR itself has useful safeguards: call IDs are verifier constants in
the tagged lookup tuples; the bridge enforces row-to-row equality for all eight
endpoint columns; source-derived multiplicities count repeated addresses; and
the verifier checks the ordered five lookup sums before the shared STARK proof.
These observations still depend on the challenge collision bound, LogUp
rational identity, correct quotient masks and degree declarations, and PCS/FRI
soundness. The staged source check and tests do not discharge those assumptions.

### Static re-review after canonical preflight patch

Engine `197291cb` and S31 `8d17edf` add a proof-wire preflight before
postcard decode allocation. The shape is reconstructed from the source-derived
Plan, pinned and rebound AIR, the same five verifier component types, their
column log sizes, and their sampled mask widths. It has four fixed tree counts;
the composition count follows the verifier's split calculation, and its
one-point mask width matches the core composition mask. The parser's canonical
varint reader rejects the `0x9a 0x00` overlong encoding described above.
Five claimed sums still occupy fixed header positions, pass canonical M31
limb checks, and enter the ordered lookup closure and transcript before STARK
verification. This closes the identified byte-malleability path by source
inspection. Honest pair proof decoding and the new mutation control remain
pending native execution at this review checkpoint; the embedded-key release
gate remains open.
