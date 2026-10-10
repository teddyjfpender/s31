# Bounded multi-call authenticated circuit-to-chip boundary

Status: **experimental source-pinned native proving and verification are
implemented for the bounded 1–8-call profile**. The unexported
[`bounded_call_admission.zig`](../../../src/frontends/s31/language/bounded_call_admission.zig)
extracts canonical, live calls and enforces the initial source bounds. The
[`bounded_compiled_binding.zig`](../../../src/frontends/s31/runtime/bounded_compiled_binding.zig)
inspection recompiles 1–8 source calls without witness values, attaches their
compiler-owned addresses, builds a separately counted Gate preprocessed
circuit, and checks the generated V4 roster against engine prefix sums and
live V4 chip/bridge verifier handles. The preflight derives tree logs, mask
widths, composition split and degree, and fixed PCS from those handles.
[`many_native_package.zig`](../../../src/frontends/s31/runtime/many_native_package.zig)
binds that inspection to a distinct V4 transcript, checks a canonical
source-pinned byte envelope before bounded postcard decoding, then invokes
native verification. The engine still builds its component schedule from a
typed Plan; the manifest cross-checks it instead of constructing each handle.
This is the successor to
the experimental, fixed two-call `direct-m31-private-pair-v1` profile. It must not
replace or reinterpret any existing one-call or pair proof. The first v4
implementation admits 1–8 instances of the existing four-lane tagged
`s -> s² + c` chip. The plan and manifest formats are suitable for more chip
kinds, but each later kind needs its own AIR, lookup tuple, resource limits,
and soundness review before admission.

Earlier inspection validation at S31 `5382e252` and engine `a3656919` passed:
`zig build test -Dtest-filter=V4` in the engine circuit CPU package;
`zig build test-bounded-call-source test-bounded-component-manifest
test-bounded-compiled-binding` in the S31 package; and the existing V3
`zig build test-pair-native` regression. These historical checks predate V4
proof admission.

The live-handle slice at S31 `c59b885` and engine `fb300ed1` passed
`zig build test -Dtest-filter=V4` in the engine package and
`zig build test-bounded-component-manifest test-bounded-compiled-binding`
in S31. This includes one-call live preflight and one-/three-call manifest
inspection with geometry, relation, and source-binding mismatch controls.
This historical checkpoint also predates V4 proof admission.

The current source-pinned V4 test matrix proves and verifies every count from
1 through 8. The N=2 through 8 test generates dependent source calls,
mutates every `1+2N` claimed-sum position, and includes call ID 7 at N=8.
For N=5,6,7, the eight public words are also checked against pinned values
from an independent ordinary-integer modular oracle. The one-call black-box
CLI acceptance test mutates public words, envelope digests, claimed sums,
postcard bytes, and embedded source. These tests are evidence for this one
reviewed chip family and source grammar, not for arbitrary component kinds.

## Statement and source-owned Plan

The public statement is the sealed source identity, versioned proof profile,
generated manifest identity, PCS parameters, and the source-declared public
outputs. Each call's input and output values are witness values. Every admitted
call must contribute to a public output through the circuit's checked dataflow;
dead calls are rejected. `private` means absent from the public ABI, **not**
confidential: the present bridge commits each endpoint as a constant column
and proof openings can reveal it. A zero-knowledge boundary is a separate
profile and requires a new privacy argument.

The adversary may choose witness values, proof bytes, and every package file.
The verifier must obtain source and key identity from its embedded binary or
an authenticated caller, then reconstruct the Plan and fixed circuit before
accepting a proof. The target claim is that accepted public outputs are
consistent with *some* private witness under that pinned source, subject to
the AIR, lookup, and PCS soundness assumptions. It does not assert where the
witness came from, prevent a prover from choosing a different valid witness,
or hide endpoint values from someone who sees the proof.

Compile the normalized source twice, without values and with values, using
the same canonical IR traversal. The witness-free pass is authoritative:

```text
PlanV4 = {
  profile: direct-m31-private-many-v1,
  calls: [Call { id, source_node_id, chip_kind, chip_version,
                 rounds, constant, input_address[4], output_address[4] }],
  public_output_addresses, circuit_shape, fixed_preprocessed_root
}
```

IDs are consecutive `0..N-1` in canonical **live repeat-node** order, with
`1 <= N <= 8`. The admitted initial normalized JSON source grammar is v1
direct-M31 arithmetic:
private `[m31; 4]` inputs, `N` four-lane repeats whose body is exactly
`square; add_const`, and ordinary `add`, `mul`, and lane-reduction nodes that
connect all repeat results to public outputs. A call may consume an earlier
call's output; the compiler must record that actual circuit address, rather
than assuming independent inputs. Initially, each repeat input is a private
input or the output of an earlier repeat. Arithmetic immediately before a
repeat requires constrained scalar endpoint materialization and is rejected
until that compiler path exists. Public inputs and non-direct circuit
components are outside this initial profile. All rounds are powers of two
in `[16, 32768]`; constants are canonical M31 words. No source or proof field
may assign an ID or an endpoint address. Reject unused repeats, unsupported
bodies, aliases that would evade live-node accounting, and public exposure of
an endpoint. The source declares at most eight public M31 words. The compiler
flattens them in canonical public-output order into the first `W` of eight
reserved words; the remaining `8-W` words are constrained zero. The native
statement must carry all eight words and its verifier must check this padding
against the source-derived public ABI. Compare every Plan field and the
preprocessed root between value and topology compilation before building the
witness trace. Recompile the witness-free Plan from the
verifier's *embedded or externally pinned* source before parsing proof bytes.

For example, a three-call source may compute `a = repeat_16(x)`,
`b = repeat_32(y)`, `c = repeat_16(a)`, then publish
`sum_lanes(b + c)`. Its canonical calls are `0,1,2`; call 2's input
addresses are call 0's output addresses. Those four addresses receive two
boundary uses each, one as call 0's output and one as call 2's input, in
addition to ordinary circuit uses. All three chip outputs affect the claim.

Each of the `8N` endpoint occurrences adds **one** Gate use at its circuit
address. Repeated addresses are legal and add repeated uses; a deduplicated
set is wrong. Check one genuine producer per address, no reserved/public
endpoint address, `address < p`, and canonical checked multiplicity `< p`,
where `p = 2^31 - 1`. The fixed preprocessed columns and their Merkle root
must be recomputed from these counts. Source and key hashes inside an
attacker-selected package are not a trust root; a released verifier embeds
or receives authenticated source/key identities from its caller.

## AIR and lookup closure

Keep one bridge component per call for v4. One chip component has nine base
columns, eight interaction columns, six constraints, and `R_i` rows. One
bridge has eight base columns, 20 interaction columns, thirteen constraints,
and 16 rows. Its eight cyclic row-equality constraints make its eight
endpoint columns constant. The remaining five constraints realize four
pairs of Gate fractions and one pair of tagged chip endpoint fractions.
The chip lookup tuple is

```text
Chip(relation_id, call_id, row_index, lane0, lane1, lane2, lane3)
```

with `call_id` a source-derived **component parameter**, never a trace
column or proof choice. The Gate tuple retains its six fields. One challenge
pair `(z, alpha)` is sampled after all base commitments. Gate and chip
relations use distinct fixed relation IDs. For call `i`, let `G(a,v)` and
`C(i,j,s)` denote their compressed tuples, and let `b_i^0,b_i^R` be its
eight bridge endpoints. Its extra rational terms are

```text
Gate circuit:  -Σ_i Σ_lanes [1/G(a_in(i,l), v_in(i,l))
                            + 1/G(a_out(i,l), v_out(i,l))]
Bridge i:      +Σ_16 rows (1/16) [Σ_lanes 1/G(a_in(i,l), b_i^0[l])
                                         + 1/G(a_out(i,l), b_i^R[l])
                                  - 1/C(i,0,b_i^0) + 1/C(i,R_i,b_i^R)]
Chip i:        +Σ_{j=0}^{R_i-1} [1/C(i,j,s_j) - 1/C(i,j+1,s_{j+1})]
```

The actual verifier checks `public_Gate_terms + Σ_{k=0}^{2N} claimed_sum[k]
= 0`, then verifies all AIRs and the shared PCS proof. All sums use one
ordered claim vector; no component may be omitted or appended. The ideal
algebraic argument assumes exact tagged event-multiset equality, unique
Gate producers, and the AIR transition equations. The native argument must
also bound false equality under random compression, zero denominators,
weighted multiplicities, and field wrap. It must account for all `N` calls,
all relations, and the selected FRI/PCS parameters. Do not infer a concrete
soundness level merely from the ideal Lean theorem.

**Why an array generalization is unsafe:** the current tagged chip and
bridge reject `call_id >= 2`, and the pair verifier constructs exactly five
component handles. More subtly, the chip AIR enforces each local transition
but does not set `row_index` equal to the physical trace row. The conclusion
that a length-`R_i` chip is the exact path `0 -> R_i` relies on exact
tagged multiset balance, `R_i < p`, and the fact that this path already
uses all `R_i` rows; it cannot simply be asserted from the transition
equations. The proof must be generalized to `N` with unique canonical tags
and no extra cycles or field-wrapped paths. A global claimed-sum equality is
only a probabilistic proxy for that exact balance. Repeated Gate addresses
make canonical multiplicity accounting essential.

## Canonical typed manifest and native schedule

Use fresh envelope magic, manifest-hash domain, and transcript tag for V4.
Do not reuse `S31NAT8P` or the pair's V3 digest. Serialize a
typed `ComponentSource`, for example `bundled_air {bundle_sha256, index,
part_sha256}` or `native_air {kind, version, code_sha256}`. The current V4
inspection has a typed native kind and a program digest that includes the
distinct V4 chip/bridge AIR source files and the compiler-owned endpoints.
The source-pinned V4 proof envelope is implemented but remains experimental;
there is no external V4 verification-key schema. The pair format's
numeric `source_index = 0` is a native sentinel, so treating it as a general
zero-based AIR index would be ambiguous. Reject unknown kinds and versions;
the JSON view is not the hash input.

The source-derived component order is **circuit, chips in call order,
bridges in call order**. Every entry includes source kind, proof index,
claimed-sum index, relation dependencies, row log, exact base and
interaction spans, evaluation-degree bound, constraint count and random
coefficient offset, selected preprocessed indices, and program binding.
The inspection manifest includes the ordered Call records, source and
canonical IR digests, the reconstructed fixed preprocessed root, fixed PCS/FRI
parameters, the geometry derived from live verifier handles, and public ABI
shape. It does not yet contain individual fixed-column value digests or a
native proof key. After compiler endpoints are attached, both native
component program digests include the ordered input and output addresses;
the source-only blueprint uses a distinct absent-endpoint tag. Length-delimit
every field in a canonical binary encoding. Exclude
the circuit identity hash from the precommitment to avoid a hash cycle;
derive that identity from the manifest precommitment, fixed root, and PCS
profile. Mix the versioned manifest digest before the first base commitment.
The verifier reconstructs the source-derived manifest from embedded source
and pinned AIR; no proof-supplied component description drives the schedule.

The proposed V4 channel begins with its own profile tag `S31MANY\x01` and
an effective digest in the
`S31-DIRECT-CHIP-MANY-MANIFEST-TRANSCRIPT-V4` domain, followed by the
source-derived ordered call Plan. It then mixes channel salt and fixed FRI
configuration, commits the fixed preprocessed columns, mixes the circuit
identity in the `S31-DIRECT-M31-CHIP-MANY-V1` domain, and mixes the public
output words **before** the main commitment. The remaining order is main
commitment, interaction PoW nonce, lookup challenge, ordered claimed sums,
interaction commitment, then the PCS proof. `TranscriptOrder` records this
expected sequence for review; the native V4 prover and verifier consume the
corresponding ordered fields, while the helper itself is not their executable
transcript implementation.

For circuit row log `L`, rounds `R_i`, and circuit constraint count `C`, the
selected roster has `1+2N` components and ordered claims. Tree 0 has eight
fixed columns. Trees 1 and 2 contain, respectively,

```text
base width          = 12 + 17N
interaction width   =  8 + 28N
constraint count    =  C + 19N
chip i base span    = [12+9i, 12+9(i+1))
bridge i base span  = [12+9N+8i, 12+9N+8(i+1))
chip i inter span   = [8+8i, 8+8(i+1))
bridge i inter span = [8+8N+20i, 8+8N+20(i+1))
chip i coeff offset = C+6i
bridge i offset     = C+6N+13i
```

These formulas are review invariants, **not** a second source of verifier
truth. The witness-free preflight now builds the actual V4 verifier handles
from the source Plan, derives tree logs, widths, masks, composition split and
degree through the same component API intended for proof verification, and
rejects disagreement with the generated manifest. The experimental native
verifier uses this preflight before decoding. Claimed-sum indices are exactly
`0..2N`: circuit,
then chips, then bridges. An empty, duplicate, or reordered slot is invalid.
The source-derived roster also determines lookup dependency closure: Gate
production/consumption and every tagged chip endpoint relation must balance.
Reject a component whose relation dependency is absent, even if its
claim happens to be zero.

### Can the manifest schedule components?

For this bounded profile, **the manifest can become the single typed schedule
input**, but it is not yet the direct scheduler. Today `inspectMany` derives a
manifest and an engine `Plan` from authenticated source, constructs live AIR
handles through `direct_many_preflight.inspect`, and compares each handle's
order, widths, trace/evaluation logs, degree, fixed indices, source binding,
constraint offsets, and PCS geometry with the manifest. Proof admission
repeats this inspection before decoding. The engine then independently
constructs its component arrays from the `Plan` and its own roster. No caller
supplies geometry to the source-pinned verifier, but the manifest still
cross-checks a second schedule instead of owning the construction.

The next scheduler API should accept only a sealed, source-derived
`SelectedSchedule` containing the ordered live handles and checked PCS
geometry. It should create each chip/bridge handle from its typed source kind
and compiled endpoints, derive all spans and claimed-sum indices from those
handles, and use that same object for commitment, transcript, quotient,
opening, and verifier preflight. Unknown kinds, different handle counts or
order, or any mismatch with the generated manifest must fail before proof
decoding. Keep the engine's independent roster formulas as assertions, not
as caller-controlled geometry. A generalized package reader must
authenticate the source and selected AIR before constructing this object;
raw package metadata or a matching digest alone is not authority.

This change needs an AIR-level lookup dependency registry for each admitted
kind. The current `lookup_relation_ids` values are assigned by known source
kind in `direct_many_preflight`, rather than discovered from evaluator
formulas. Thus the lookup-closure check is conditional on review of those
AIR implementations. A new kind cannot become admissible merely by adding
a manifest enum value. The source compiler, live AIR, relation IDs, and
transcript schedule must agree under separate tests or proofs. Endpoint
confidentiality remains absent because the bridge commits endpoint values.

## Resource and proof-byte admission

Initial fixed profile caps: `N <= 8`, `L <= 16`, `ΣR_i <= 2^18`, source bytes
`<= 1 MiB`, and canonical endpoint multiplicities `< p`. Compute every
length, offset, and allocation with checked arithmetic. Before proving,
bound the field-cell count

```text
B = 12*2^L + 9*ΣR_i + 8*16*N
I =  8*2^L + 8*ΣR_i + 20*16*N
B + I <= 6,000,000
```

This bounds the principal committed trace storage; it is **not** a peak-RSS
claim. The exact PCS, FFT, quotient, and proof-memory limits require native
measurements. The current profile uses a 16 MiB proof wire cap and a bounded
decoder allocation of 8–64 MiB, at most 32 times the wire length. Before
postcard allocation, reject wrong magic, wrong source-derived digests,
noncanonical M31 words or varints, extra/trailing bytes, and use the
source-derived four-tree column counts, max log size, and mask sample widths
with the canonical postcard preflight. Do not accept proof-provided logs,
query widths, component counts, or FRI parameters. A parser may do bounded
work on untrusted bytes but must not allocate according to them before these
checks. Record proof size, prove/verify time, and peak RSS at N=1 through 8
against the same-source generic-circuit path before choosing a default.
The envelope has exactly one nonce and `1+2N` canonical QM31 claims of
16 bytes each; its header length is computed from the source Plan, never
from a proof count field.

## Implementation and release sequence

The fixed V3 pair protocol is separate. V4 now has source admission,
compiler-derived endpoints, witness/topology and fixed-root checks, 1–8-call
tagged AIRs, a typed manifest, live-handle/PCS preflight, a source-pinned
envelope, native proving and verification, and count-matrix tests. The
following gates remain before treating this as a released general boundary:

1. Make the typed selected schedule the actual prover/verifier construction
   path, preserving live-handle checks and refusing unsupported AIR kinds or
   geometry. Confirm transcript, quotient, and PCS order use that one object.
2. Extend the exact path and tagged lookup arguments in Lean to variable N;
   prove compiler/IR-to-AIR correspondence for all admitted source forms.
3. Complete the mutation matrix below with independent source-level review,
   including lookup adversaries that bypass self-hash checks.
4. Quantify lookup/PCS soundness error and measure proof size, time, and peak
   memory at all admitted counts and large resource-bound instances.
5. Define an authenticated external verification-key/package format before
   allowing a general package reader to select this profile.

| Mutation class | Required rejection evidence |
| --- | --- |
| Source/Plan | Re-sealed changed source, constants, rounds, call order, missing/duplicate ID, wrong endpoint or public-output address, dead call, and value/topology Plan mismatch. |
| Lookup | Cross-swapped endpoints, repeated address with one lost Gate use, changed multiplicity including `p` wrap, row-varying bridge endpoint, chip trace with missing/duplicate index or disjoint cycle. |
| Roster/transcript | Omitted/extra/reordered component, source-kind swap, wrong program binding, span/log/constraint/degree/claim index, altered claimed sum, old-profile replay. |
| Wire/PCS | Changed public claim, noncanonical field word or varint, truncated/trailing bytes, inflated vector length or mask width, wrong FRI/PCS parameters, proofs above caps. |

At least one case in each class must bypass package self-hashes by re-sealing
an adversarial key or mutating the native proof bytes. A failed semantic
mutation should be rejected by the **native** verifier, not only by a Python
package comparison. This v4 slice is a scalable authenticated boundary for
one chip kind; arbitrary chip families, a general scheduler, and endpoint
confidentiality remain separately versioned work.
