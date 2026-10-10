# General authenticated circuit-to-chip boundary

Status: **one-call generated manifest implemented; general design and
ideal-boundary theorem**. The native implementation is still restricted to
one four-lane affine-square repeated-step call. This brief defines the next
proof profile; it does not claim multi-call proof support.

## Contract

A chip call has an immutable compiler-assigned `call_id`, a chip kind and
version, static parameters, four input circuit addresses, four output circuit
addresses, and one selected AIR component instance. The compiler emits its
boundary plan while compiling **without witness values**. The verifier
recomputes that plan from its sealed source. The plan is part of a canonical
component manifest in the key and transcript. A proof supplies committed
values for all endpoints but cannot nominate an address, call ID, relation
kind, round count, or component order.

For each call, the intended statement is:

```text
circuit_gate_values(input_addresses)  = chip_state_at_start(call_id)
circuit_gate_values(output_addresses) = chip_state_at_end(call_id)
chip_AIR_accepts(the complete indexed trace between those states)
```

The endpoints may be omitted from the public statement. That does **not**
guarantee confidentiality: the current bridge repeats each endpoint in an
opened trace column. A separate blinded bridge and privacy argument are
required before a confidential API can be advertised.

## One proof, two authenticated joins

The circuit Gate lookup already authenticates an addressed wire's value by
matching uses to the unique producer of that address. The generalized bridge
must consume one extra Gate event per endpoint address. The chip lookup joins
an indexed transition trace to its two endpoint tuples. The bridge emits the
opposite chip endpoint events. All components share one base commitment,
challenge pair, interaction commitment, claimed-sum roster, composition
proof, and FRI proof.

The future chip tuple must include a **canonical call ID** as well as its
relation ID, row index and four state lanes:

```text
Chip(relation_id, call_id, row_index, lane0, lane1, lane2, lane3)
```

The current six-field tuple lacks `call_id`, which is safe only for its
single-call profile. Two calls with identical parameters must not be able to
exchange start or end endpoints. A new tuple arity and transcript/profile
version are required; assigning distinct calls to one shared six-field
relation would leave the desired per-call join unstated.

The bridge may batch calls in one 16-row component with separate column
groups for each call. This keeps its row domain fixed while base,
interaction and constraint widths grow linearly. The initial implementation
can use one bridge instance per call if that is easier to audit; a measured
batching change needs its own profile version and cost evidence. If the
bridge keeps `1/16` weights, the proof needs the field characteristic not to
divide 16, committed endpoints before challenges, and a bound on a false
weighted multiset identity. Merely checking the final sum at one challenge
does not give a deterministic equality assertion.

## Generated manifest and verifier schedule

For `N` calls, the selected roster is the circuit Gate AIR, `N` chip AIR
instances in canonical call order, then bridge component(s). The generated
manifest must contain, for **every** selected component:

- relation and component version, proof index, exact main/interaction trace
  offsets and logs, constraint count, evaluation degree, preprocessed column
  indices and value digests;
- chip parameters, call ID, four ordered input and output addresses, row
  count, and the bound program/code digest;
- ordered claimed-sum position and every lookup relation it consumes or
  produces, including multiplicity at repeated circuit addresses.

The verifier must rebuild this roster from the sealed source and pinned AIR
definitions **before proof deserialization**, compare it with the embedded
key, and use that same roster to configure both transcript and PCS trees.
The canonical manifest digest must be mixed before the first commitment in a
new proof profile. A self-hashed sidecar alone is neither a trust root nor a
binding to native verifier behavior.

The current direct-gate manifest is a one-component slice. The one-call
direct-chip manifest checks two components for public inputs, or three when
the private bridge is selected. The current native schedule still independently
selects those components and uses its existing transcript profile. The
manifest does not yet drive arbitrary component admission or enter the
Fiat–Shamir transcript under its own digest. Both slices are useful starting
points, but neither meets this general schedule contract.

## Soundness premises

The [generic Lean boundary theorem](../../../formal/s31/S31/Gadgets/Air/GenericChipBoundary.lean)
proves the ideal join for any number of tagged calls given exact Gate and chip
event multiset balance and unique producers. The
[affine chip theorem](../../../formal/s31/S31/Gadgets/Air/AffineChipBoundary.lean)
proves the existing coordinate change and iteration independently of proof
plumbing. Native soundness still needs these additional links:

1. The actual circuit, chip and bridge AIR equations imply their claimed
   rational sums with the declared degree and masks. All denominators are
   handled consistently with the transcript challenge distribution.
2. The two random lookup challenges make a false weighted event balance
   unlikely after all base columns are committed. Bounds must cover tuple
   compression collisions, zero denominators, multiplicities modulo the
   field characteristic, and bridge rows whose endpoint values vary.
3. Each chip trace has exactly its declared indexed path. A length-`R` trace
   with transition index `i → i+1`, authenticated `0` and `R` endpoints,
   and `R < p` must exclude missing rows and disjoint cycles.
4. The compiler preserves source semantics when it emits endpoint address
   pairs, witness values and preprocessed Gate multiplicities. The verifier
   recomputes exactly that compiler result without witness values.
5. The generated manifest, native selected-component order, claimed-sum
   order, transcript commitments and PCS tree geometry all agree. The package
   verifier's metadata checks do not substitute for this native agreement.

## Delivery gates

The one-call direct-chip migration and tamper controls are complete for its
current public and private profiles. Next introduce tagged chip tuples and two independent calls with
different constants and lengths, including a public output that depends on
both results. Accept the honest native proof and reject cross-swapped
endpoints, omitted/duplicated components, reused call IDs, wrong
multiplicity, changed claims and proof bytes. Then measure batch versus
per-call bridge geometry before choosing the general default. No automated
lowering choice should use an unvalidated cost model or presume the two
proof profiles soundness-equivalent.

## Implementation map: two independent calls

The first multi-call release should be the explicit `direct-chip-pair`
lowering, capped at exactly two calls. Use profile
`direct-m31-chip-pair-v1`, key schema
`s31-verification-key-direct-chip-pair-v1`, manifest schema
`s31-component-manifest-direct-chip-pair-v1`, proof magic `S31NAT8P`, and
transcript tag `0x5333315041495201` (`S31PAIR` plus version byte). Keep the
existing one-call `direct-chip` key schemas, proof magic, six-field tuple and
native verifier unchanged. A later variable-`N` profile can
reuse the internal plan with another versioned limit and measured geometry.

Use a source relation with two private four-lane inputs, two `repeat` nodes
with different constants and lengths (for example 16 and 32 rounds), and a
public sum of their four-lane outputs. The exact source operations already
exist; the new feature is extraction and proof selection for **both** nodes.
The first pair profile should reject unsupported repeat bodies, extra repeat
nodes, unconsumed calls, and noncanonical parameter values before packaging.

| Owner | Required change |
| --- | --- |
| S31 `language/relation.zig` and `canonical.zig` | Extract an ordered call plan from canonical IR, assigning call IDs `0,1` in canonical node order. Record each node ID, chip kind/version, rounds, transformed constant and nonzero affine coordinate map. Reusing or skipping an ID is invalid. |
| S31 `language/relation_compiler.zig` | Add a separate tagged multi-call lowering mode. For each planned repeat, emit the same constrained affine input/output wires as the one-call path, collect four input and four output addresses, and return a plan in `Maps`. Value and topology compilation must produce identical plans apart from witness values. |
| stwo-zig `frontends/circuit/common/direct_arithmetic.zig` | Build one preprocessed circuit from all boundary calls. Validate each address has one producer, reject forbidden public reservation addresses, and add one Gate use **per occurrence**, including repeated addresses. Bound the total multiplicity below the field characteristic. Preserve the one-boundary constructor. |
| stwo-zig `integrations/circuit_cpu/repeated_step_chip.zig` and `private_boundary_bridge.zig` | Add versioned tagged AIR modules. The chip and bridge use `Chip(relation_id, call_id, index, lane0..3)` with seven compression powers. `call_id` is a fixed component parameter, so the nine chip and eight bridge main-column widths need not grow. The new bridge also enforces eight row-to-row endpoint equalities. Keep the old six-field components callable by legacy proofs. |
| stwo-zig `integrations/circuit_cpu/direct_arithmetic.zig` | Add a shared pair-plan prover schedule: circuit, chip 0, chip 1, bridge 0, bridge 1. Commit all base columns before drawing one lookup challenge pair; mix the five claimed sums before committing all interaction columns, matching the existing direct prover transcript. Require `circuit_sum + Σ chip_sums + Σ bridge_sums = 0`. |
| S31 `runtime/component_manifest.zig`, `mvp_runtime.zig`, `native_verifier.zig` | Generate and reconstruct the exact five-component roster from sealed source and pinned AIR. The native verifier uses the validated plan for PCS logs, offsets, component handles, sum positions and transcript setup **before proof deserialization**. The new proof envelope carries exactly five canonical QM31 sums. |
| S31 `python/package/{build,verify}.py` and acceptance | Bind the versioned manifest into key, sidecar, cost report and package; retain explicit legacy branches. Build an honest pair proof and adversarial resealed-key, witness and proof cases. |

For two calls, tree 1 has `12 + 2·9 + 2·8 = 46` main columns and tree 2
has `8 + 2·8 + 2·20 = 64` interaction columns. The eight fixed circuit
columns remain in tree 0. Chip trace logs are `4` and `5` for the example;
both bridge logs are `4`. If the selected circuit has `C` constraints, the
five random-coefficient offsets are `0, C, C+6, C+12, C+25`; the total is
`C+38`, assuming six constraints per chip and thirteen per new bridge.
The extra eight bridge constraints make each endpoint column constant across
its 16 rows, simplifying the argument behind its `1/16` lookup weight.
Generate these values from the selected components and verify them
against the manifest, rather than maintaining a second handwritten list.

Use a canonical binary encoding to hash the roster: domain tag, source and
canonical IR digests, pinned AIR/code identities, fixed-column digests and
root, ordered call records, component geometry, and sum order. Exclude the
circuit identity hash from that digest to avoid a cycle; derive the new
circuit identity from the roster digest and fixed root. Mix the roster digest
under a new transcript tag **before the first commitment**. The JSON
manifest is an audit view of the same typed roster, not the hash input.

Acceptance must reject cross-swapped endpoints, changed call IDs, duplicated
or omitted calls/components, changed constants/lengths/addresses, wrong Gate
multiplicity, row-varying bridge endpoints, changed public claims, altered
claimed sums, truncated/trailing proof bytes, and old/new profile replay.
At least one mutation should re-seal a false key and verifier binary, proving
that source-derived reconstruction rejects it independently of package hashes.
The Lean ideal-join theorem covers exact tagged multiset balance only; a
separate probabilistic LogUp/PCS argument and compiler correspondence proof
remain release obligations. Measure complete prover time, peak memory and
proof size against the same source lowered through the generic circuit.

### Independent review questions before release

- Does canonical IR traversal assign the same IDs in the value compiler,
  topology compiler and sealed verifier, including repeated or shared
  subexpressions? Are dead chip calls rejected before any proof is built?
- Does the tagged chip AIR actually incorporate the fixed `call_id` into each
  seven-field lookup constraint, or is it merely displayed in JSON?
- Are every Gate address use and all repeated occurrences reflected in the
  committed multiplicity column with checked arithmetic below `p`?
- Are the new bridge's eight row-to-row equalities enforced at the wrap edge
  in both domain and point evaluation, with the correct circle-domain mask?
- Does the challenge argument bound false global lookup balance for both
  relations, seven-field compression collisions, zero denominators and
  weighted multiplicities? The ideal Lean multiset theorem assumes exact
  balance and does not discharge this probability bound.
- Does the same typed roster drive prover columns, verifier PCS logs,
  component order, sums and transcript mixing? Can an altered key be re-sealed
  with a verifier that silently uses another schedule?
- Are proof privacy and package trust described accurately? The current
  bridge opens private endpoints, and a self-hashed package is not an external
  trust root for its verifier binary.
