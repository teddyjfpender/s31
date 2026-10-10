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
