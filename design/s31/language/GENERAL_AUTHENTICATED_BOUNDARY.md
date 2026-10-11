# General authenticated circuit-to-chip boundary

Status: engineering contract for the next profile. The source-pinned V4
one-kind profile proves 1–8 tagged square/add calls. The mixed N=3 profile
proves the fixed pair/pair/many roster; the distinct N=4 profile is being
admitted separately. Neither fixed roster is a general component scheduler.

## Claim and trust root

For a verifier binary built from an authenticated source program, AIR bundle,
component registry and PCS profile, acceptance should mean that **some**
witness satisfies the source program and yields the caller's expected public
words, subject to the stated compiler, AIR, lookup and PCS soundness premises.
The caller must choose those public words independently of the prover. A
package manifest and hashes inside the package cannot authenticate a replaced
verifier executable. `private` controls the public ABI; the current bridge
traces are unblinded and do not hide endpoint values.

The verifier must reconstruct every call, endpoint address, component kind,
column span, claimed-sum index, fixed column, lookup relation and PCS setting
from its embedded source plus a versioned registry **before** decoding a proof.
The proof may carry values and commitments, but may not nominate a component
or an AIR. The canonical roster digest enters Fiat–Shamir before the first
witness commitment. Exact source bytes, the official AIR bundle, the registry
revision, and the verifier's profile tag have independent digest domains.

## Compiler output and registry

The source compiler emits a witness-free `BoundaryPlan` and a witness plan.
Both follow the same normalized dataflow. The witness-free plan owns the
addresses; the witness plan must reproduce the complete plan, including the
preprocessed root, before it can write traces.

```text
BoundaryPlan {
  source_digest, canonical_ir_digest, public_abi,
  fixed_root, circuit_air_binding, pcs_profile,
  calls: [Call { id, source_node, kind, parameters,
                 input_ports: [GateAddress], output_ports: [GateAddress] }],
  components: [Component { registry_id, call_id?, role,
                           proof_index, sum_index, column_spans,
                           trace_log, evaluation_log, constraint_span,
                           fixed_indices, relation_dependencies,
                           air_binding }]
}
```

`registry_id` is a tagged, versioned constructor identity. A native AIR is
identified by its kind, version, source digest and parameter encoding; a
bundled AIR is identified by bundle digest, bundle index and rebound program
digest. The pair and many AIRs can be the first two registered chip families.
Each registry entry must provide: parameter validation, a fixed port type,
arity and parameter ABI, a bounded witness writer, prover and verifier AIR
constructors, claimed-sum extraction, exact trace/constraint geometry, lookup
relation IDs and port semantics. A new kind
is disabled until those functions and its soundness review are present.

The manifest is a canonical encoding of the reconstructed plan and live AIR
handle facts. Its JSON view is for inspection. The verifier compares its
registry-derived roster with actual handles; a caller-supplied JSON field or
digest never drives construction. Use checked arithmetic for all offsets,
counts and allocations, and bound components, calls, rounds and proof bytes
per versioned profile.

## One proof, one ordered transcript

The native composer should generate specialized arrays of registered AIR
constructors from the source-derived plan. This preserves per-chip trace
generators and packed columns while sharing one fixed commitment, one main
commitment, one interaction commitment and one PCS/FRI instance. It avoids
emitting a generic circuit for long chip recurrences. The verifier uses the
same generated roster and order, and rejects extra or absent claim slots.

```text
profile + roster digest + source digest + PCS settings
    -> fixed root + public words
    -> main commitment
    -> interaction PoW + lookup challenge
    -> ordered component claimed sums
    -> interaction commitment
    -> one native PCS proof
```

For each lookup relation, the circuit, chips and bridges must close their
tagged event sums; the verifier checks the declared closure vector before
PCS verification. A bridge's Gate address and chip endpoint tags must be
compiler-owned. Equal total sums alone do not authenticate individual AIR
claims, so every claim must also be installed in its corresponding live AIR.
Unrelated lookup relations, calls and event identities need structural domain
separation in their tuples **before** random linear lookup compression.
Matching producer and consumer events use the same canonical tuple encoding
with opposite signed multiplicities; role determines the sign and source, not
a distinct event tag. Compressed field values can still collide. The release
argument must bound those collisions, zero denominators and false closure
probability for the actual challenge field and event counts. Repeated Gate
addresses retain their full multiplicity.

## Release sequence

1. Admit a new bounded **1–8-call mixed** profile using the existing pair and
   many registry entries. The kind policy is source-derived and explicit;
   first preserve the N=3 and N=4 behavior under a new transcript tag. Make
   count, component arrays, envelope and preflight dynamic within fixed caps.
2. Generate one typed roster and manifest from the same registry used to
   instantiate prover and verifier handles. Reject changed role, order,
   source binding, relation list, address, span, sum index, fixed root, PCS
   geometry and unused claim slots before native proof admission.
3. Add a second semantically different chip kind only after its transition,
   endpoint and lookup contracts are specified. A mixed proof must exercise
   both kinds and a circuit operation between them; identical square/add
   implementations with different AIR names do not establish generality.
4. Complete the compiler refinement for the admitted source grammar and the
   AIR/lookup/PCS reduction. Keep the native experimental label until that
   chain is reviewed. Add a separate blinded profile and privacy proof before
   claiming witness confidentiality.

The first release test matrix covers every admitted count and chip kind;
dependent calls, repeated addresses and public-output liveness; independent
integer-oracle outputs; changed source, key, statement and all proof-header
fields; every claimed sum and compensated sum pairs; omitted, duplicate and
reordered components; malformed or oversized proofs; and cross-profile replay.
Proof bytes, peak RSS, setup, proving and verification time need paired native
measurements against equivalent circuit lowerings before a speedup claim.
