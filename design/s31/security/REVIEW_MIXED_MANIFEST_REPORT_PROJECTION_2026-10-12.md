# Independent review: mixed manifest report projection

Date: 2026-10-12. Reviewed base: `07bae7c96a391a996e231b2ba3ae4f35a35bfd22`.
Scope: the generated N1–N8 mixed manifest report, the independent acceptance
projector, and the source-embedded native verifier admission path.

## Finding and correction

The JSON inspector emits both `slots[].source_kind` and the registry constructor
fields. The version-1 registry digest hashes `registry_key`, ID, version, role,
call ID and claim index, but deliberately omits `source_kind`. Before this
change, the independent Python source/manifest projector checked the role and
call ID but did not check `source_kind`, constructor key, registry ID/version or
proof/claim indices. A postprocessed inspection report could therefore relabel
`source_kind` without changing its diagnostic digest or failing that projector.
This was **report/audit integrity only**: no evidence indicates native
false-proof admission.

The selected-schedule digest does include the live `source_kind`. Thus a
mutation of the schedule itself is rejected by its current-digest check. The
gap applies to a JSON report changed after inspection while retaining its
already emitted selected-schedule digest.

The projector now requires the canonical circuit, pair chip/bridge and many
chip/bridge constructor in every slot. It also requires each slot's proof and
claimed-sum index to equal its position in the `1+2N` roster. A serializer-only
fixture demonstrates that changing `source_kind` leaves the digest unchanged,
while changing `registry_key` changes it. Mutation controls alter every slot's
source kind for N1, N3 and N8, and swap chip/bridge claim indices while keeping
the same index set.

The native verifier remains independently source-embedded: it calls
`inspection.inspectSource`, builds the typed registry manifest via
`selectedFromSource`, compares the proof envelope's source hash, registry
digest and circuit identity against this reconstruction, then verifies using
the source-derived plan and geometry. It does not accept an external JSON
inspection report as a verifier key. The registry digest and this Python
projector are audit aids, not substitutes for proof verification.

## Focused evidence

`python3 -B src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static`
passed at the reviewed base plus this patch. It exercised N1, N3 and N8,
rejecting 20, 24 and 34 manifest mutations respectively and one changed
source constant per count. The static projector intentionally accepts a
coordinated fresh absolute-address retarget; it cannot derive compiler
addresses from source text alone. This review makes no claim about the native
AIR, PCS/FRI security, or complete compiler correctness.
