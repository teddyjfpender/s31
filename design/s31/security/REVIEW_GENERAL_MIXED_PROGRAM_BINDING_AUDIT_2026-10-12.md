# Exact native program binding in the bounded mixed manifest audit

## Scope

The experimental 1–8 call mixed inspector reports one chip and one bridge per
call. Its `program_binding_sha256` for each native component is the SHA-256 of
the component kind, its AIR source hash, and the *entire* call tuple. The call
tuple includes the source node, rounds, constant, and all four private circuit
input and output addresses. Each bridge and chip must point at its own call.

The independent Python report audit now recomputes this digest for every
chip/bridge slot. It uses the same specified byte layout as the Zig producer:

```text
SHA256("S31-MIXED-NATIVE-COMPONENT-PROTOTYPE-V1\0"
       || u8(source_kind)
       || 32-byte AIR source hash
       || le32(call_id, source_node_id, input_node_id, rounds, constant)
       || le32(input[0..4]) || le32(output[0..4]))
```

The audit also checks the slot's constructor and call index. This closes a
specific **inspection coverage** gap: the earlier independent source roster
check accepted an arbitrary program binding string if the diagnostic registry
digest was recomputed with it. The new static controls re-seal that digest
after changing private input and output addresses, chip/bridge binding strings,
and an AIR source hash; all seven changed reports are rejected for each of
1-, 3-, and 8-call fixtures. First and last calls are covered.

Run the fast check with:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static
```

The audit reads a diagnostic JSON report. It does not grant verifier authority
to the report or make changed source code valid. Native proof admission still
rebuilds the roster from verifier-owned source and installed AIR code; the
native verifier, PCS and FRI must enforce the committed polynomial openings.
The static check alone does not independently authenticate the report's native
AIR source hashes or prove PCS/FRI soundness. A native report cross-check for
all eight call counts remains necessary before claiming end-to-end coverage.
