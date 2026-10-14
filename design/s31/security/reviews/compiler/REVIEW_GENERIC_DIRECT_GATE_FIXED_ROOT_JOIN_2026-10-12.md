# Independent review: direct Gate package fixed-root join

Reviewed `91b96fd` and the snapshot fix in `524280e`. The inspector is a
bounded, one-proof diagnostic for the public four-lane, 1–16 arithmetic-gate
text fragment. I found no additional acceptance issue in that scope.

## Checked trust chain

1. The caller supplies five lowercase SHA-256 pins for the original text,
   normalized source, key, prover, and verifier. `admitted_snapshot` checks
   them on a private package copy before either executable runs. Authenticity
   of the pins is an external assumption. The case07 regression derives pins
   from its already checked local package; it does not test that assumption.
2. `bounded_direct_gate_snapshot` recomputes the source certificate, requires
   the v2 direct Gate key and rooted topology, and asks the generated verifier
   to reconstruct its sealed key. The certificate independently parses the
   admitted source syntax and compares the exact normalized relation, gate
   schedule, ordered eight fixed columns, and all 4,096 selector/address/
   multiplicity cells. It uses the pinned prover only after package admission.
3. The inspector compares a fresh prover topology export with the checked
   package topology. It then passes eight explicitly serialized, canonical
   512-word columns to the native `rootFromWords` path. The resulting root
   must equal both the topology root and the sealed key root. This reuses the
   production PCS preparation and Merkle implementation with an explicit
   cell input; it is an independent input route, not a separate hash library.
4. The generated native verifier must accept the private proof and statement
   copies with that sealed key. The inspector compares both copies byte for
   byte with their captured originals after verification. It parses and
   hashes the originals, and requires the proof's first commitment root to
   equal the recommitted fixed root. Native `verifyDirectProfile` checks the
   entire proof decode, four commitments, exact PCS config, and that same
   first root against the reconstructed key before returning success.

The Python root offset matches the native serialization: eight magic bytes,
eight nonce bytes, one 16-byte QM31 sum, five one-byte PCS config values,
one null lifting-log tag, one commitment-count byte, then the 32-byte fixed
root. The parser rejects nonminimal or oversized varints; any accepted proof
has already passed the native decoder. The focused Python header tests pass
(three tests). The author reports passing retained-package native replays for
one, eight, fifteen, and sixteen gates. The eight-gate case07 has fixed/key/
proof root `791ada77…cb62ef8` and proof SHA-256 `78c03271…20b58548`;
wrong verifier pin, changed proof root, and changed statement were rejected.
I did not repeat the expensive native runs.

## Remaining assumptions

This joins checked fixed cells to **one accepted proof**. It does not prove
that arbitrary PCS openings authenticate the displayed main/interaction
rows, establish Merkle or FRI soundness, or extend source correspondence
beyond the admitted fragment. The native verifier and prover implementations,
the local execution environment, and the external pin source remain trusted.
The post-verifier byte comparison detects a persistent mutation of the private
copies; it is not a concurrency proof against a same-user process that can
modify and restore a private file while the verifier reads it.
