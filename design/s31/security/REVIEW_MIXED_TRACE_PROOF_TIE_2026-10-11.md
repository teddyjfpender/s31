# Mixed trace and proof tie: independent check

Scope: `src/frontends/s31/tests/proofs/mixed_boundary/trace_correspondence.zig`
at `a52822f`, plus the decoded-commitment control added in this review.

## What the production path actually does

`general_package.proveSealedAndInspect` reconstructs a source schedule,
compiles the witness, and calls `direct_mixed_general_arithmetic.proveSourceBound`.
That engine calls the circuit, pair/many chip, and pair/many bridge base writers
used in the fixture, checks chip final states, selects those columns into the
main commitment, and creates the STARK proof. The package serializes a header
containing source, registry-manifest, and circuit-identity digests, followed by
the nonce, claimed sums, and postcard proof.

`general_package.verifyEmbeddedAndInspect` supplies compile-time source and AIR
bytes. Its private verifier rebuilds the schedule and digest identities before
decoding proof bytes, checks the header, derives the expected proof shape from
the rebuilt geometry, runs structural preflight, and delegates to
`verifySourceBoundBorrowed`. The engine checks the fixed root, PCS config,
public outputs, transcript nonce, lookup closure, runtime component handles,
and the borrowed STARK proof. The caller cannot select a manifest or AIR roster
through the serialized envelope.

## Test claim and one strengthened control

The N=1/N=8 fixture uses pinned source bytes, checks all chip and bridge base
rows against an independently calculated field recurrence, then proves and
verifies those same source bytes and public words. Header digest mutations,
nonce and claimed-sum mutations, an arbitrary proof-body byte mutation, a
changed public word, and a different embedded source all fail verification.

The original last-byte proof mutation could fail solely in postcard parsing.
The added control decodes the genuine STARK proof, changes only its **main
Merkle commitment root**, reserializes it, and asserts that the changed proof
passes the same source-derived structural preflight as production. It then
requires native verification to reject it. This distinguishes a well-formed
commitment tamper from malformed-byte rejection and exercises transcript or
cryptographic verification after preflight.

## Limits

This is a two-fixture executable check, not an extraction of committed trace
polynomials or a proof that the serialized commitment equals every independently
calculated cell. The fixture intentionally calls the production base writers,
so a shared writer defect could survive its row checks; the recurrence oracle
and source address assertions reduce that risk. General compiler correspondence,
independent AIR soundness, and the underlying STARK/FRI security assumptions
remain separate obligations. A single changed commitment may be rejected at
the transcript nonce before the later FRI verifier; this control therefore
does not claim that FRI itself was reached.
