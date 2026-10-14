# Mixed boundary private endpoint disclosure

Status: **confirmed proof-byte disclosure** in the experimental
`direct-mixed-general` profile. This is a confidentiality finding, not an
accepted false proof or a break of Merkle authentication. The word `private`
in the current S31 source means absent from the public statement; it does
not mean hidden from a holder of the proof.

## Concrete extraction

For each source-derived call, `tagged_pair_bridge.writeBase` or
`tagged_many_bridge.writeBase` copies its four input and four output words into
eight committed main columns. Each column is filled with the same M31 word on
all 16 bridge rows. Its committed low-degree polynomial is therefore constant
at every PCS query point. The source-derived component schedule gives the
bridge's main-column offset. The serialized STARK proof contains
`commitment_scheme_proof.queried_values.items[1]`, indexed by main column and
then query. A proof holder reads one query from each of those eight columns
and obtains the exact endpoint words, without the assignment or prover key.

The focused N=3 regression in
`src/frontends/s31/tests/proofs/mixed_boundary/opening_authentication.zig`
parses an honestly accepted `S31MIX07` proof. It asserts that **every** queried
value in the first four bridge main columns for each of the three calls equals
that call's private input state, and that the next four columns equal its
private output state. In particular, call 0's four input columns reveal the
four source-level private input words. The test deliberately does not print
the words into logs or reports. It also retains the existing mutation checks
showing that the queried values authenticate to their Merkle root; their
authenticity is exactly why they are dependable disclosures.

This mechanism applies to the one-call, pair and many bridge designs that
use the same constant endpoint columns. The regression runs the N=3 general
profile containing both pair and many roles. It is not evidence that every
other proof profile or every implementation path has been exhaustively
audited.

## Other disclosure surfaces

The circuit main trace commits actual Gate operands/results, and the chip
main trace commits each indexed input and output state. Their opened
low-degree extensions depend on private values without a hiding mask. A
sampled chip or circuit opening need not equal a raw trace cell, so this
review does not claim a general extraction algorithm from those columns.
Removing only the bridge columns would leave these surfaces. The individual
LogUp claimed sums in the proof header also depend on witness endpoint
values; their leakage must be analyzed before any zero-knowledge claim.
Deterministic commitments to low-entropy witnesses may allow candidate
testing even when an opening is not directly readable. We did not measure
such a candidate attack here because the bridge already gives exact words.

## Release boundary and remediation

Immediately document the current profile as **soundness-oriented,
non-confidential witness proving**. Never use source `private` as a security
promise, and do not use this proof profile where hiding a witness matters.
Changing the JSON statement or omitting endpoint words from it does not
change the proof-byte disclosure.

For a confidential profile, use a new proof/transcript version and a complete
zero-knowledge design across circuit, chip, bridge, lookup interaction and
composition traces. One candidate is randomized trace-polynomial masking:
keep the required values on the AIR trace domain while adding random multiples
of its vanishing polynomial to the committed codeword. That raises degree and
changes PCS geometry, masks and quotient bounds. The bridge's row-equality
constraints still need to hold on the trace domain, while off-domain queries
must no longer be constant endpoint values. The LogUp claimed-sum exposure
needs separate treatment, such as a proved sum-hiding construction that still
enforces global closure. The design needs an explicit zero-knowledge argument,
including low-entropy witnesses, and tests that inspect accepted proof bytes
for every component role. A bridge-only mask is insufficient while other
witness-bearing columns and claimed sums remain unreviewed.

No change to the current proof bytes or soundness verifier is proposed by this
review. The regression intentionally captures the present behavior until a
separate confidential profile replaces it.
