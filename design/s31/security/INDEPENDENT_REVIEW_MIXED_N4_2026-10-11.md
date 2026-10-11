# Independent review: source-pinned mixed N=4 proof profile

**Date:** 2026-10-11. **Exact reviewed code:** isolated S31 implementation
`39d235c5cf1e503e8b60cca90e1fddcc5bd373c1`; integrated S31
`ad8ad39cec501ff8d2ddadf76e8a78b49d60fc5e`; pinned engine
`2a0960dd8b57c6bff5c10ea241bd559e15cd95b9`. All 18 paths in the
isolated N=4 implementation commit are byte-identical at the integrated head.
The integrated head also contains separate compiler and formal-inventory
changes, which this N=4 review does not assess. I reviewed the clean commits,
their focused test code, and their CI wiring. I did not independently rerun
the native proof suites or Ubuntu CI.

**Decision:** Go for the dedicated, source-embedded experimental N=4 verifier
in `runtime/mixed_boundary/n4_package.zig:verifyEmbedded` and its
`direct-mixed4` binary. I found no concrete P1/P2 false-proof admission in
this scope. No-go for treating the in-process engine adapter or an unpinned
package as a general authenticated S31 boundary, for arbitrary mixed rosters,
or for witness-confidentiality and full AIR/PCS soundness claims.

## Admission and equations inspected

The S31 wrapper rebuilds its four-call, nine-component roster from literal
source and the official AIR bundle before proof allocation. It checks the
distinct `S31MIX06` envelope, call/sum counts, version, source, manifest and
circuit-identity digests, and nine canonical QM31 sums. A source-derived
four-tree preflight limits proof shape; decoding uses a bounded arena and
requires exact end of input (`n4_package.zig:188-274`). The CLI embeds its
source and AIR, reads proof and statement into memory, checks all eight
canonical public words through native verification, checks statement identity,
and prints `verified` only after both pass (`n4_verifier_main.zig:7-24`). Zig's
JSON parser rejects duplicate fields by default; the CLI also rejects unknown
fields.

The engine rechecks the exact count, resource shape, official AIR bytes,
source digest, fixed-column root, selected live geometry, bound Gate AIR,
four PCS commitment roots and configuration, and output words
(`direct_mixed_four_arithmetic.zig:202-225,459-494`). Prover and verifier
order the profile, salt, FRI settings, fixed commitment, circuit identity,
public words, main commitment, PoW nonce, lookup challenge, nine claimed sums,
interaction commitment and PCS proof alike (`:323-445,495-575`). The verifier
checks global lookup closure, mixes every sum before interaction commitment,
then installs each sum into its corresponding circuit, pair/many chip or
bridge AIR. It rejects nonzero unused in-memory sum slots. The source-derived
roster fixes the first two calls to pair AIRs and the next two to many AIRs;
each chip and bridge has a call ID and compiler-owned endpoint addresses.

The engine's `verifySourceBoundBorrowed` accepts a caller-supplied plan and
manifest digest and cannot itself prove that they came from S31 source. Only
the S31 embedded-source wrapper supplies that authorization. An external
party must authenticate the verifier executable and its embedded source,
registry, AIR and PCS profile; hashes inside a replaced package cannot do so.

## Controls and limits

The focused S31 test exercises honest proof verification, mutations of each
of nine sums, a compensating two-sum mutation that preserves global closure,
header/source/manifest/identity changes, resealed source, wrong public words,
trailing bytes, resealed descriptor role swap, and both N=3 to N=4 and N=4 to
N=3 replay rejection (`n4_package.zig:277-376`). The engine test adds call
order, endpoint, PCS geometry, role, commitment-root and unused-slot changes
(`direct_mixed_four_arithmetic.zig:578-694`). The black-box CLI acceptance
also checks invalid witness/output, duplicate and unknown statement fields,
noncanonical public words, proof bytes, changed embedded source and unsupported
three-call build (`source_pinned_n4.py`). The dedicated CI job is configured
to run these checks on Ubuntu; its result was pending at review time.

The implementing agent reported engine Debug and ReleaseFast N=4 runs at 3/3
each; S31 sealed Debug and ReleaseFast N=4 runs at 2/2 each; descriptor and
witness controls at 6/6; existing N=3 and V4 regression suites passing; and
the black-box CLI acceptance passing 30 negative controls. These were not
independently rerun for this review. The pinned local proof fixture is
110,020 bytes with SHA-256
`408ff6a32b9374ea92a8a086ffc4b2ef0114749a2f9b2a09b4e5adb9b849aade`.
I checked both committed increments with `git diff --check`; they were clean.
These are test and code-review observations, not an independent proof of the
pair/many AIR equations, lookup collision and zero-denominator bounds, random
composition, PCS/FRI, Fiat–Shamir, or full source/compiler correspondence.

The source language's `private` visibility determines the public ABI. The
committed base trace is unblinded and may reveal witness values. The N=4
profile admits only this fixed four-call schedule; the proposed general
authenticated circuit-to-chip boundary remains a separate release obligation.
