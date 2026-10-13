# Raw PCS/FRI capture admission in the v0.1 SHA packages

The `sha-joint`, `sha-shift`, and `sha-fused` package runtimes dispatch to
separate native verifiers. Each now runs three checks after core proof
verification and before reporting success:

1. Recompute each raw DEEP quotient answer from captured sampled and queried
   columns, with the package's trace lifting size.
2. Replay every raw FRI query through the captured fold subsets and terminal
   polynomial, with the package's FRI configuration.
3. Rebuild each packed or unpacked FRI Merkle subset subtree, replay its upper
   path, and compare with the captured commitment root.

The shared gate is
[`pcs_capture_admission.zig`](../../../src/frontends/s31/sha/verification/pcs_capture_admission.zig).
[`sha_release_capture.py`](../../../scripts/s31_formal_lib/sha_release_capture.py)
pins all three release package dispatches, their verifier calls, and the
post-verification replay order. The generic runtime has its own equivalent
barriers. Other SHA research verifiers are outside this release roster.

These checks detect disagreement in the accepted capture and prevent verifier
success when replay fails. The SHA verifiers discard the capture after this
check. They reuse core quotient, terminal and Merkle
primitives; they do not prove those primitives correct, bind a fixed global
oracle, establish collision resistance, or derive random-oracle challenges.
They also do not prove the native verifier implements the Lean acceptance
model. P04, P05 and P06 remain open in the v0.1 blocker matrix, alongside
the transcript and full-proximity obligations.

The focused source mutation controls are in
[`test_sha_release_capture.py`](../../../scripts/tests/test_sha_release_capture.py).
The v0.1 native audit exercises each release package with a real proof,
changed public statement, altered proof, and altered key. Passing those
finite cases is regression evidence, not a whole-proof security bound.
