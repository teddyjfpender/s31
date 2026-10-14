# Framed raw-word arithmetic for the candidate PCS

**Status:** local arithmetic theorem for the reserved `S31NAT9F` channel. It
does not admit a proof or assign native security bits.

The [Lean model](../../../formal/s31/S31/Gadgets/PcsFri/FramedExactWord.lean)
matches one word of the candidate `canonicalM31Block` rule in the
[experimental native channel](https://github.com/teddyjfpender/stwo-zig/pull/282). For
`p = 2^31 − 1`, a raw little-endian `u32` word is accepted precisely when it
is below `2p`. Its canonical output is `word` if below `p`, otherwise
`word − p`.

For every residue `r` in `0 .. p−1`, Lean proves the **only** accepted raw
words mapping to `r` are `r` and `r+p`, and both fit in `u32`. The finite
preimage set therefore has cardinality two. Since `2^32 = 2p+2`, the only
rejected words are `2p` and `2p+1`. In an ideal independent uniform raw-word
model, conditioning on acceptance makes one residue exactly uniform. The
native code rejects an entire eight-word block when any word is excluded,
so the rejected block is consumed before the next counter is tried.

The theorem proves this finite arithmetic for **all** raw 32-bit values. It
does not establish that BLAKE2s frames are independent uniform oracle words,
that the native Zig loop refines Lean for all executions, or that the
challenge cap and all transcript failures are accounted for in a BCS theorem.
The framed channel remains unselected. The production Gate channel still
uses its different [M31 reduction and masked query
model](PCS_FRI_M31_MASKED_QUERY_DISTRIBUTION.md).
