# Wide integer examples

The `u256_*` programs exercise checked and wrapping 256-bit arithmetic,
comparisons, and public commitments to private results. Their fixture values
are little-endian arrays of sixteen `u16` limbs. Checked operations reject
overflow or underflow; wrapping operations retain the low 256 bits.

[`functional_u256_sum.s31`](functional_u256_sum.s31) passes a three-argument
closure through `apply3` before performing a checked sum and hashing its
limbs. Its [explicit counterpart](functional_u256_sum_manual.s31) uses the
same checked reduction directly. They must emit identical normalized IR and
select the same `sparse-wide-gate` AIR geometry. The shared
[`u256_sum_checked` assignment](u256_sum_checked.valid.json) adds
`2^128−1`, `1`, and `7` to obtain `2^128+7`. The functional acceptance gate
proves that result under the sparse-wide profile and rejects a changed public
root.
