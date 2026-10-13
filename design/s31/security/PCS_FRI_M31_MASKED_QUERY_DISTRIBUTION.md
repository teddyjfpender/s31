# Native M31 masked queries: exact finite distribution

The native M31 channel takes a BLAKE2s digest, treats it as eight little-endian
32-bit words, reduces each word modulo `p = 2^31 - 1`, and `drawQueries` keeps
its low `k` bits. For an ideal uniform 32-bit raw word `w`, the index is

```text
index_k(w) = (w mod p) mod 2^k,       1 <= k <= 31.
```

The [Lean proof](../../../formal/s31/S31/Gadgets/PcsFri/M31MaskedQuery.lean)
counts preimages over the entire finite range `0 <= w < 2^32`. The
[source contract](../../../scripts/s31_formal_lib/pcs_fri_m31_query.py) checks
the selected native call chain and arithmetic stages; the formal binding
records hashes of the channel, hasher, field and query source files. This
contract is a change detector, while the Lean theorem is an arithmetic
statement about the explicitly modeled map.

## Counting by hand

Since `2^32 = 2p + 2`, every residue in `0 .. p-1` has two raw preimages,
and residues `0` and `1` each have one more. For `m = 2^k`, let
`q = 2^(31-k)`. Then `p = m q - 1`, so `0 .. p-1` contains `q` full
blocks of each masked index except the last index, which occurs `q-1`
times. Hence the exact count for a query index `i` is

```text
preimages_k(i)
  = 2 * (q - 1 + [i < m - 1]) + [i = 0] + [i = 1],
```

where `[P]` is 1 if `P` is true and 0 otherwise. A uniform query index
would have `2^32/m = 2q` raw preimages. For `k=1`, index 0 has `2q+1`
preimages and index 1 has `2q-1`. For `2 <= k <= 31`, indices 0 and 1
each have `2q+1`, the final index has `2q-2`, and all others have `2q`.

At `k=2`, `q = 2^29` and the four counts are:

| Index | Raw preimages | Difference from uniform |
| --- | ---: | ---: |
| 0 | 1,073,741,825 | +1 |
| 1 | 1,073,741,825 | +1 |
| 2 | 1,073,741,824 | 0 |
| 3 | 1,073,741,822 | -2 |

These add to `2^32`. The good set `{0,1}` has one-draw probability
`1/2 + 2/2^32`, so the positive bias bound is attained. At `k=1`, the
good set `{0}` attains `1/2 + 1/2^32`.

For any **fixed** good set with uniform density at most `alpha`, the Lean
proof gives one-draw probability at most `alpha + 1/2^32` for `k=1`, or
`alpha + 2/2^32` for `2 <= k <= 31`. Conditional on successive raw hash
words being independent and uniform, all `s` draws land in that same fixed
set with probability at most the corresponding bound raised to `s`.
Repetition is allowed; sorting and deduplication after sampling do not
improve this all-good probability.

This result does not prove that BLAKE2s outputs are independent ideal words,
that an adversarial prover cannot choose the good set after seeing queries,
that a native Merkle opening is binding, or that the FRI agreement parameter
`alpha` holds for the committed oracle. Those are separate PCS/FRI obligations.
