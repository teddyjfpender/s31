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

The [word reduction proof](../../../formal/s31/S31/Gadgets/PcsFri/M31WordReduction.lean)
also justifies that map for the native little-endian vector path. Zig first
computes `folded = (word & p) +% (word >> 31)`, then subtracts `p` when
`folded >= p`. For every `u32` input, Lean proves the first expression is
`word % 2^31 + word / 2^31`, is at most `p+1` (so `+%` cannot overflow),
and the conditional result is exactly `word % p`. The query proof composes
this reducer equality with the low-bit mask. The separate big-endian scalar
fallback and the correctness of the BLAKE2s digest implementation are not
covered by this arithmetic theorem.

## How raw words become a query batch

The [batch schedule proof](../../../formal/s31/S31/Gadgets/PcsFri/NativeQueryBatch.lean)
indexes an arbitrary stream of eight-word blocks. Raw query slot `j` reads
block `⌊j/8⌋`, lane `j mod 8`; its output is precisely
`(word mod p) & (2^k−1)`. This equality holds for every 32-bit word and
every requested slot, including a final partial block. `drawQueries` accepts
`k=0..31`; at `k=0` every position is zero. At 70 positions, nine blocks are
drawn; the last used word is block 8 lane 5, and lanes 6–7 are discarded.
The `rawWord_blocksOfRaw` theorem also shows that every ordered raw-word
tuple can be embedded in this layout by filling unused lanes with zero.
The position list still contains repeats in draw order. Sorting and deduplication
occur later in `Queries.init`.

The [native differential](../../../formal/s31/tests/pcs_fri_native_query_batch.zig)
checks actual Zig `drawQueries` and `reduceToM31` at mask widths 0–31, batch
boundaries, repeated words, and M31 boundary values. It also compares the
selected `Blake2sM31MerkleChannel` at 70 positions to direct nine-block
drawing. The [source guard](../../../scripts/s31_formal_lib/pcs_fri_m31_query.py)
pins the eight-lane loop, reducer, selected S31 profile, and native verifier
selection. These are finite execution checks and source pins, not a proof of
Zig operational semantics for all inputs.

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

The `exact_raw_product_fraction` theorem makes the repeated-draw step a
finite counting statement. Its sample space is the set of all functions
`Fin s -> Fin 2^32`, each representing an ordered `s`-tuple of raw words.
The event includes exactly those functions whose every word maps into the
fixed good set. Its cardinality divided by the sample-space cardinality
equals `maskedMass(k, good)^s`; `exact_raw_product_*_vs_alpha` then applies
the proved one-draw bias bound to that actual fraction. This is the
uniform product sample space. Applying it to BLAKE2s transcript outputs
requires the stated independence and ideal-word assumption.

This result does not prove that BLAKE2s outputs are independent ideal words,
that an adversarial prover cannot choose the good set after seeing queries,
that a native Merkle opening is binding, or that the FRI agreement parameter
`alpha` holds for the committed oracle. Those are separate PCS/FRI obligations.
