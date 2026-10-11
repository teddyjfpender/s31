# Lookup compression budget for a general circuit-to-chip boundary

Status: algebraic audit worksheet, **not** a security claim for the current
native profiles. This isolates one failure event in the Gate/chip LogUp join;
AIR, PCS/FRI, Fiat–Shamir, and proof-of-work soundness need their own bounds.

## What is sampled

The pinned engine draws `z` and `alpha` as two QM31 challenge elements after
the main trace commitment. A tuple `t = (t_0, ..., t_d)` is mapped to

```text
f_alpha(t) = t_0 + alpha*t_1 + ... + alpha^d*t_d
denominator(t) = f_alpha(t) - z
```

Gate tuples have six coordinates; the current tagged mixed-chip tuples have
seven, so `d <= 6`. `QM31` has `q = (2^31 - 1)^4`, just under `2^124`, elements.
This worksheet treats both challenges as independent uniform field elements.
For the real hash transcript that is a Fiat–Shamir/random-oracle premise, not
a theorem established here.

## A conditional bound

Fix all tuple occurrences and signed multiplicities **before** sampling
`alpha`. Let `T` be the number of distinct canonical tuples, including every
Gate, chip, bridge, call, and relation tag. Require their signed multiplicity
coefficients to retain their intended nonzero values modulo the field
characteristic; in particular, checked occurrence counts must stay below
`p = 2^31 - 1`. Require distinct event kinds to have different canonical
tuple encodings, while matching producer/consumer events use one encoding
with opposite signs.

For two distinct tuples, their compressed-key difference is a nonzero
polynomial in `alpha` of degree at most six. The union bound gives

```text
Pr[any compressed-key collision] <= 6 * binom(T, 2) / q.
```

Conditioned on no collision, an imbalanced multiset gives a nonzero rational
function `F(z) = sum_t m_t / (f_alpha(t) - z)`. After a common denominator its
numerator has degree at most `T-1`; its denominator has at most `T` zeros.
Thus a conservative additional bound for a false zero or undefined fraction
at uniform `z` is `(2*T-1)/q`. Together, this **algebraic part only** is at
most

```text
epsilon_lookup <= [6 * binom(T, 2) + 2*T - 1] / q.
```

The bound is deliberately conservative. If `T = 524288`, its collision term
alone is about `2^-84.4`; `q` being nearly 124 bits does not make this a
124-bit lookup argument at that size. The actual release budget needs the
source-derived maximum `T` for each admitted profile, including every
committed Gate row and chip round. Counting just boundary endpoints would be
incorrect. A tighter argument may exploit tuple structure or independent
relation challenges, but must be proved for the implemented transcript.

## Conditions to check in the implementation

1. The manifest or registry supplies a checked upper bound on **distinct**
   event tuples and total occurrences for each source-derived component
   roster. Dynamic dimensions and multiplicities use checked arithmetic.
2. The main commitment fixes all tuple coordinates before the challenge draw.
   Every interaction fraction and claimed sum is constrained in its live AIR;
   a closure sum by itself does not establish this.
3. The same tuple is used on both sides of each intended join; unrelated
   events are structurally tagged before compression. Repeated Gate addresses
   keep every occurrence and its signed multiplicity.
4. The exact `drawSecureFelts` distribution, the transcript's grind step, and
   any correlation from adaptive prover queries are included in the final
   Fiat–Shamir argument. This worksheet assumes ideal independent draws.
5. The final error budget adds the committed-AIR/PCS/FRI and hash assumptions
   separately. It must not report this algebraic term as total proof security.

Sources in the pinned engine revision: `core/channel/lookup_transcript.zig`
draws the challenges; `integrations/circuit_cpu/private_pair_boundary.zig`
defines the seven-coordinate tagged compression; and
`integrations/circuit_cpu/direct_mixed_four_arithmetic.zig` commits main columns
before drawing lookup challenges and installs ordered claimed sums.
