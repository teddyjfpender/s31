# Lookup compression budget for a general circuit-to-chip boundary

Status: algebraic audit worksheet, **not** a security claim for the current
native profiles. This isolates one failure event in the Gate/chip LogUp join;
AIR, PCS/FRI, Fiat–Shamir, and proof-of-work soundness need their own bounds.

## What is sampled

The pinned prover commits the main trace and mixes an interaction proof-of-work
nonce; the verifier checks and mixes that nonce. Both then draw `z` and
`alpha` as two QM31 challenge elements.
A tuple `t = (t_0, ..., t_d)` is mapped to

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
`alpha`. Represent each emitted lookup tuple by its coefficient vector,
zero-padded to the maximum arity. Let `T` count distinct such vectors over
all Gate, chip, and bridge events. Require this padded-vector encoding to be
injective for intended distinct event identities: `(a,b)` and `(a,b,0)`
otherwise compress identically for every `alpha`. The current fixed profile
separates six-coordinate Gate and seven-coordinate chip events with distinct
first-coordinate relation IDs. Matching producer/consumer events use the
same vector with opposite signs. Require checked total event occurrences
`< p = 2^31 - 1`, or prove each nonzero signed imbalance has absolute value
`< p`, so it stays nonzero modulo the field characteristic.

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

### An envelope from the current bounded geometry

For the proposed 1–8-call pair/many schedule, the existing `Plan.validate`
caps circuit rows at `2^16`, the sum of chip rounds at `2^18`, and calls at
eight. **The numeric ceiling also requires source admission to cap the public
output shape at eight words plus the reserved `u` wire.** The fixed N=4
profile checks that shape; `Plan.validate` alone does not, and the general
1–8-call native verifier still needs this check. The direct circuit emits
three Gate lookup occurrences per row. Each
tagged chip emits two endpoint occurrences per round. A bridge has 16 rows;
each row contributes eight Gate and two tagged chip denominator terms. The
public statement contributes at most eight output terms plus the `u` term.
Counting every bridge row separately, even though its AIR should force equal
endpoints across rows, gives the conservative envelope

```text
E <= 3 * 2^16 + 2 * 2^18 + (8 + 2) * 16 * 8 + (8 + 1)
  = 722185 occurrences.
T <= E.
```

The multiplicity budget needs a separate count. Write `R = G + 2P` for
`G` arithmetic gates and `P` permutation pairs, `S` for total chip rounds,
`N` for calls, and `O <= 9` for at most eight public words plus `u`.
`CircuitView.computeUses` counts at most `2G + P + O` wire uses. The direct
preprocessor adds `2P` uses of the zero wire and `8N` bridge endpoint uses.
The circuit's output lookup weight is drawn from these checked counts;
its `P` synthetic permutation wires add weight one each. Thus the total
absolute weight of circuit lookup terms is bounded by
`2R + (2G + 4P + O + 8N) = 4R + O + 8N`.
The chip contributes `2S` unit weights and the public statement `O` more.
Every one of the `10 * 16 * N` bridge row terms has weight `1/16` in
magnitude. Multiplying the whole closure equation by 16 therefore gives
an **integer** coefficient for every distinct tuple with total absolute
weight at most

```text
B = 16 * (4R + 8N + 2O + 2S) + 10 * 16 * N
  <= 16 * (4 * 2^16 + 8 * 8 + 2 * 9 + 2 * 2^18) + 10 * 16 * 8
   = 12585504 < p = 2147483647.
```

Consequently, under these checked source geometry and multiplicity rules,
no nonzero integer tuple imbalance can disappear only by reduction modulo
`p`. This argument counts a malicious bridge row independently and does not
use its row-constancy constraint. It still relies on the live AIR to enforce
each row's fraction equation and on the source-derived preprocessed counts;
the arithmetic bound by itself authenticates neither.

Substituting this ceiling into the conditional formula above gives an
algebraic error ceiling below `2^-83.49`, subject to the stated AIR and
uniform-challenge premises and the weighted bound above. This is not an
independent bridge-soundness proof or a blanket bound for every S31
program or future chip kind. The native N=3 and N=4 profiles use smaller
source-derived counts; the 1–8-call native proof scheduler is still pending.
The factors come from `private_many_boundary.Plan.validate`,
`components.qm31_ops.n_lookups`, `tagged_pair_chip.FillContext.fill`,
`tagged_pair_bridge.FillContext.fill`, and `witness.trace.lookupSum` in the
pinned engine. Any change to those emitters or caps requires recomputing this
envelope before using it in a release budget.
The release admission gate must enforce `source.output.len <= 9` and its
profile's exact public-word shape before applying these numeric ceilings.

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
4. The field sampler rejects 32-bit words at least `2p` before reduction;
   under ideal uniform hash output this gives uniform M31 limbs and hence
   uniform QM31 challenges. The transcript's grind step and any correlation
   from adaptive prover queries still belong in the final Fiat–Shamir
   argument. This worksheet assumes ideal independent draws.
5. The final error budget adds the committed-AIR/PCS/FRI and hash assumptions
   separately. It must not report this algebraic term as total proof security.

Sources in the pinned engine revision: `core/channel/lookup_transcript.zig`
draws the challenges; `integrations/circuit_cpu/private_pair_boundary.zig`
defines the seven-coordinate tagged compression; and
`integrations/circuit_cpu/direct_mixed_four_arithmetic.zig` commits main columns
before drawing lookup challenges and installs ordered claimed sums.
