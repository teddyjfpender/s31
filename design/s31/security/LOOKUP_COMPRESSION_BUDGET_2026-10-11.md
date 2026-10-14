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

## Conditional algebraic bounds

Fix all tuple occurrences and signed multiplicities **before** sampling
either `z` or `alpha`. Represent each emitted lookup tuple by its coefficient
vector, zero-padded to the maximum arity. Let `T` count distinct such vectors over
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

This is a valid but deliberately conservative decomposition: it counts any
pairwise compressed-key collision as a failure, even when that collision does
not make the **whole** false lookup equation vanish. If `T = 524288`, its
collision term alone is about `2^-84.4`.

### Direct two-challenge bound

There is a sharper bound for this same fixed, signed tuple imbalance; it does
not require separate relation challenges or tuple structure beyond the
injective tagged encoding above. Let `f_i(X)` be the distinct coefficient
polynomials of the `T` vectors after
combining repeated vectors, and let `m_i` be their integerized signed
multiplicities reduced into the characteristic-`p` subfield. Here `T >= 1`;
at least one `m_i` must be nonzero. Define polynomials over `QM31`:

```text
D(X,Z) = product_i (f_i(X) - Z)
H(X,Z) = sum_i m_i * product_(j != i) (f_j(X) - Z).

When D(alpha,z) != 0, the false closure equation is H(alpha,z) = 0.
```

`H` is **not the zero polynomial**. Choose `k` with `m_k != 0` and substitute
`Z = f_k(X)` as a polynomial identity. Every term except `k` vanishes, while

```text
H(X, f_k(X)) = m_k * product_(j != k) (f_j(X) - f_k(X)) != 0.
```

The last inequality uses distinct *formal* coefficient polynomials and the
fact that `QM31[X]` has no zero divisors. With maximum tuple degree `d = 6`,
each factor `f_j(X) - Z` has total bivariate degree at most six, so
`deg_total(H) <= 6(T - 1)`. Schwartz–Zippel on **independent uniform**
`(alpha,z) in QM31^2` bounds its zero probability by `6(T - 1)/q`.
Separately, for every fixed `alpha`, at most `T` choices of `z` zero a
denominator, giving probability at most `T/q`. Therefore the false closure
or undefined-fraction event has the conditional algebraic bound

```text
epsilon_lookup <= [6(T - 1) + T] / q = (7T - 6) / q.
```

More generally, for tuples of degree at most `d`, replace six by
`max(d, 1)`. This direct bound subsumes the collision case: a collision can
make `H` vanish at that sampled `alpha`, but the exceptional **pair of
challenges** still lies in the zero set of the one nonzero polynomial `H`.
The earlier `O(T^2/q)` bound remains an independent conservative cross-check.

For a small exact check, take `F_5`, `f_1(X)=0`, `f_2(X)=X`, and weights
`(1,-1)`. Then `H(X,Z)=X`. There are nine challenge pairs with a zero
denominator and four more with `alpha=0`, `z!=0`, where the false closure
holds: 13 bad pairs out of 25. The direct ceiling is
`[1*(2-1)+2]/5 = 15/25` for degree one. This example also shows why simply
discarding compressed-key collisions would be unsound.

The actual release budget still needs the source-derived maximum `T` for
each admitted profile, including every committed Gate row and chip round.
Counting just boundary endpoints would be incorrect. In particular, the
direct proof fails if an adversary can choose tuple coefficients or
multiplicities after seeing either challenge, if semantically different
relation tuples share the same padded coefficient polynomial without a
structural tag, or if all nonzero integer imbalances can vanish modulo `p`.
For the latter two failures, `(a,b)` versus `(a,b,0)` can cancel at **every**
challenge without a tag, and a single integer imbalance of `p` becomes zero
in the field. The checked `B < p` envelope below excludes the latter for
the proposed bounded profile, once its other premises are enforced. The
pre-challenge commitment is essential too: after observing `alpha`, an
adversary allowed to choose new base-field tuple coefficients could use the
minimal polynomial of `alpha` over `M31` (degree at most four), multiplied
by `X` to retain a fixed constant relation tag. The resulting nonzero tuple
difference has degree at most five and compresses to zero at that challenge.

### An envelope from the current bounded geometry

For the proposed 1–8-call pair/many schedule, the existing `Plan.validate`
caps circuit rows at `2^16`, the sum of chip rounds at `2^18`, and calls at
eight. **The numeric ceiling also requires source admission to cap the public
output shape at eight words plus the reserved `u` wire.** The fixed N=4
profile checks that shape; `Plan.validate` alone does not. The isolated
general 1–8-call draft checks exactly nine output addresses in both prover
and verifier, but has not passed native admission yet. The direct circuit emits
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

Substituting `T <= 722185` into the direct conditional formula gives
`(7T-6)/q <= 5055289/q < 2^-101.73`. The older collision-decomposition
formula gives a conservative ceiling below `2^-83.49`. These are bounds on
the **same algebraic event**, not independent error terms to add. They are
subject to the stated AIR, fixed-trace, uniform-challenge, and weighted
imbalance premises. This is not an independent bridge-soundness proof or a
blanket bound for every S31 program or future chip kind. The native N=3 and
N=4 profiles use smaller
source-derived counts; the isolated 1–8-call native proof scheduler remains
uncompiled and unadmitted.
The factors come from `private_many_boundary.Plan.validate`,
`components.qm31_ops.n_lookups`, `tagged_pair_chip.FillContext.fill`,
`tagged_pair_bridge.FillContext.fill`, and `witness.trace.lookupSum` in the
pinned engine. Any change to those emitters or caps requires recomputing this
envelope before using it in a release budget.
The release admission gate must enforce `source.output.len <= 9` and its
profile's exact public-word shape before applying these numeric ceilings.
The isolated general profile now has an executable candidate gate in
`src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig`: source inspection
checks exactly nine circuit output addresses, power-of-two circuit rows and
chip rounds, live circuit/chip/bridge trace sizes, the checked `E` count,
and `B < p`. `registry_manifest.fromSchedule` rechecks the derived counts
before the general package selects its proof identity. This candidate still
requires native compilation and rejection tests before release. The envelope
does not add its algebraic term to a measured AIR/PCS/FRI/Fiat–Shamir budget.

## Conditions to check in the implementation

1. The manifest or registry supplies a checked upper bound on **distinct**
   event tuples and total occurrences for each source-derived component
   roster. Dynamic dimensions and multiplicities use checked arithmetic.
2. The main commitment fixes all tuple coordinates and the signed occurrence
   weights before the challenge draw; the source-selected roster and relation
   tags are fixed too. A tuple or weight selected after seeing `alpha` or `z`
   invalidates the bivariate-polynomial argument.
   Every interaction fraction and claimed sum is constrained in its live AIR;
   a closure sum by itself does not establish this.
3. The same tuple is used on both sides of each intended join; unrelated
   events are structurally tagged before compression. Repeated Gate addresses
   keep every occurrence and its signed multiplicity.
4. The selected field sampler reduces raw BLAKE2s words modulo `p` before
   its later `>=2p` check, so the latter never rejects. Even under ideal
   independent raw words, M31 residues `0` and `1` have three preimages and
   others have two; the resulting QM31 challenges are biased. This worksheet's
   uniform-challenge bounds are conditional algebraic results, not native
   Fiat–Shamir bounds. A final argument must handle that bias, the grind step,
   and adaptive prover queries.
5. The final error budget adds the committed-AIR/PCS/FRI and hash assumptions
   separately. It must not report this algebraic term as total proof security.

Sources in the pinned engine revision: `core/channel/lookup_transcript.zig`
draws the challenges; `integrations/circuit_cpu/private_pair_boundary.zig`
defines the seven-coordinate tagged compression; and
`integrations/circuit_cpu/direct_mixed_four_arithmetic.zig` commits main columns
before drawing lookup challenges and installs ordered claimed sums. The draft
`direct_mixed_general_arithmetic.zig` uses the same ordering for dynamic
`1+2N` rosters; its native proof tests are still a release gate.
