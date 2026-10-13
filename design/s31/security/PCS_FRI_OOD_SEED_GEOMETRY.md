# Native OOD seed image and subfield boundary

**Status:** theorem correspondence open. The proven-security release gate stays
closed. This note audits the pinned engine at
`59e1f115250b8af01712b9bf3d71616e53094964` and counts field elements;
it neither proves a random-oracle distribution nor measures attack success.

The [S-two whitepaper's flat-AIR OOD round](https://eprint.iacr.org/2026/532.pdf)
samples a point outside the base-field circle. The native prover and verifier
instead draw a `QM31` seed `t`, then use the rational circle map

```text
x = (1 − t²) / (1 + t²)
y = 2t / (1 + t²)
```

`pointFromOodsSeed` rejects the two roots of `1+t²` through the checked
inverse. It does not explicitly exclude a seed in `M31` or `CM31`. The
native row quotient denominator uses only the `CM31`-extension coefficients
`x.c1` and `y.c1`:

```text
D(P) = (x.c0 − P.x)·y.c1 − (y.c0 − P.y)·x.c1.
```

For a nonexceptional `t ∈ CM31`, both `x.c1` and `y.c1` are zero, so this
denominator is zero at every base-field row. In particular, every base-field
seed maps to a base-field circle point. Whether the complete native proving
and verification paths reject each such proof at exactly the intended stage
requires an operational proof; the source-level facts alone do not establish
it.

If the seed were uniform over `QM31`, its field has `(2³¹−1)^4` elements.
There are exactly two exceptional seeds, `(2³¹−1)` base-field seeds, and
`(2³¹−1)²−2` nonexceptional quadratic-subfield seeds. The corresponding
fractions are respectively `2/q⁴`, `1/q³` (about `2^-93`), and
`(q²−2)/q⁴` (about `2^-62`), where `q=2³¹−1`. These are **seed-set
fractions conditional on uniformity**, not native failure probabilities or
soundness errors. A Fiat–Shamir attacker may choose commitment attempts and
the actual transcript distribution remains unproved.

There are also regular seeds outside `CM31` for which `y.c1=0`. Write
`t=a+bu`, with `a,b∈CM31` and `u²=R=2+i`. Taking the `u` coefficient of
`y=2t/(1+t²)` shows that `y.c1=0` exactly when `b=0` or
`a²−Rb²=1`. The norm-one equation has `q²+1` solutions because `R` is a
nonsquare in `CM31`; two have `b=0`. Removing the two exceptional roots of
`1+t²` leaves **`2q²−3` regular seeds** with `y.c1=0`, or
`(2q²−3)/q⁴` (about `2^-61`) under a uniform-seed assumption. Here `R` is
indeed a nonsquare: its norm down to `M31` is `5`, and `q mod 5=2` makes
`5` a nonsquare in `M31`. The [draft experimental paired verifier](https://github.com/teddyjfpender/stwo-zig/pull/249)
rejects this larger set before publishing the transcript state; the pinned production
path does not have that early guard. `y.c1=0` alone does **not** imply the
row quotient denominator is zero at every row, so this larger count is not
a failure count for the pinned production path.

The [source-bound diagnostic](../../../scripts/release/pcs_fri_ood_seed_geometry.py)
pins the native gitlink and six exact file hashes, checks the reviewed
sampling and denominator code, and reports these fractions as exact rational
numbers:

```sh
python3 -B scripts/release/pcs_fri_ood_seed_geometry.py
python3 -B scripts/release/pcs_fri_ood_seed_geometry.py --require-proven
python3 -B -m unittest scripts.tests.test_pcs_fri_ood_seed_geometry -v
```

The `--require-proven` command exits 2 by design. Any source change requires
a new review. The diagnostic reports no native security bits.

To use the published OOD theorem, prove the sampled point distribution and
the relationship between the rational map's exceptional/subfield cases and
the verifier's acceptance event. A proof may use rejection sampling with a
specified transcript schedule or a direct bound for the actual accepted-seed
set; it must account for any changed denominator and the complete OOD/FRI
protocol. An early rejection of subfield seeds is a useful fail-closed
implementation step, but by itself is not that theorem.
