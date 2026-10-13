# CAS05 conservative-profile capacity decision

**Decision as of 2026-10-13:** keep CAS05 outside release admission. No native
PCS/FRI security bits are established. The [S-two whitepaper's published
unique-decoding and BCS bounds](https://eprint.iacr.org/2026/532.pdf) permit
an *idealized* 96-bit **work-factor** calculation in QM31, but the same
one-table geometry cannot achieve an **absolute** 96-bit bound at an
adversary hash-query budget `T=2³²` with QM31 and zero proved grinding
credit. A hypothetical degree-six extension is the first *even-degree*
field size that clears the nonquery terms for this illustrative geometry;
it has no native implementation or theorem correspondence.

This diagnostic reuses Protocol 4's **single-point** OOD numerator and
support. CAS05 implements a conjugate two-point quotient; Section 4.5's
candidate support excludes `C(CM31)`, and its Eq. 80 uniqueness and bad-set
bounds still need rederivation. None of the numerical rows below is a bound
for CAS05 itself.

The [official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
specifies `F ⊇ 𝔽_(q²)`, the unique-decoding fold and query expressions,
and the BCS/ROM formula. Here `q=2³¹−1` and an even degree `d` gives
`|F|=q^d` and `|C(F) \ C(𝔽_q)|=q^d−q−2`. Odd degrees do not contain the
required quadratic subfield; the checker rejects them. It assigns no PoW
credit and uses the paper's unguarded OOD point set. CAS05's actual `y.c1`
guard, proved so far only for the QM31 tower model, needs a new finite-field
and transcript reduction for any changed field.

## Exact reproducible calculation

The input [fixture](../../../scripts/release/fixtures/cas05_one_table_paper.json)
is a deliberately small **paper protocol**: one table of `N=2²⁰` rows,
`B=2`, one constraint, one use and yield, batch width two,
`θ=16383/65536`, `T=2³²`, and 256-bit hash outputs. It declares `R=26`,
the full-roster round count; retaining it for the eight-fold short cascade
is a conservative arithmetic overcount, not a measurement of native rounds.
For `D₀=NB²=2²²`, eight folds leave 8192 terminal coefficients on 16384
evaluation points. The paper's variable-round Protocol 3 allows this
terminal shape. Neither that shape nor the one-table fixture describes a
source-bound installed CAS05 key.

Run:

```sh
python3 -B scripts/release/pcs_fri_cas05_field_capacity.py \
  scripts/release/fixtures/cas05_one_table_paper.json --height-count 8
python3 -B scripts/release/pcs_fri_cas05_field_capacity.py \
  scripts/release/fixtures/cas05_one_table_paper.json --height-count 8 --require-proven
```

The second command exits 2 regardless of the arithmetic. All comparisons
use `Fraction` and integer powers; the code scales the paper's QM31 flat-AIR,
batching and selected fold numerators to each hypothetical `q^d`, replaces
the OOD denominator by `q^d−q−2`, and keeps the exact 256-bit collision term.
It checks the QM31 row reproduces the existing ledger unchanged. `R≥13`
is required for the idealized eight-fold schedule; the worked result uses
`R=26` throughout.

| `d` | Field status | Nonquery expression meets absolute `2⁻⁹⁶`? | Least queries for absolute 96 if nonquery fits | Least queries for paper work-factor 96 if nonquery fits |
| ---: | --- | :---: | ---: | ---: |
| 2 | Hypothetical CM31 | No | Impossible by this expression | Impossible by this expression |
| 4 | Native QM31 field, hypothetical CAS05 theorem | No | Impossible by this expression | 232 |
| 6 | No native field/protocol | Yes | 309 | 232 |
| 8 | No native field/protocol | Yes | 309 | 232 |

The target meanings are distinct:

```text
absolute:          ε(T) ≤ 2⁻⁹⁶
paper work factor: ε(T)/T ≤ 2⁻⁹⁶
ε(T) ≤ (T+R) max(round errors) + 3(T²+1)/2²⁵⁶.
```

At `d=4`, the first fold alone is `3·2²¹/q⁴`; multiplying by `T+26`
exceeds `2⁻⁹⁶` independently of query count. This is an obstruction in
the **quoted upper-bound expression**, not an attack lower bound. At `d=6`,
the nonquery expression fits, while the query term requires 309 draws for
the selected `θ` and `R`. The CLI fixture has 232 draws so it still fails
the absolute target; changing only its query count to 309 makes the
**hypothetical expression** pass. This does not certify native soundness or
make 309 a universal count for other AIRs, batch widths or trace heights.

## Engineering consequence

First finish the actual CAS05 verifier-to-paper Protocol 3/4 relation,
including all authenticated values, degree-corrected original-plus-quotient
oracles, conditional OOD support, native query law and a quantified BCS/ROM
reduction. Extract `N`, widths, multiplicities, `R`, and a defensible `T`
from the final program/key and threat model. Then choose the security claim
explicitly. If the release requires absolute 96 bits at `T=2³²` under the
quoted zero-credit bound, prototype a larger even-degree challenge field;
degree six is the minimum size that passes **this** fixture, while a
quadratic extension of existing QM31 would have degree eight and may be
simpler to implement. Measure both before fixing the release profile. If
the target is the paper's work-factor convention, QM31 remains numerically
possible only after the protocol correspondence and 232-query scale are
actually established. The current 70-query production PCS satisfies neither
diagnostic.

Focused check:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_cas05_field_capacity -v
```
