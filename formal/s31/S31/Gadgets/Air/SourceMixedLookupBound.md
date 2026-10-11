# Mixed lookup occurrence bound

`SourceMixedLookupBound.lean` counts the ideal signed event lists for the
source-pinned 512-row mixed program family. It sits between the typed
`SourceMixedPath` boundary and the generic seven-coordinate challenge lemma.

For a call count `N` from one through eight, the `SourceShape` contract says:

| Source fact | Value |
| --- | ---: |
| Arithmetic Gate rows | 512 |
| Sum of output lookup multiplicities | `1033 + 8N` |
| Baseline Gate uses and yields | zero |
| Chip rows per call | 16 |
| Public Gate uses | 9 |
| Bridge Gate uses | `8N` |

The sum of Gate output multiplicities is **not** the number of distinct
producer rows. It counts repeated reads of the same produced value. For
example, the exported N=1 and N=8 fixed columns sum to 1041 and 1097,
respectively. The native producer-roster test checks all N=1..8 family
instances, but the Lean `SourceShape` proposition remains a correspondence
premise until those native results are tied to the authenticated verifier
trace and the Lean `Boundary`.

The Lean proof derives both ideal closure list lengths:

```text
Gate uses:    2·512 + 9 + 8N = 1033 + 8N
Chip uses:                   17N
Gate yields: 1033 + 8N
Chip yields:                 17N
Each side:    1033 + 25N <= 1233 < p = 2147483647
```

Every occurrence count for a single tuple is therefore below `p`. The
theorem also proves each list entry is either a Gate tuple with a canonical
`Fin p` address or a tagged chip tuple. The generic challenge proof then
gives at most `36,491,868 · |QM31|` exceptional pairs out of `|QM31|²` for
this ideal roster. The factor follows from at most `2·1233 = 2466`
distinct tuples and the conservative `6s² + 2s` lemma. This is strictly
smaller than the pair space. The `imbalancePairs7` version has an **empty**
error set for exactly balanced lists, so it is meaningful for honest traces.

This bound concerns the algebraic false-closure event for fixed lists and
ideal independent challenges. It does not prove that native verifier
acceptance implies these lists, that the verifier enforces all AIR fractions,
or that its Fiat–Shamir challenges are independent. Native bridge fractions
are repeated across sixteen trace rows; the ideal lists used here count the
telescoped endpoint relation. The larger whole-AIR lookup budget in
`design/s31/security/LOOKUP_COMPRESSION_BUDGET_2026-10-11.md` counts every
bridge row separately and is a different envelope.
