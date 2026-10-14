# Gate to CAS07 source roster: an audit boundary

The experimental [CAS07/XDM05 draft](https://github.com/teddyjfpender/stwo-zig/pull/269)
can represent sparse source heights, including the Gate profile with ten empty
interior heights. That fact alone does not make CAS07 a verifier for a Gate
proof. The [source-pinned audit](../../../scripts/release/pcs_fri_cas07_gate_roster.py)
derives the proposed XDM05 column order from one sealed Gate package, its
native `check-key` result, and a reviewed CAS07 commit. It produces an audit
digest and always reports `production_equivalent=false` and
`native_proven_security_bits=null`. `--require-production-equivalent` exits 2.

## Exact checked profile

One reviewed Gate package has 45 preprocessed, 114 main, 152 interaction,
and 8 composition columns. The proposed CAS07 source roster flattens the
first three trees in this order at each height: fixed columns in commitment
order, then each component's main columns in proof order, then its
interaction columns in proof order. It has 311 source columns:

| Source log size | XDM05 height | Fixed + main + interaction columns |
| ---: | ---: | ---: |
| 20 | 0 | 51 |
| 18 | 2 | 8 |
| 16 | 4 | 15 |
| 14 | 6 | 8 |
| 9 | 11 | 28 |
| 8 | 12 | 8 |
| 4 | 16 | 193 |

All other positions in `H=17` have **zero** columns. XDM05 uses an ordinary
upper-parent hash at each absent insertion height; a present all-zero
column would have different commitment bytes. With `k=20`, illustrative
`beta=2` and 232 raw queries, the visible profile caps pass: 56,708,112
source field words, 293,941,280 source-plus-tree estimated bytes, and
578,144 fixed source query-payload bytes before Merkle witnesses and wire
headers. The two-coefficient
terminal shape follows from `2^(k-H-beta)=2`. These are the draft's source
tree geometry, not a whole-prover memory bound or a proven security setting.
The **draft synthetic pilot**, measured once on an Apple host, reported about
4.0 seconds to prove and a 1.22 MB proof. It used easy nonconstant columns,
not the Gate AIR witness; these observations do not estimate production cost.

The heights are **program dependent**. A fresh locally sealed `arith4_m31`
package still has 45/114/152/8 total columns, but its 28-column group is at
log size **10**, rather than 9. The exact-profile checker rejects that
package until a separate CAS07 pilot and review of its derived roster are
recorded. A hard-coded height list cannot be used as authority for every
generated Gate program.

## Why the metadata is not a proof migration

The current verifier has four commitments and challenge-dependent epochs:

```text
preprocessed root -> public/circuit values -> main root
                 -> interaction PoW and lookup challenge
                 -> interaction claims and interaction root
                 -> AIR random coefficients and composition root
                 -> OOD, FRI, queries

CAS07 draft: one XDM05 source root -> OOD and claims -> folds and queries
```

The draft's 311-column root omits the **eight composition columns**. It also
asks the main and interaction columns to share one source root despite their
distinct production transcript epochs. Moving an interaction column before
its lookup challenge would change what the prover is allowed to condition on;
moving a composition column before AIR coefficients has the same problem.
No existing proof can be translated to this root merely by concatenating
column vectors. A production path needs a multi-epoch commitment protocol
with its own theorem, or a proved transcript-preserving adapter, and must
include composition at its correct epoch. The installed key must reconstruct
the roster and exact row values; the audit's digest binds only metadata and
cannot authenticate an XDM05 row or claim.

## Published batching width is still unknown

For the [S-two whitepaper's multi-domain batching theorem](https://eprint.iacr.org/2026/532.pdf)
(see the [official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)), a **hypothetical**
substitution `N=2^20`, `B=2`, `|QM31|=(2^31-1)^4` gives
`(M-1)NB²/|QM31|`. The exact-arithmetic audit reports:

| Assumed paper `M` | Batching expression | Can this expression alone fit `2^-96`? |
| ---: | ---: | :---: |
| 152 | approximately `2^-94.762` | No |
| 311 | approximately `2^-93.724` | No |
| 319 | approximately `2^-93.687` | No |

The actual paper `M` is **unidentified**. Neither a production tree width nor
the number of candidate source columns determines the full original,
own-quotient, and composition ensemble's batch width. If a proved mapping
establishes `M>=65` at this `N,B`, this particular published upper-bound
expression already exceeds the selected `2^-96` work-factor target before
other positive terms. That is a certificate feasibility statement, not a
lower bound on attack success. Changing queries alone does not reduce this
batching expression. The selected adversary hash-query budget remains
`T=2^64`; the native BCS/ROM composition is also unproved.

## Next proof interfaces

1. Bind compiler-owned columns, ordered row values, source root, OOD claims,
   and composition to one installed key and a specified multi-epoch transcript.
2. Prove accepted XDM05 row custody for every sparse height, including
   hash-upper gaps and H=1, against fixed committed oracles; refine native
   bit-reversed rows and inverse arithmetic to the Lean model.
3. Derive the paper's `M,N,B` and the two-point quotient filtration from the
   actual source/quotient/composition ensemble, then prove correlated common
   agreement across its domains.
4. Compose query sampling, Merkle/Blake2s BCS, PoW, and all paper round errors
   at `T=2^64`, leaving the production gate closed until the selected
   `epsilon(T)/T <= 2^-96` claim is proved.

For a locally trusted Gate package and the exact reviewed stwo-zig draft
checkout, run:

```sh
python3 -B scripts/release/pcs_fri_cas07_gate_roster.py \
  /path/to/gate-package /path/to/stwo-zig-cas07-checkout
python3 -B scripts/release/pcs_fri_cas07_gate_roster.py \
  /path/to/gate-package /path/to/stwo-zig-cas07-checkout \
  --require-production-equivalent
```

The second command must fail. A changed candidate commit or any reviewed
source byte, Gate key, component order, width, or height also fails closed.
