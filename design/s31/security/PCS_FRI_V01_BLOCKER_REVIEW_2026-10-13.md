# v0.1 PCS/FRI published-proof admission review

**Decision: blocked for a proven-security release claim.** The existing
26-bit PCS PoW, blowup-2, 70-query tuple is a nominal work-plus-query score.
Changing query count, blowup or PoW alone cannot discharge the missing
protocol and cryptographic reductions. This review does not estimate an
attack probability or claim a native soundness theorem.

The machine-readable [blocker matrix](pcs-fri-v01-blockers.json) covers all
12 v0.1 audit profile/schedule rows. It binds partial evidence files by
SHA-256 and the native engine gitlink, records exact open obligations, and
marks every profile's `native_proven_security_bits` as `null`. The generator
checks the audit roster independently, and `--check` fails if the snapshot or
evidence changes:

```sh
python3 -B scripts/release/pcs_fri_v01_blockers.py --check
python3 -B scripts/release/pcs_fri_v01_blockers.py --check --require-admissible
```

Each `gap_kind` separates an uninstantiated published theorem premise from
an unproven native correspondence, cryptographic reduction, or unmatched
protocol schedule. These are open proof interfaces, not estimated security
bits or completion percentages. No currently warranted published-proof
conservative profile was found; proven v0.1 admission remains fail closed.

The second command deliberately exits 2 while any obligation remains open.
The [published-bound preflight](../../../scripts/release/pcs_fri_proven_preflight.py)
still reports useful **necessary** arithmetic for an illustrative geometry;
it never treats that arithmetic as a native certificate.

## Published theorem interface

The primary [Circle STARKs paper, Appendix B, Theorems 6 and 7](https://eprint.iacr.org/2024/278.pdf)
analyses an interactive batch circle-FRI proximity protocol and an AIR IOP.
Theorem 6 needs a standard position coset, finite degree/rate parameters,
single-fold round relation, independently uniform queries from a fixed
consistency set, and its commitment/folding error in addition to the query
term. Its Johnson agreement is
`alpha = (1+1/(2m))*sqrt((N+1)/|D|)` with `m>=3`; the query term is
`alpha^s`. Theorem 7 additionally accounts for AIR composition and OODS
failure terms. The current preflight calculates this query term and an
outward interval for one leading commitment-error envelope term. It has no
per-package `C`, `d`, `L`, component-height or full error substitution.

The primary [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf), with
an [official theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md),
provides the closer multi-domain target: flat-AIR IOPP soundness,
cross-domain correlated agreement, multi-domain circle FRI, degree-corrected
batch evaluation, and a BCS/Fiat–Shamir transformation. The map records
setup conditions including `deg(A)<=B+1`, `N*B^2<=2^30`, and a
small-table degree-correction condition. Its NIROP error includes an
adversary-budget term of the form `(T+R)*max_i epsilon_i` plus a hash
collision term. A source-level resemblance to that protocol is insufficient:
the native verifier needs a complete relation-preserving refinement and
every concrete parameter needs to satisfy the theorem's premises.

The source-visible nominal v0.1 tuple is `pow_bits=26`,
`log_last_layer_degree_bound=0`, `log_blowup_factor=1`, and `raw_queries=70`.
The S31 runtime chooses fold step 1 or 4; the three SHA package runtimes use
fold step 1. The blocker generator pins the exact constructor calls and their
source hashes. Package-specific `N`, `D`, `C`, degree and component height
remain unbound, so this tuple is not a theorem parameter substitution.

The pinned Zig source and Lean models now provide useful **local** bridges:
raw M31 reduction and query-mask arithmetic, exact finite product-space
query bias, query order/custody, projected index geometry, Merkle path
reconstruction, local fold algebra, and modeled layer acceptance. They do
not prove that the actual transcript emits independent ideal words, that
all native committed columns define the modeled fixed good set, that the
whole multiproof decoder implements the model, or that all native FRI rounds
and DEEP quotients instantiate either paper's protocol. The exact missing
interfaces are P01–P09 in the matrix. P10 additionally blocks the two
four-fold profiles because one challenge is reused across a grouped fold
round; the single-fold paper theorem does not cover that schedule as-is.

The [raw-query epoch audit](../../../scripts/s31_formal_lib/pcs_fri_query_epoch.py)
closes one bounded-counter subcase of P07 for the pinned engine. The verifier
absorbs the verified PoW nonce with `mixU64`, which resets `n_draws` through
`mixU32s` and `updateDigest`; it then samples 70 raw queries with one
`drawU32s` per eight output words. The nine hash inputs use distinct
little-endian counters 0 through 8, so this epoch cannot wrap a u32 counter.
Mutation tests guard the reset, query forwarding and draw loop. The newer
pinned engine also uses a checked u32 increment in `drawU32s` and traps before
overflow, including inside the unbounded `drawSecureFelt` rejection loop.
This prevents that channel from returning a block after its counter would
wrap; it does **not** bound the running time of a rejection loop or formally
link every selected native verifier path to the checked channel. It also does
not establish independent random-oracle words, BLAKE2s security, grinding
soundness or a Fiat–Shamir reduction. P07 remains open.

The `N=512`, blowup-2, `m=3`, `s=70` example in the preflight is illustrative.
Its Johnson query term alone fails a 96-bit target, and the preflight finds
348 ungrinded queries for that term alone. This is **not** a recommended
native setting: the commitment, AIR, OODS, Merkle and ROM terms still need a
bound, and larger `s` has proof-size and prover-time costs. The native
`securityBits()` sum must be read as a nominal score.

## Independent whole-prover cost review

The [V8r1 result](../measurements/WHOLE_PROVER_V8R1_RESULT.md) is a useful
qualified local measurement: 23 training packages, 20 held-out packages,
4,300 native trials, and a second-source held-out check on one M5 Max host.
Its original frozen evaluator failed before scoring because of a case-name
mismatch; a reviewed roster-only post-freeze bridge then produced passing
local gates. The result explicitly keeps automatic lowering disabled.

That evidence pins engine `7d544c6839497ca19b6c7ef9b982e464f10cfeed`;
the current v0.1 matrix pins `039dacb59980e1e871571958b396b2e29f93c0e5`.
No current-stack transfer, cross-host accuracy, tail latency, or automatic
lowering result follows from the frozen study. The [mixed stage cost
protocol](../measurements/MIXED_STAGE_COST_MODEL_V1.md) further exposes
opaque native setup/prove intervals and reports package build wall separately;
its narrow record-family fit is not a general source-to-proof predictor.
There is also no soundness-equivalent S31/Cairo speed comparison until the
two systems' verified security profiles are justified on comparable terms.

The cost limits are a separate measurement claim from the cryptographic
release blockers. They do not turn an accepted native test proof into a
published soundness result, and the security blockers do not erase the
scoped measurements that were actually made.
