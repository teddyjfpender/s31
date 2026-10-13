# Gate PCS/FRI: feasibility of a proven conservative profile

The user selected a **proven conservative** v0.1 profile. The current sealed
`affine_guard` gate uses blowup `B=2`, `s=70` raw query draws, 26 native PoW
bits, fold step 1, a maximum trace domain of `2^20`, and a conditional first
FRI domain of `2^21`. The [gate error ledger](PCS_FRI_GATE_ERROR_LEDGER.md)
extracts these facts from a locally trusted package and keeps every native
theorem parameter and security claim blocked. This note asks a narrower
question: can the **published proven Johnson-regime query envelope** even
reach a 96-bit target with those numbers?

Run the [exact arithmetic diagnostic](../../../scripts/release/pcs_fri_gate_conservative_feasibility.py)
against a locally trusted sealed gate package:

```sh
python3 -B scripts/release/pcs_fri_gate_conservative_feasibility.py /path/to/sealed-gate-package
python3 -B scripts/release/pcs_fri_gate_conservative_feasibility.py /path/to/sealed-gate-package --require-proven
```

The second command exits 2. The first executes the package's native
`check-key` command and checks the source-bound gate geometry. Package hashes
only establish internal consistency; they do not authenticate the executable,
prove that a native proof verifies, or discharge any cryptographic theorem
premise. The tool never modifies the production FRI tuple.

## The obstruction, by hand

The [S-two whitepaper's proven Johnson regime](https://eprint.iacr.org/2026/532.pdf)
has rate `rho=1/B` and proximity `theta < 1-sqrt(rho)`. Its query-round
error expression is `(1-theta)^s`. Therefore, for every allowed `theta`,

```text
(1-theta)^s > B^(-s/2).
```

At `B=2`, `s=70`, the **published expression** is strictly greater than
`2^-35`. Even granting a hypothetical, fully justified 26-bit query-phase
grinding discount gives an expression strictly greater than `2^-61`. Neither
can certify an upper bound of `2^-96`. This is a limit of this proof route
at these parameters, **not** a lower bound on actual attack success. The
native 26-bit PoW setting is not itself a proved discount; the calculation
deliberately grants it as a favorable upper limit.

For blowup 2, the strict Johnson boundary means at least **193** independent
queries are necessary to *possibly* fit `2^-96` without grinding. Even with
the entire hypothetical 26-bit discount, at least **141** are necessary:

```text
ungrinded:  s/2 > 96       => s >= 193
26-bit credit: s/2 + 26 > 96 => s >= 141
```

The [Circle STARKs Appendix B, Theorem 6](https://eprint.iacr.org/2024/278.pdf)
gives a more concrete **single-domain candidate** if the native `N=2^20`
and `D=2^21` were proved to be its degree parameter and standard-position
coset. Its rate would be `(N+1)/D = 1048577/2097152`, and its agreement
parameter is `(1+1/(2m))*sqrt((N+1)/D)` for valid finite `m`.

| Candidate multiplicity | Minimum draws for query term `<=2^-96` | Minimum with hypothetical full 26-bit query credit | Current 70-draw query term's integer bits |
| --- | ---: | ---: | ---: |
| `m=3` | 346 | 253 | 19 |
| `m=N/2=524288` | 193 | 141 | 34 |

These are **separate candidate settings**; the `m=N/2` choice is favorable
only to the query expression. The same paper's Remark 26 contains a
commitment/folding **upper-bound expression** whose leading term grows as
`(m+1/2)^7`. Even at the favorable `m=3`, **unrealistically small** batch
width `L=1`, and `B=2`, that single leading term is above `2^-96` for
`N=2^20`. The actual native batch width is unextracted, other theorem terms
are positive, and choosing large `m` for queries makes this leading term
worse. A term of an upper-bound expression exceeding the target does not
prove an attack; it means that expression cannot certify the target without
additional justified reductions.

The [Lean arithmetic theorem](../../../formal/s31/S31/Gadgets/PcsFri/ConservativeEnvelope.lean)
strengthens this candidate conclusion. For **every** `B >= 2`, `m >= 3`,
`L >= 1`, and `N >= 256`, the same Remark 26 leading expression exceeds
`2^-96` over the native `QM31` challenge field. Substitute `D=N*B` and
`rho_minus=1/B`: the expression contains `B^3*sqrt(B)*N^2` times positive
monotone factors in `m` and `L`. Replacing `sqrt(B)` by the lower floor `1`
already gives more than `2^-96` at the favorable corner
`(N,B,m,L)=(256,2,3,1)`. The exact diagnostic checks that `N=128` does not
cross this *floor* while `N=256` does. Query count and PoW do not alter this
particular commitment/folding expression. This is a **conditional limit of
the published proof envelope**, assuming the paper's parameter mapping; it
is neither a native soundness result nor an attack lower bound. A different
published bound, a wider challenge field or a different protocol could change
the conclusion.

## Query-only design space

The table holds `N=2^20` fixed, uses the whitepaper's circle-domain capacity
condition `N*B^2 <= 2^30`, and changes `B` **hypothetically**. It says nothing
about whether the native AIR degree, multi-domain protocol, prover capacity,
or other soundness terms permit that change.

| Hypothetical blowup `B` | Minimum Johnson-limit draws without grinding | Minimum with full hypothetical 26-bit query credit | Circle candidate `m=3` minimum ungrinded draws |
| ---: | ---: | ---: | ---: |
| 2 | 193 | 141 | 346 |
| 4 | 97 | 71 | 124 |
| 8 | 65 | 47 | 76 |
| 16 | 49 | 36 | 55 |
| 32 | 39 | 29 | 43 |

With 70 draws and 26 hypothetical query-credit bits, `B=4` still misses the
strict Johnson boundary by one draw. `B=8` passes this **necessary query-only
screen**, but it says nothing about the commitment/folding, composition,
OODS, logUp, small-table, Merkle, or Fiat–Shamir errors. The Circle candidate
at `B=8,m=3` would still need 76 **ungrinded** draws. A larger blowup also
increases the domain and generally the proof cost. No row in this table is
a proposed production configuration or a security certificate.

## What remains before selecting parameters

The [published theorem-input ledger](PCS_FRI_GATE_ERROR_LEDGER.md) still has
null values for the actual multi-domain batch widths, AIR degree and
constraint count, multiplicity and list-size bounds, small-domain premises,
all interactive round errors, and the BCS/ROM adversary budget. The native
source and binary must be related to the paper's exact oracle and transcript
relations, including the lifted commitment layout, query sampling, degree
correction, hash binding, and PoW schedule. Only then can a candidate tuple
be chosen by evaluating the **whole** published error expression and its
prover cost. Until that reduction is complete, all native proven security
bits and release admissibility stay null/false.

Focused test:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_conservative_feasibility -v
```
