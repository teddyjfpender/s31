# P09/P07: fail-closed error ledger for one gate profile

The [ledger tool](../../../scripts/release/pcs_fri_gate_error_ledger.py) accepts a
locally trusted sealed `gate`, fold-step-1 package whose maximum trace height
is `2^20` and whose conditional FRI input domain is `2^21`. It reruns the
[P01 gate diagnostic](PCS_FRI_GATE_FINAL_DOMAIN.md), including the package's
native `check-key` command. Run it only with a locally trusted package binary:

```sh
python3 -B scripts/release/pcs_fri_gate_error_ledger.py /path/to/sealed-gate-package
python3 -B scripts/release/pcs_fri_gate_error_ledger.py /path/to/sealed-gate-package --require-proven
```

The second command exits 2. This is a theorem-input ledger, **not** a
certificate. It emits no native security bits and cannot open the v0.1 release
gate. The package hashes check internal artifact consistency, not an external
trust anchor; `check-key` acceptance is not proof acceptance. The source
guard does not establish the installed executable's binary provenance.

## What can currently be entered

| Observation | Value for the reviewed local `affine_guard` package | Why it is limited |
| --- | ---: | --- |
| Maximum sealed trace rows | `2^20` | Candidate `N`, not yet identified with the paper's degree parameter. |
| FRI input domain rows | `2^21` | P01 derives this only for a successfully executed pinned verifier path. |
| Blowup factor | `2` | Key and native constructor agree; theorem oracle relation remains open. |
| Raw query draws | `70` | Source tuple and key; independence and fixed-good-set premises remain open. |
| Fold step | `1` | Avoids the separate grouped-fold schedule gap; other refinement gaps remain. |
| PoW setting | `26` bits | A native setting; it is not automatically a multiplier on every error. |
| Ideal M31 mask excess | `1/2^31` for a fixed set of `2^21` positions | Exact preimage count under independent uniform raw words; no native ROM claim. |

If the theorem's Circle `N` were the maximum trace size and its standard
position coset `D` were this final FRI domain, its candidate rate would be

```text
rho_plus = (N+1)/D = 1048577/2097152.
```

Both identifications are **unproved**, so the ledger records the candidate
ratio separately and leaves `circle_N_degree_parameter` and
`circle_D_standard_position_coset` null. The same applies to the S-two
multi-domain initial-oracle family. In particular, the source-derived
`D=2^21` is not silently substituted into the published theorem.

## Error structure and missing inputs

For [Circle STARKs, Appendix B, Theorem 6](https://eprint.iacr.org/2024/278.pdf),
the candidate ideal query event would be bounded by

```text
((1 + 1/(2m)) sqrt((N+1)/D) + 1/2^31)^70
```

only after identifying `N,D`, choosing a valid Johnson multiplicity `m`,
checking the list and finite-domain conditions, fixing the good set before
sampling, proving independent ideal raw words, and matching all native query
checks to that set. The exact mask-excess term comes from the finite M31
preimage theorem; it is not an extra proven native soundness term. Theorem 6
also has a commitment/folding error. Theorem 7 adds AIR composition and OODS
terms. None is filled in by the query expression.

The closer [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf)
[theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
requires **per-round** errors for flat-AIR logUp, composition, OODS,
cross-domain batching, each FRI fold, and query checking. The ledger leaves
each `epsilon_i` and `max_i epsilon_i` null. It does not place the Circle
single-domain query expression into the S-two multi-domain theorem by name.

The S-two NIROP/BCS theorem gives this **conditional** form:

```text
epsilon_NIROP(T) <= (T+R) max_i epsilon_i + 3(T^2+1)/2^lambda.
```

`T` is an explicit *adversary hash-query budget*, `R` the theorem's actual
transformation round count, and `lambda` its random-oracle output parameter.
The selected release target fixes `T = 2^64` BLAKE2s queries and requires the
paper's work-factor expression `epsilon(T)/T <= 2^-96`. The package itself
does not fix or enforce that adversary budget; accounting for the native hash
calls in the theorem's query model remains open. `R` and `lambda` remain null
in the ledger. The second term is the theorem's random-oracle collision and
binding contribution, conditional on its exact BCS model. Separately, the
native Merkle binding failure bound is null until the concrete plain
BLAKE2s-256 leaf/node encoding and decoder are reduced to that model; the
ledger does not assume that the theorem's collision term automatically covers
native Merkle failures. A 32-byte hash output does not by itself justify
substituting `lambda=256`, and `pow_bits=26` does not reduce `epsilon_i`
without an exact grinding reduction.

The missing native-to-published refinement error is also null. Consequently
there is no whole-proof error to compare with a target and no security-bit
output. Closing P09 requires every published term and prerequisite; closing
P07 additionally requires explicit `T,R,lambda`, native transcript and PoW
semantics, random-oracle or concrete-hash assumptions, and an accounted Merkle
collision event. Source pins and finite tests make the current **unknowns**
auditable, but they do not discharge these cryptographic premises.

Focused controls:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_gate_error_ledger -v
python3 -B scripts/release/pcs_fri_v01_blockers.py --check --require-admissible
```
