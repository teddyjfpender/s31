# CAS07 one-height circle fold and terminal check

CAS07 is an experimental native proof candidate in stwo-zig PR #269. It is
not admitted by the production S31 verifier. This note fixes the exact
one-source-height (`H = 1`) local relation formalized in
[`Cas07H1Terminal.lean`](../../../formal/s31/S31/Gadgets/PcsFri/Cas07H1Terminal.lean).

## A query by hand

Take an initial circle domain with `k = 2` (four positions) and blowup
`beta = 1`. The verifier folds one circle pair, so the terminal line domain
has `2^(k-1) = 2` positions and the permitted terminal coefficient array has
`2^(k-1-beta) = 1` word. Let the challenge be `alpha = 7`. At line row zero,
take circle `y = 3` and opened source values `(10, -2)`. The inverse
butterfly computes

```text
sum = 10 + (-2) = 8
difference / y = (10 - (-2)) / 3 = 4
fold = sum + alpha * (difference / y) = 8 + 7*4 = 36
```

At line row one, `y = 5` and pair `(14, -6)` give the same result:
`8 + 7*(20/5) = 36`. Thus terminal coefficients `[36]` pass at both rows;
`[37]` fails. Over M31, negative small values mean their canonical residues
modulo `2^31 - 1`. The Lean example uses rationals for readable arithmetic;
the general theorem works over any field, including QM31.

The general affine identity is

```text
pair(y) = (c0 + y*c1, c0 - y*c1)
fold(pair(y), alpha) = 2 * (c0 + alpha*c1).
```

The factor two is intentional: native `ibutterfly` does not divide the sum or
difference by two. A zero initialized prover destination has exactly this
result after `foldCircleIntoLineWithWorkspace`.

## Exact local statement

For each raw transcript query `q`, CAS07 uses `p = q / 2`, reads its captured
pair, inverts the circle `y(p)`, applies the equation above, and evaluates the
terminal polynomial at line coordinate `x(p)`. The verifier has **zero**
intermediate line commitments at `H = 1`. Lean's `verified` records the
terminal coefficient count, query range, nonzero `y`, and equality of the
captured fold with the terminal value. `authenticated` separately states
that each captured pair is the corresponding pair of one fixed source oracle.

`verified_authenticated_terminal` proves that both premises imply, for every
raw query including duplicates, that the *oracle* fold equals the terminal
evaluation and the row is in the terminal domain. `same_row_openings_agree`
proves two authenticated raw slots at the same row cannot equivocate. The
line evaluator uses ordered coefficients: the first four terms are
`c0 + c1*x + c2*(2*x^2-1) + c3*x*(2*x^2-1)`; Lean proves the one-, two-, and
four-coefficient expansions.

The current general `LayerAcceptance.Layer.fold` type has no row argument,
whereas the circle inverse coordinate depends on the row. This H=1 model
keeps that coordinate dependence explicit. It does not assert that the
existing abstract layer model represents the native fold without a further
indexed-fold refinement.

## Native correspondence and remaining gates

The equations are matched to `src/core/pcs/paired_sparse_cascade_heights_experimental.zig`:
`foldPair`, the `step == 0` branch of `verifyFolds`, the final
`TerminalFoldMismatch` check, and `Profile.terminalLength`. The prover's
`height_count == 1` branch in
`src/prover/pcs/paired_sparse_cascade_heights_experimental.zig` performs the
same circle-to-line fold, interpolates the line evaluation, rejects nonzero
coefficients above the permitted terminal length, and sends the ordered
coefficients. The cited Zig paths refer to the draft stwo-zig PR #269, not
the pinned production submodule.

The Lean theorem is conditional. Release remains blocked until the following
are independently established and composed:

1. Successful Zig execution refines `verified`, including exact `y`, `x`,
   inverse, row indexing, M31-to-QM31 embedding/multiplication, and native
   ordered line evaluation.
2. The XDM05 source openings and batched quotient answers imply
   `authenticated` for a single committed oracle; the trusted S31 AIR/claim
   roster and verification key must bind that oracle.
3. The paper's proximity and degree-corrected quotient theorem applies to
   this H=1 profile; Fiat–Shamir, BCS/ROM, hash, and query sampling failure
   terms are bounded for the chosen work-factor target `epsilon(T)/T`.

Focused proof check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake env lean S31/Gadgets/PcsFri/Cas07H1Terminal.lean
```
