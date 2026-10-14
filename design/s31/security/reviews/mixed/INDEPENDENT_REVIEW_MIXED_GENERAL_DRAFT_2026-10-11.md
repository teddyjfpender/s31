# Independent static review: bounded general mixed profile

Review target: engine draft `7d544c6839497ca19b6c7ef9b982e464f10cfeed`
and S31 staging source-pinned wrapper through `6933095`. This is an
independent agent's **read-only static review**, not a native test, formal
proof, or cryptographic security audit. Later CLI and test changes must be
checked by their dedicated native gates.

## Finding and conditions

The reviewer found no concrete P1/P2 false-proof admission path in the
source-embedded verifier. It reconstructs the 1–8 call plan, exact `1+2N`
ordered circuit/chip/bridge roster and typed registry digest from literal
source; checks the eight public words, all active claimed sums and zero
unused sums, fixed root, AIR binding, live handle geometry and PCS settings;
and verifies one ordered transcript and borrowed PCS proof. The exported
engine API itself accepts caller-selected source and manifest values. It is
an internal adapter; only `general_package.verifyEmbedded*` supplies the
source authority required for proof-byte admission.

For the tagged step relation, each chip row enforces four
`next = current² + constant` transitions and a tagged input/output lookup
fraction. Each bridge row binds eight endpoint words throughout its 16-row
cycle and contributes eight Gate fractions plus the first and last chip
fractions, weighted `1/16`. Given authenticated all-row AIR constraints,
noncolliding tuple compression, committed tuples before independently drawn
uniform QM31 challenges, and rounds below the field characteristic, the
tagged flow from step zero through the declared rounds links the circuit
input and output to the chip computation. The reviewer did not formalize
this argument or derive a total STARK soundness bound.

The [lookup worksheet](../../LOOKUP_COMPRESSION_BUDGET_2026-10-11.md)
computes at most 722,185 denominator terms and the reviewed weighted bound
12,585,504 for N≤8, circuit rows≤2¹⁶, total chip rounds≤2¹⁸ and exactly
nine circuit outputs. Its ideal-challenge algebraic term below 2⁻⁸³·⁴⁹ is
conditional; it excludes AIR degree testing, PCS/FRI, Fiat–Shamir and
implementation error. The engine enforces the nine-output shape and the
existing bounded plan enforces row, round and call limits.

## Admission checklist

1. Compile and run engine proofs and mutation tests for all eight call counts.
2. Pin that tested engine commit in S31; run the sealed wrapper tests and
   black-box CLI tests, including malformed claims, cross-source rejection,
   wrong assignments and independent manifest digest recomputation.
3. Check the CI evidence and refresh the source binding and Lean proof
   inventories. Update the mixed-boundary user docs after admission.
4. State the conditional lookup term separately from a complete
   AIR/PCS/FRI/Fiat–Shamir error analysis.

Until these gates pass, this document records a **conditional static GO for
continued implementation**, not release acceptance.

## Subsequent local evidence

On engine revision `7d544c6839497ca19b6c7ef9b982e464f10cfeed`, the
selected engine N=1..8 native proof tests, S31 source-pinned wrapper tests,
and black-box source/manifest/claim mutation suite passed locally. The
black-box suite independently recomputed the generated registry manifest
digest and checked all eight call counts. The source-pinned N=3 and N=4
legacy native gates also passed. This evidence satisfies the **local test**
part of items 1 and 2 above; CI and a complete formal/cryptographic
soundness review remain open. The original reviewer did not inspect these
later test results, so this appendix does not change the static review's
scope or release conclusion.
