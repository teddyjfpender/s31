# Independent terminal evaluation in FRI capture admission

The native verifier checks each final FRI query against
`LinePoly.evalAtPoint`. S31's post-verification capture gate now evaluates the
same committed terminal coefficients by a separate pair-reduction algorithm.
The gate reuses one scratch buffer for all raw transcript slots. This removes a
common control path between the verifier's terminal check and the capture
admission check; it does not make either implementation a formal semantics
proof.

For four coefficients `[1, 2, 3, 4]` and line coordinate `x = 5`, the first
doubling factor is `2x² − 1 = 49`. The coefficients are in the native recursive
order, so the two reductions are

```text
[1, 2, 3, 4]  -- factor 49 -->  [1 + 2·49, 3 + 4·49] = [99, 199]
[99, 199]    -- factor  5 -->  [99 + 199·5]          = [1094]
```

For `2^k` coefficients, the gate computes factors
`x, 2x²−1, doubleX²(x), …` and consumes them in reverse order while pairing
adjacent coefficients. This takes `2^k−1` QM31 multiplications and additions,
plus `k` factor doublings, and `O(2^k)` reusable scratch space. The native
verifier instead uses a pending-stack evaluator. The two algorithms agree in
the focused differential test for eight deterministic M31 point samples at
each coefficient count `1, 2, 4, 8, 16, 32, 64`; a hand-calculated four-term
case additionally pins factor order.

[`TerminalBasisRefinement.lean`](../../../formal/s31/S31/Gadgets/PcsFri/TerminalBasisRefinement.lean)
now proves the coefficient-basis identity for *every* full binary tree of
height `k`, hence every `2^k` coefficient count: reducing adjacent pairs with
the last factor equals the recursive outer-half evaluation with the first
factor. The theorem includes the exact native-order flattening length and a
four-coefficient calculation that detects reversed factor order. A separate
native regression exercises every one-hot coefficient in counts `1` through
`256` at `x = 0`, `x = 5`, and `x = p-1`. It compares both evaluators against
the independently computed product of the selected doubling factors, so an
omitted coefficient or incorrect factor index is visible even if both
evaluators happen to agree with each other.

The existing capture gate independently replays every raw FRI query through
each captured circle or line subset. At every round it checks the raw position,
the current value in the subset, and the next value computed from the captured
challenge and domain coordinate. It then checks the final value using the
pair-reduction evaluator. The native regression covers zero, one, and several
inner layers; fold widths one, two, and three; a partial final fold; and
duplicate raw queries. It also mutates a raw answer, subset, position, inner
subset, and terminal coefficient after verifier acceptance. Source controls
reject bypasses of terminal evaluation, wrong factor order, wrong doubling,
and missing odd coefficients.

An additional native `FriVerifier.commit` regression constructs a three-root,
two-coefficient proof shape directly, with first fold width two and inner
fold widths two and one. It independently replays the actual M31-channel
transcript: absorb first root, draw its QM31 challenge, absorb each inner root
and draw its challenge, then absorb the bounded terminal coefficients. The
test checks each stored challenge, the circle/line domain sizes, each stored
fold width, the terminal coefficient copy, and the final 32-byte digest.
Changing a root or a terminal coefficient changes that digest. A source guard
also pins the native final-query path: the query index is bit-reversed in the
last line domain, `LinePoly.evalAtPoint` evaluates the terminal polynomial at
that point, and a mismatch returns `LastLayerEvaluationsInvalid`. Mutation
tests reject removal of the coordinate, evaluator, or equality check.

This is a finite executable refinement of the root/challenge/terminal order
and final-query check for the pinned implementation. It does not prove the
Zig loop semantics for every input, challenge independence in the random
oracle model, or that accepted Merkle paths define one fixed oracle. Those
remain required for the published circle-FRI protocol and P04 discharge.

Run the focused checks from the S31 root:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_operational_admission -v
bash formal/s31/tests/run_pcs_fri_raw_refinement_native.sh
```

P04 remains open. The native verifier and capture gate are Zig programs, and
Lean has no machine-checked theorem that their successful execution implies
`OperationalExtraction.operationalAccepts`. The coefficient-tree theorem does
not compile the native pending-stack loop or capture-gate loop into Lean, and
the native evaluator also relies on shared QM31 arithmetic and line-domain
point implementation. A
separate authenticated-oracle reduction must bind captured subsets to fixed
committed FRI columns; source checks and finite tests do not prove that
binding. The full FRI proximity theorem and cryptographic failure terms are
separate obligations.
