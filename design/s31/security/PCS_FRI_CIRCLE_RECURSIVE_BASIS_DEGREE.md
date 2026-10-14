# The full recursive circle basis has a Laurent degree bound

The [two-Q degree join](PCS_FRI_SPARSE_GATE_TWO_Q_DEGREE_JOIN.md) needs a
bounded source polynomial at each accepted height. Its previous four-slot
basis theorem covered only the first four native coefficients. The new
[`CircleRecursiveBasisDegree.lean`](../../../formal/s31/S31/Gadgets/PcsFri/CircleRecursiveBasisDegree.lean)
proves the degree bound for **every coefficient slot** in a source-transcribed
recursive circle evaluator. This is an algebraic bridge. It does not certify
that an accepted native column or the iterative evaluator realizes the model.

The generic Laurent construction assumes an `i` with `i² = −1`. M31 itself
has no such element. The concrete mathematical instantiation therefore uses
CM31 coefficients with each native M31 coefficient embedded as `(a,0)`;
the [M31 embedding proof](PCS_FRI_CIRCLE_BASIS_DOT.md) makes this cast and
its QM31 base-value image explicit. It still does not prove Zig's M31 array
conversion or sampled-value implementation.

The follow-on [circle FFT-space proof](PCS_FRI_CIRCLE_FFT_POLYNOMIAL_SPACE.md)
establishes the stronger two-component degree condition from the whitepaper's
`L′ₖ` definition for this same recursive word. A Laurent radius bound by
itself admits one extra top direction.

## The native factor order

[`fillEvalFactors`](../../../deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig)
constructs point factors in this order:

```text
factor 0 = y
factor 1 = x
factor 2 = 2x² − 1
factor 3 = 2(2x² − 1)² − 1
...
```

The same source file's `evalAtPointRecursive` splits a `2^k` coefficient
array into left and right halves and evaluates

```text
E₀([c₀]) = c₀
Eₖ₊₁(c) = Eₖ(left half) + factor k · Eₖ(right half).
```

The selected `CircleCoefficients.evalAtPoint` calls the faster
`evalAtPointIterative` carry loop. The recursive function is retained in
native source as a differential reference. The Lean definitions transcribe
the factor and half-split recurrences; they do not formalize Zig execution,
slice lengths, carry state, or compiler behavior.

## Why the bound doubles

Set `T=x+i y`, so `T⁻¹=x−i y` on the circle. The first two factors `x` and
`y` have Laurent radius one. Each later factor is a double-angle x-coordinate,
so factors 2, 3, ... have radii 2, 4, ... . Multiplying Laurent words adds
their support radii. The Lean proof establishes this for arbitrary field
coefficients by shifting each Laurent word to an ordinary polynomial,
multiplying, and shifting back.

Here are the first two nontrivial complete words by hand:

```text
4 coefficients:
  L = (c₀ + c₁y) + x(c₂ + c₃y)                     radius ≤ 2

8 coefficients:
  R = (c₄ + c₅y) + x(c₆ + c₇y)                     radius ≤ 2
  E₃ = L + (2x²−1)R                               radius ≤ 4
```

At the next merge, the new factor has radius four, so the 16-coefficient
word has radius eight. Induction gives radius `2^(k−1)` for any `2^k`
coefficient word. The Lean theorem `coefficientWord_eval_algebra` also proves
that evaluating this Laurent word at a secure-field Fourier coordinate gives
the exact **recursive value recurrence**. Thus the degree statement concerns
a polynomial with the same abstract evaluation rule, not merely a formal
support count.

| Accepted extended source height | Trace coefficient log `k` | Coefficients | Proven recursive-model radius |
|---:|---:|---:|---:|
| 17 | 16 | 65,536 | 32,768 |
| 11 | 10 | 1,024 | 512 |
| 5 | 4 | 16 | 8 |

Lean checks that these numbers equal the radii in
`SparseP05TwoQDegree.sourceRadius`. The theorem accepts arbitrary coefficient
values, including all nonzero high slots. No assumption that only the first
four coefficients are present remains **inside this recursive model**.

The composed theorem `accepted_recursive_word_two_q_own_quotients` now takes
one fully populated recursive source word and two correct evaluations at the
projected OOD points. It constructs an **own quotient for each point** with
radius one below that source's bound and proves both exact polynomial
identities. Its value premises say that the sampled claims equal this
recursive word's evaluations. Both claim certificates must have the stated
source height and the same imaginary unit as the source word. The value
premises still need to be derived from
the selected native evaluator and accepted proof; the theorem does not infer
them from the 73 captured claim values.

## Remaining native and paper join

The selected proof's source columns must still be shown to have exactly the
claimed coefficient arrays, and the iterative carry evaluator, FFT
interpolant and barycentric fallback must refine the recursive mathematical
word at every source row and projected OOD point. Native differential tests
between the iterative and recursive evaluators are useful drift checks, but
they are not an all-input semantics proof. Authentication of those same
source rows and independent degree tests of the original and each own
quotient remain open. The paper's circle-code filtration also needs an
explicit map from this Laurent filtration before importing its error bound.

The release blocker matrix therefore keeps P05 open, actual native-to-paper
batch width `M` unknown, proven security bits null, and release admission
false.

## Reproduce

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.CircleRecursiveBasisDegree
```
