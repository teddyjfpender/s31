# Static enum and match audit (2026-10-12)

## Scope and claim boundary

This review covers the source parser, whole-program type elaboration, conservative
effect analysis, specialization, and the new Lean model for source-only sums.
It is an implementation review, not a proof of Python-to-Zig correspondence or
native PCS/FRI soundness. The Lean model has binary sums and a local four-lane
arithmetic-to-AIR theorem; the text frontend supports nominal enums with up to
64 variants. There is no checked translation from every text enum to that Lean
core yet.

The supported zero-cost claim is structural: a constructor's tag and
`match` introduce no normalized relation node when the tag is known at
specialization. Payloads are evaluated eagerly during specialization, and
unobserved total M31 arithmetic may then be pruned. Partial operations and
the selected arm's live computations retain their proof obligations and
nodes. The tag is not a private input, public output, or witness-selected
circuit value. The adversarial test compares complete
first-order relation topology after deterministic wire renaming against direct
arithmetic, including inputs, nodes, assertions, and the public output. A
separate three-variant case permutes match-arm order and checks the selected
arm's emitted nodes and evaluated public result.

## Findings

| Severity | Finding | Reproduction and disposition |
| --- | --- | --- |
| Medium, fixed | At audit start, enum payload layouts were computed but their depth and flattened leaf limits were not enforced. A 1,025-element tuple payload passed `Parser.parse()` despite the documented 1,024-leaf limit. | The parser now checks both limits. `src/frontends/s31/tests/python/security/test_static_sum_admission.py` passes at the 1,024/1,025-leaf and 32/33-depth boundaries. |
| Low, fixed | At audit start, an unused, total constructor payload emitted arithmetic. `Choice::Left(x .* x)` followed by an arm returning outer `x` retained a multiplication node. This did not weaken proof soundness. | The [conservative DCE pass](../language/STATIC_SUM_DCE.md) now removes unobserved M31 `constant`, `add`, and `mul` forms after strict specialization. It retains partial failures, assertions, ABI roots, and dependencies of unreviewed operations. Eight focused Python cases and a native direct-chip proof compare an ignored-payload recurrence to the exact direct AIR geometry; the changed public claim is rejected. |

No witness-dependent enum tag path was found in the reviewed language subset.
Circuit boundaries reject sum values; witness-dependent `if` rejects sum and
tuple-of-sum results; constructors specify their tag syntactically; and a
`match` specializer requires a `StaticVariant` before selecting exactly one
arm. The effect checker evaluates constructor payload effects and, for an
unknown enum parameter, conservatively joins effects from every arm. An
inactive match arm with a known tag is not evaluated. The step specializer uses
the same static selection and still applies its restricted recurrence checks.

## Remaining assurance work

1. Extend the formal source model or provide a checked encoding for nominal
   enums with more than two variants, including text parser and elaborator
   correspondence.
2. Prove or independently validate that the Python effect analysis admits no
   partial operation in an inactive witness-dependent `if` arm after enum
   specialization and higher-order calls.
3. Compare canonical relation geometry and native verifier acceptance for a
   varied enum corpus against direct first-order programs. The focused
   direct-chip proof and structural regressions do not cover every builtin or
   chip profile.

This review does not upgrade the release status of those obligations.

Focused validation: `PYTHONPATH=src/frontends/s31/tests/python:src/frontends/s31/python python3 -m unittest security.test_static_sum_admission` passed all four tests after the parser fix. `git diff --check` passed for the parser, audit note, and security test.
