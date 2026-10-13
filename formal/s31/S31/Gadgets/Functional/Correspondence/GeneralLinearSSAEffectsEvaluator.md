# Effectful SSA to the normalized evaluator

[`GeneralLinearSSAEffectsEvaluator.lean`](GeneralLinearSSAEffectsEvaluator.lean)
connects the effectful M31 SSA model to the actual `S31.evaluateNode` and
`Program.environment` functions. It covers arbitrary numbers of lanes and
`add`, `sub`, `mul`, `add_const`, and `mul_const` nodes, including nodes that
do not feed the selected output.

## An assertion on an otherwise unused value

```s31
circuit checked(private a: [m31; 1], private b: [m31; 1])
    -> public [m31; 1] {
    let out = a + b;
    let twice_a = a + a;
    let twice_b = b + b;
    assert_eq(twice_a, twice_b);
    out
}
```

For `a=[3]` and `b=[3]`, the arithmetic rows constrain
`out=6`, `twice_a=6`, and `twice_b=6`. The assertion adds a separate
zero-polynomial constraint `twice_a - twice_b = 0`. The normalized program
evaluates every row, then checks the named assertion. It accepts this input.
With `a=[3]` and `b=[4]`, the arithmetic rows still compute `out=7`, but the
assertion polynomial is `6 - 8`, which is nonzero in M31. The normalized
assertion loop rejects it even though `twice_a` and `twice_b` are not output
ancestors.

## What is proved

`named_effect_fold_of_air` proves that every accepted modeled arithmetic
trace runs to the same values through the real named evaluator, assuming the
initial input names and fresh generated names are aligned.
`named_assertion_iff_air` proves one normalized assertion accepts exactly
when the corresponding equality polynomial is zero. The ordered-list
theorems prove this for every assertion, in both directions.

`effectful_interpreter_preserves_source_assertions` uses successful actual
`Program.evaluate` to **derive** the assertion polynomials. It then applies
the checked effectful SSA source model's soundness theorem. The proof does
not assume the assertions pass.

`effectful_interpreter_public_output_claim` also binds the public output
assignment to `source.output.eval inputs`. It first derives the selected
source value from the checked certificate and accepted arithmetic rows. It
then derives assertion AIR acceptance from the actual evaluator's successful
assertion loop, reconstructs the final named environment, and uses the
evaluator's own public output check. For the example above, a successful
evaluation with `a=[3]` and `b=[3]` forces the assigned public output to be
`[6]`; assigning `[7]` cannot satisfy `Program.evaluate`.

The theorem still accepts explicit premises for the exact named node graph,
typed initial assignment, distinct names, and modeled arithmetic AIR rows.
It does not prove production compiler equivalence, native committed row
authentication, or PCS/FRI soundness. The public output result is about the
normalized evaluator and an explicitly aligned source certificate, not a
native proof's public pin.

## Check

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator
```
