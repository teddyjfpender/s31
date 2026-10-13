# M31 SSA with constants and assertions

[`GeneralLinearSSAEffects.lean`](GeneralLinearSSAEffects.lean) checks the
`linear-ssa-m31-effects-v1` profile. It adds canonical `add_const` and
`mul_const` operations and `assert_eq` to the pure arithmetic profile. The
soundness and completeness theorems quantify over any finite number of inputs,
steps, assertions, and lanes. The byte gate checks the production certificate
format but does not itself enforce the Python source fragment's input, lane,
and statement-count limits.

## Worked source and witness

```s31
use std@1;
circuit affine_guard(public x: [m31; 3], private y: [m31; 3]) -> public [m31; 3] {
    let shifted = x + splat<3>(7_m31);
    let scaled = shifted .* splat<3>(9_m31);
    assert_eq(y, scaled);
    let out = y - x;
    out
}
```

The production package emitted the [source], [normalized relation], and
[certificate] fixture used by the runtime Lean gate. The input prefix is
`0=x`, `1=y`. Its complete indexed graph is:

| ID | Name | Operation | Reads | Active-lane equation |
| ---: | --- | --- | --- | --- |
| 2 | shifted | `add_const` | 0 | `w₂[i] - (x[i] + 7) = 0` |
| 3 | scaled | `mul_const` | 2 | `w₃[i] - 9 w₂[i] = 0` |
| 4 | out | `sub` | 1, 0 | `w₄[i] - (y[i] - x[i]) = 0` |

The separate assertion is `y[i] - w₃[i] = 0` for each of the three lanes.
Output ID 4 is constrained even though it does not use `shifted` or `scaled`
directly. Without the assertion, those operations would be irrelevant to the
output; the checker still requires their IDs and reads to be valid. With the
assertion, the accepted output is `9(x + 7) - x`, and no witness exists if the
private `y` differs from `9(x + 7)` on any lane. All arithmetic is in M31,
including the constants.

Each arithmetic step is modeled by a four-lane packed circuit row relation.
For this three-lane example, the fourth limb is inactive and may contain
arbitrary field data. `constant_packed_iff_node` proves the packed constant
row agrees with the executable normalized `evaluateNode`, including its M31
kind and lane count. `air_iff_normalized_trace` lifts this to the complete
graph. `assertion_poly_iff_eq` proves the zero residuals express exactly the
source equality effect. `checked_air_sound` says every satisfying witness
agrees with the supplied source meaning; `checked_air_complete` constructs
rows only when all source assertions hold. The normalized variants state the
same results with normalized nodes in place of packed rows.

Assertions are collected into a final list by the production source
fragment. `assertions_permutation` proves order independence for the total,
immutable M31 terms. The production parser separately checks that an
assertion's identifiers had already been declared at its original source
position; certificate JSON has no statement positions and cannot recheck
that temporal property.

[`GeneralLinearSSAEffectsBytes.lean`](GeneralLinearSSAEffectsBytes.lean)
parses the entire certificate JSON byte string. It requires at most 65,536
UTF-8 bytes, exact sorted/indented canonical JSON, exact schema and profile,
empty `unmodeled_features`, full field sets, canonical constants below
2,147,483,647, consecutive IDs, valid backward reads, resolvable assertions,
and an output matching a separately supplied Lean `Source`. The executable
runner pins a handwritten source and roster for this fixture. Runtime controls
reject duplicate keys, unknown fields, alternate spacing, invalid references,
assertion loss, and constants outside M31. Valid visibility changes are
rejected by the *fixture roster*, while the generic checker only checks
visibility spelling.

The byte checker validates digest **syntax** and the certificate's graph. It
does not recompute source/relation SHA-256, independently parse `.s31` source
bytes, prove public ABI binding, connect the graph to emitted native Zig rows,
or establish PCS/FRI authentication. Those are separate boundaries. Records,
arrays beyond homogeneous M31 lanes, control flow, static loops, library
calls, hashes, chips, and recursion remain outside this theorem.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsBytes \
  s31-general-linear-effects-certificate-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffects
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsBytes
python3 tests/audit/general_linear_ssa_effects_certificate.py
```

[source]: ../../../../fixtures/correspondence/effects/affine_guard.s31
[normalized relation]: ../../../../fixtures/correspondence/effects/affine_guard.relation.json
[certificate]: ../../../../fixtures/correspondence/effects/affine_guard.certificate.json
