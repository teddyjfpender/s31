# Scalar control gadgets: source to Gate AIR

This is a bounded correspondence slice for a transparent v1 S31 program with
one public scalar M31 input, two private four-lane M31 inputs, and exactly
three source nodes: `is_zero`, `select`, and `inv`. It joins four checks:

1. The existing exact-byte Lean checker independently parses the S31 source
   and compares its typed derivation and normalized relation. The package
   verifier also re-runs the production parser against the sealed source.
2. The native optimizer receipt matches source JSON and canonical IR digests
   and reports no aliases. The accepted shape therefore has six canonical
   nodes in source order.
3. `control_air_correspondence.py` inspects the installed compiler's real
   generic Gate roster. It checks 14 distinct owning arithmetic rows, canonical
   constants, the public input's M31 scalar owner, all four active inverse
   lanes, and the key-bound dynamic fixed columns.
4. `ControlGadgetAir.lean` proves that every assignment satisfying those
   local nine-residual AIR rows computes the chosen branch and that a selected
   zero lane cannot satisfy the inverse gadget.

For example:

```s31
use std@1;
circuit control_air(public x: [m31; 1], private a: [m31; 4],
                    private b: [m31; 4]) -> public [m31; 4] {
    let z = std::field::is_zero(x);
    let picked = std::field::select(z, a, b);
    let result = std::math::inv(picked);
    result
}
```

If `x=0`, the zero-test constraints force the **entire QM31 wire** `z` to
`(1,0,0,0)`; `picked=b`. If `x=1`, `z=(0,0,0,0)`; `picked=a`. For
`a=[2,3,4,5]` and `b=[7,8,9,10]`, the first case requires
`7·result[0]=1`, `8·result[1]=1`, `9·result[2]=1`, and
`10·result[3]=1` modulo `p=2³¹−1`. If the selected branch has a zero
lane, `0·result[i]=1` is impossible; the circuit has no satisfying witness.

The native graph uses these *actual* primitive rows (one packed word for the
four-lane branches):

| Source step | Gate rows | Constraint consequence |
|---|---|---|
| scalar input `x` | `x .* 1 = x` | Only the base M31 coordinate may be nonzero |
| `z=is_zero(x)` | `p=x·u`, `c=1−z`, `d=p−c`, `q=x·z`, `A+d=A`, `B+q=B` | `x·u=1−z` and `x·z=0`, hence `z=1` exactly when `x=0` |
| `picked=select(z,a,b)` | `t=1−z`, `l=a·t`, `r=b·z`, `picked=l+r` | The packed branch is `a` for `z=0`, `b` for `z=1` |
| `result=inv(picked)` | `p=picked .* result`, `d=p−(1,1,1,1)`, `C+d=C` | Every active lane obeys `picked[i]·result[i]=1` |

`A`, `B`, and `C` are fresh anchor wires. They do **not** need a trusted
zero hint: cancellation in `A+d=A` forces `d=0` for any anchor value.
The M31 input row and the all-ones mask are checked against source-bound
native fixed-column data. Each arithmetic row is the native `qm31_ops`
polynomial residual for its recorded operation flag, addresses, and packed
input/output values.

Run the auditable package check after building a package and the Lean byte
checker:

```sh
cd formal/s31 && lake build s31-pure-field-derivation-bytes-check
cd ../..
python3 scripts/compiler/control_air_audit.py /path/to/control-air-package
```

The command verifies the package manifest and artifact hashes, re-runs the
production parser, runs the independent Lean exact-byte checker, and captures
the installed native graph. The twelve hostile controls are
in `test_control_air_correspondence.py`; they remove an anchor, change
selection and inverse wires, remove the scalar input owner, and mutate fixed
columns, sealed identities, extraction, conversion, and public pins.

The Python graph checker alone binds the source digest; it does not parse S31
text. The audit command supplies the source-to-relation check. Its optional
injected topology argument exists only for mutation tests and must not be used
for package admission. The 14-row count comes from the distinct matched row
outputs: one scalar owner, six zero-test rows, four select rows, and three
inverse rows. Padding and unrelated Gate rows are outside that count.

The [public pin continuation](ControlGadgetPublicPins.md) follows the packed
inverse result through extraction, M31-to-u32 conversion, and four ordered
public output pins under an explicit conversion-component premise.

This is local compiler-to-AIR correspondence for one no-alias fragment. The
native inspector supplies graph bytes; the Lean proof assumes the corresponding
AIR rows are satisfied. The theorem proves soundness and zero-inverse
rejection for arbitrary satisfying rows. `ControlGadgetCompleteness.lean`
proves that the local zero-test, selection and inverse equations have some
witness exactly when every selected lane is nonzero. Its forward direction
quantifies over all possible hints; its reverse direction constructs concrete
hints. It does not construct a full physical trace or prove native
witness-builder behavior. Circuit lookup/permutation
closure, committed witness authentication, native verifier refinement, and
PCS/FRI soundness are separate obligations. The package is not a v0.1
soundness certificate.
