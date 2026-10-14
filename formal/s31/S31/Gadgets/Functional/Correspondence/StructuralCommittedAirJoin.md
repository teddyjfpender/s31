# Structural graph to a verified direct-Gate commitment

This finite audit connects one Lean-checked `.s31` source and assignment to
the **exact physical fixed and base columns** produced by the installed
direct-Gate prover. It then recommits those columns with the native PCS code
and compares both roots to a proof accepted by the generated native verifier.
On a clean checkout, initialize the pinned Stwo submodule and prepare Lean
dependencies and the structural statement checker first. These steps may take
several minutes and should finish before the audit's 60-second Lean execution
timeout begins:

```sh
git submodule update --init deps/stwo-zig
cd formal/s31
lake exe cache get Mathlib.Data.ZMod.Basic Mathlib.Tactic Mathlib.NumberTheory.LucasLehmer
lake build s31-general-linear-structural-check
cd ../..
```

Then run the focused audit from the repository root:

```sh
python3 -B formal/s31/tests/audit/structural_committed_air_join.py
```

The handwritten program is:

```s31
circuit square(public x: [m31; 4]) -> public [m31; 4] {
    let pair = (x, x);
    let y = pair.0 .* pair.1;
    y
}
```

For `x = [0, 1, 2, 7]`, the independent expected public result is
`y = [0, 1, 4, 49]`. The tuple exists only in source: the normalized relation
has one pointwise multiplication node. The current native compiler assigns
its packed input to address 22 and its result to address 23. After padding,
the source gate occupies QM31 component row 503:

| Row | add | sub | QM31 mul | pointwise mul | in0 | in1 | out | uses(out) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 503 | 0 | 0 | 0 | 1 | 22 | 22 | 23 | 4 |

The row's twelve base cells are three four-word values:
`in0 = [0,1,2,7]`, `in1 = [0,1,2,7]`, and
`out = [0,1,4,49]`. The audit checks these cells plus **all** 4,096 fixed
and 6,144 base cells, not only row 503. It checks the exact source bytes,
normalized relation, public assignment, native graph, and padded row roster
before making this comparison. Three changed cells on row 503 and changed
fixed- and main-root proof bytes are rejected.

There is one profile-specific step. The structural graph exporter currently
uses the full circuit padding pass, so its zero-address multiplicity includes
reads from inactive Eq/XOR/conversion/Blake padding. The direct-Gate proof
commits only the QM31 component. The audit therefore recomputes every direct
Gate multiplicity from the padded QM31 input addresses and the public output
roster, with an explicit field-bound check. Selectors, addresses, and row
values are compared exactly. This explains the otherwise observed zero row
mismatch (`203` in the full padded export versus `11` in direct-Gate).

## What the root comparison establishes

The audit invokes the package's native prover and verifier for the exact
source and assignment, checks `writeBase`'s public physical export against
the checked graph, asks the native PCS code to recommit the independently
assembled fixed and base columns, and compares those roots with the roots
serialized in the **accepted** proof. The native verifier rejects changed
fixed- and main-root bytes. The all-public bounded profile makes the base values safe to
export for this test.

This is a finite honest-prover correspondence and adversarial regression.
The two root recomputations and the prover share native PCS implementation;
the test does not prove its cryptographic binding. It also does not derive
arbitrary proof openings or committed private witness cells, cover other
trace heights/components, or prove the installed AIR evaluator is equivalent
to the Lean row model. Those remain release blockers. The source-to-graph
step still relies on a bounded artifact checker, while the Lean decoder
constructs a `NativeTrace` for its admitted JSON projection.
