# Record v2 source values and physical Gate rows

This is the next join after [record source value correspondence](GeneralRecordV2EvaluateCorrespondence.md).
It covers the bounded scalar M31 record grammar: one or two nominal record
inputs with up to four one-word fields each, up to eight `+` or `.*` local
nodes, and an ordered public record result. The static Lean admission still
checks the **exact source bytes** against the normalized relation and ABI.

## A hand-written example

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit combine(public visible: Pair, private secret: Pair) -> public Pair {
    let sum = visible.left + secret.left;
    let product = sum .* visible.right;
    Pair { left: product, right: sum }
}
```

For `visible=(2,3)` and `secret=(4,5)`, the source scalar graph is:

| Gate wire | Source value | Hand calculation |
| --- | --- | --- |
| 11 | `visible.left = 2` | public input |
| 14 | `visible.right = 3` | public input |
| 15 | `secret.left = 4` | private input |
| 16 | `secret.right = 5` | private input, unused here |
| 17 | `sum = 6` | `2 + 4` |
| 18 | `product = 18` | `6 × 3` |

The two source-owned Gate cells select add `(11,15,17)` and pointwise
multiply `(17,14,18)`. A Gate row carries a four-coordinate QM31 value at
each address; this scalar fragment uses coordinate 0 and sets the other three
coordinates to zero. The add row requires `wire[17] = wire[11] + wire[15]`.
The multiply row requires `wire[18] = wire[17] .* wire[14]`. Each row also
has a one-hot operation selector and three fixed wire addresses. In Lean,
`cellAccepts` means all nine local polynomial residuals vanish, including
the selector and four output-coordinate equations.

The ordered source result is `(18,6)`. The typed public claim is
`[2,3,18,6,0,0,0,0]`; private inputs do not enter that public array. If both
result fields select `product`, the ordered source result is `(18,18)` while
the normalized relation has one distinct output wire and claims
`[2,3,18,0,0,0,0,0]`.

## What is proved

`source_fold_physical_cells` proves by induction over **every** source node
that local Gate equations and a coherent address-to-value map propagate the
independent scalar input values to all source wires. This is a soundness
statement for arbitrary row values satisfying its premises; it does not
assume that the honest witness writer produced them. `source_run_physical_results`
then fixes every ordered result field, including aliases.

`checked_assignment_physical_results` composes that row theorem with the
exact-source admission and the actual typed `Program.evaluate` theorem. For
any assignment accepted by `checkSourceAssignment`, it concludes both the
typed claimed public words and the ordered values at the modeled physical
result addresses. It requires:

1. Input Gate addresses match the exact assignment's source-ordered public
   and private input words.
2. `checkFixedSourceCells` accepts a complete 512-row fixed-cell list with
   distinct row positions and exact source operation flags and addresses.
3. All listed cells satisfy the local `cellAccepts` polynomial equations
   under **one coherent** address-to-value map.

Premises 1 and 3 are the intended consequences of a correctly authenticated
Gate lookup and trace opening. The theorem does **not** prove those
consequences from native verifier acceptance. It also does not prove that
Python's exported JSON is the Lean `ColumnCell` list, or that the Lean checker
is executed during proof admission.

## Emitted fixed-column audit

[`record_source_cells.py`](../../../../../../src/frontends/s31/tools/audit/record_source_cells.py)
uses the independent exact-source parser and a fresh native
`inspect-topology` export for the same pinned package. It checks every source
arithmetic node against its physical row's selector and addresses, replays
all eight full fixed columns against the component manifest, and asks the
pinned native prover to recommit all 4096 fixed cells. That root must equal
the pinned verification key's preprocessed root. The snapshot uses external
SHA-256 pins for source relation, text, key, prover, and verifier.

```sh
python3 src/frontends/s31/tools/audit/record_source_cells.py PACKAGE \
  --source-sha256 SOURCE_JSON_DIGEST --text-sha256 SOURCE_TEXT_DIGEST \
  --key-sha256 KEY_DIGEST --prover-sha256 PROVER_DIGEST \
  --verifier-sha256 VERIFIER_DIGEST
```

The native export is now available for this bounded v2 record profile.
The acceptance corpus checks a public `double` at physical row 0 and a
private `paired` multiplication at row 508, then rejects a changed output
address in each export:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/record_source_cells_v2.py
```

This audit authenticates neither the **main witness trace** nor the Gate
lookup interaction. Native PCS fixed-root recommitment is still trusted as
an implementation, and the fixed-root/key comparison alone does not prove
collision resistance or proof opening soundness. A full compiler/proof join
must connect authenticated main trace cells, Gate lookup balance, public
input/output pins, and PCS/FRI/Fiat–Shamir verification to these premises.
Private-input soundness must be existential over a witness consistent with
the public claim; this module's theorem fixes an explicit assignment.
