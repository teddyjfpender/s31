# Independent review: public direct-Gate physical roster

This review covers diagnostic commit `851cee9`: the `inspect-physical-rows` branch in
[`mvp_runtime.zig`](../../../src/frontends/s31/runtime/mvp_runtime.zig), its
[`public_physical_guard.zig`](../../../src/frontends/s31/runtime/public_physical_guard.zig),
and the two-case [`full_native_roster.py`](../../../src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py)
checker. The command exports **uncommitted** `writeBase` fixed/main evaluations.
Its output is not a native proof, proof opening, or verifier acceptance result.

## Admission and private values

`parsedProgram` calls `relation.parseProgram`, which calls `Program.validate`.
For generic sources, `eligible` additionally requires version 1, transparent
mode, one public M31×4 input, 1–16 add/multiply nodes, no assertions, and one
public M31×4 output selected from a node. `Program.validate` requires both
operands of each admitted add/multiply node to be M31 of equal shape and
rejects extra node parameters. By induction from the sole M31×4 input, all
admitted generic nodes are M31×4. The native branch also requires its one
input to be public and rejects any nonempty `private_inputs` object before
evaluation, compilation, or `writeBase`. `relation.evaluate` checks assignment
field counts and values. I found no path through this branch that exports a
private assignment value.

Two earlier public examples bypass `eligible` through exact SHA-256 checks of
the embedded source bytes. They still pass the one-public-input and empty
private-assignment checks. Their admission rests on the pinned source bytes;
the generic structural guard does not independently establish their profile.
The guard's focused tests cover wrong version/mode, zero or >16 nodes, multiple
inputs/outputs, private/u16/short input, input-as-output, assertions, unsupported
ops, and nonempty private assignment. These tests exercise admission logic,
not native command integration.

## Host checker and trust boundary

The checker selects one- and sixteen-node programs from the digest-pinned
source mutation corpus. It evaluates the generator's positional four-lane DAG
without using either source parser, checks the host parse against that DAG,
constructs the full 512-row direct-Gate fixed schedule in Python, and compares
all 4,096 fixed cells with both native topology and physical exports. The
Python schedule is separate from Zig's emitted gate list, but is shared with
the package correspondence checker; it is not a second independent Python
implementation. This dependence is disclosed in the adjacent README.

For main values it checks 6,144 cells, 4,608 local arithmetic roots, one
coherent address-to-four-word value map, constant seeds, all source SSA wires,
public copies, and exact Gate address/value event multiplicities including the
nine public feeder uses. Eight mutations per case target fixed selectors,
topology, arithmetic, a locally valid wrong wire, public claim, sealed root,
source identity, and an extra public feeder use. The last mutation calls the
ledger checker with an extra use; it does not mutate a native proof.
The fresh-native path separately invokes the built prover with the same
otherwise valid assignment plus a nonempty `private_inputs` object. It
requires a nonzero exit and `PrivatePhysicalRowsUnavailable` in stderr for
each case. This exercises the assignment guard through the CLI, though it
does not build a private-source package.

The host compares the exported preprocessed root with the sealed verification
key and an earlier pinned snapshot and compares the fixed-column byte digest
with that snapshot. It does not independently compute the PCS commitment root
from the columns. Neither the snapshot nor `writeBase` authenticates main or
interaction openings, LogUp compression, PCS/FRI verification, or transcript
challenges. The native-to-modeled correspondence remains conditional on these
separate proof-system and feeder bindings.

A local Python-only smoke call to `selected_samples`, `source_plan`, and
`expected_fixed` completed. The one-node case produced 26 projected cells and
`475 add / 1 sub / 27 mul / 9 pointwise` fixed rows; the sixteen-node case
produced 41 projected cells and `470 / 1 / 27 / 14` rows. Each total is 512.
This checks schedule construction only; it does not exercise native output.

## Focused evidence

From the repository root, I independently ran the pinned checker after the
two native diagnostic fixtures appeared:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py
```

It exited 0. Both cases had 512 physical rows, 4,096 fixed cells, 6,144 main
cells, 4,608 zero arithmetic roots, 1,033 balanced Gate events, and eight
rejected mutations. The one-node case had 486 constant rows and fixed-column
digest `2cd5f1f13a18d4fc353d81800722d0645a696853bfa84f22a84ccd5504c7f1f3`;
the sixteen-node case had 471 constant rows and digest
`551da763f7b741f730bfeec37ac09bc8b077394c1594e7a98ac2b2b81c3e4bc6`.
This pinned check reads the diagnostic fixtures and does not establish
that the current native exporter reproduces them.

The roster implementation agent then reported these focused commands, all
exiting 0:

```sh
zig build --build-file src/frontends/s31/build.zig test-public-physical-guard -Doptimize=Debug
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --native --write --work zig-out/s31/formal/full-native-roster-20261012
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/full_native_roster.py --native
```

The first native invocation generated both diagnostic fixtures; the second
used a clean temporary build and reproduced both files byte-for-byte without
writing them. Both fresh runs exercised the in-script CLI negative: each
source-bound prover rejected its generated
`nonempty-private-assignment-{prefix}.json` with
`PrivatePhysicalRowsUnavailable`. SHA-256 of the
fixture files was `0d4d6fe33673721bc1e6da2dcf49dce8493391c4ca336d4fc0da6901f28dda44`
for `case00-full-native-roster.json` and
`6cebdf94b8958bf792ff319baf7c36f59e3fb97e90b7153304f260173e86e04f`
for `case16-full-native-roster.json`. These are reproducibility observations
for the diagnostic exporter, not verifier-to-trace authentication.

## Pinned square4 modeled corollary (static review)

I also inspected the new, then-uncompiled
[`PinnedSquare4CompleteModeledTrace.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/PinnedSquare4CompleteModeledTrace.lean).
`complete_modeled_trace` supplies the three premises of
`checked_u8_physical_modeled_trace` using the generated literal source/normalized
byte check, the previously checked 485-cell constant island, and a closed
finite address-ledger calculation with explicit external addresses `2..10`.
Its proof does not feed the desired trace existence or Gate balance back as a
premise. The result is one **synthetic** physical trace for every input lane
tuple, with vanishing modeled arithmetic roots and its own ideal Gate events.
The pinned constant value table came from one native diagnostic fixture;
the theorem checks its constant-island role and does not identify the modeled
trace with an arbitrary native witness. The module comments state that native
commitment, feeder-source binding, and PCS/FRI soundness remain outside scope.
No Lean build or kernel replay of this new corollary had completed at review
time; this section is source inspection only.
