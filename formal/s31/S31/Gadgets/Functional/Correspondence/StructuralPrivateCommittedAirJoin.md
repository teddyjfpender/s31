# Private input to committed direct-Gate cells: finite audit

Run from the repository root after installing the pinned Stwo submodule and
building the Lean structural checker described in
[StructuralCommittedAirJoin.md](StructuralCommittedAirJoin.md):

```sh
python3 -B formal/s31/tests/audit/structural_private_committed_air_join.py
```

The handwritten example is:

```s31
circuit private_square(public x: [m31; 4], private y: [m31; 4])
    -> public [m31; 4] {
    let pair = (x, y);
    let d = pair.0 - pair.1;
    let z = d .* d;
    z
}
```

For the audit assignment, `x = [5,8,13,21]` and `y = [1,3,5,8]`, so
`d = [4,5,8,13]` and the public result is `z = [16,25,64,169]`.
The tuple is a source-only projection and creates no AIR row. The
source-to-graph gate checks the exact source, typed tree, normalized
relation, assignment, and public statement. Its graph identifies the unique
pointwise multiplication gate that produces `z`. The physical audit derives
all 512 Gate rows from that checked graph, including the selected private
multiplication row, then checks all 4,096 fixed and 6,144 base cells against
the installed `writeBase` writer inside a **test-only Zig executable**. It
recommits the source-derived cells using native PCS code and compares both
roots to the exact proof accepted by the generated native verifier.

The production `inspect-physical-rows` and `inspect-physical-root` commands
must reject the private assignment; the test verifies both denials. The
private graph and expected cell roster are stored under a temporary directory
with owner-only access and deleted when the test exits. The test executable
prints only a pass/fail count. It also decodes the accepted proof, confirms
its fixed and main roots, changes one queried value in the main tree's output
column, and reserializes an otherwise unchanged proof. The generated native
verifier rejects that well-formed opening mutation with `RootMismatch`.
No production private-row export is added.

This is one transparent proof profile. Here `private` keeps `y` out of the
public statement; it **does not promise zero knowledge** or hide `y` from
someone who analyzes proof openings. The test shows finite honest-prover
cell and commitment-root correspondence, with mutations of source-derived
cells, claimed roots, accepted proof roots, and one sampled opening rejected.
It does not prove cryptographic PCS binding, equality of all sampled proof
openings to independently evaluated low-degree extensions, or general
compiler correctness. Those remain release blockers.
