# Independent static review: public record ABI v2

Review target: S31 staging through `6933095`. This was a read-only agent
review. It did not compile Lean, run native proofs, or establish a formal
end-to-end refinement.

The reviewer found no concrete verifier bypass in the inspected version-2
path. The Zig validator checks the declared type tree, tagged field and tuple
paths, root visibility and input order, unique output order, alias agreement,
canonical M31 words and the eight-word proof statement. The native runtime
checks the sealed ABI digest before proof bytes, rebuilds circuit and
component identity, and restricts public one-call chip admission to the
declared source shape. The Python package verifier re-lowers text and checks
sealed source bytes. Its existing independent correspondence certificate is
for a bounded version-1 direct-gate fragment and must not be cited as a
version-2 record ABI proof.

The Lean `RecordAbiV2` module currently models **already validated** leaf
blocks: width-aware flattening and decoding, public/private projection and
the eight-word budget. General tagged-path injectivity is an assumption of
`ValidatedPaths`; only a two-field fixture proves it. Canonical JSON, source
digest, key binding, production `claimedWords`, compiler erasure and native
AIR/PCS acceptance remain outside that theorem.

Release evidence still required: run `acceptance_record_chip_v2.py` and
`acceptance_record_inputs_v2.py` on the pinned integration stack, including
their changed-source, key, alias, path, width, visibility, order, noncanonical
word and malformed JSON controls; compile the imported Lean module; and
refresh the formal proof inventory and source bindings. Later formal work
should connect the production descriptor and canonical claim parser to the
Lean word projection, then connect those words to authenticated public AIR
cells. The standalone `record_v2.py` layout codec is documented separately
from the proof-bound `binding_v2.py` codec and has no production call sites.

This is a **conditional static GO for testing**, not a release sign-off.
