# Direct Gate generated-byte fixture review

Scope: commits `b036500` and `4c74edc`, the four-sample native acceptance
harness, and the verifier path it exercises.

## Correspondence checked

The 384-case positional DAG corpus has an independent recurrence oracle.
Seventeen selected exact source byte strings are parsed in Lean. For the four
native samples, Lean also checks the **literal normalized JSON bytes** and
compact canonical IR bytes against the source certificate; altered normalized
opcode and canonical-byte controls fail. The Python renderer supplies those
literal bytes, so the kernel check proves the stated byte relation but does
not independently compute SHA-256.

The native harness compares `source.s31.json` byte for byte against the
renderer serialization. `check_package` independently parses the source,
computes SHA-256 of its canonical IR bytes, compares that value against the
package manifest, verification key, cost report, and component manifest, and
checks the exported direct Gate topology and fixed cells against source row
positions. The package manifest's IR digest is copied from native prover
`inspect`; the component manifest is native inspection output. These
comparisons therefore cross the Python and Zig implementations, rather than
just comparing two fields produced by one Python function.

`s31.trial` constructs a real native proof and invokes the installed native
verifier. The verifier first requires the supplied key to equal its embedded
key byte for byte; `validateKey` then reconstructs canonical IR from its
embedded normalized source and recompiles the fixed circuit root. The
positive proof and changed-public-statement control therefore test native
admission, but a changed external key by itself would stop at the byte seal.

## Added negative control

For the one-Gate sample, the acceptance harness now changes the canonical IR
digest in the key and its component manifest, **builds a new verifier with
that changed key embedded**, supplies the identical changed external key,
and runs the original valid proof and statement. It requires the native
`InvalidVerificationKey` result. This bypasses the easy byte-seal rejection
and tests the independent canonical rebuild in `validateKey`. The other three
samples retain their positive proof and changed-public-claim controls.

## Limits and wording

`check_static_mutations` changes generator metadata while keeping source text
fixed; those ten rejections check metadata consistency. The Lean fixture's
separate mutated source byte strings test source changes. The native samples
do not prove that the verifier authenticated every fixed or witness cell in
the way the Lean model assumes. The package manifest is metadata checked by
the Python package checker; it is not itself the native verifier's transcript
input. The verifier uses its embedded source and key, whose profile and
component fields are validated before proof verification. The native proof
path still relies on the AIR evaluator, lookup argument, PCS/FRI, and
Fiat–Shamir assumptions. This review found no vacuous positive correspondence
check in the four-sample harness; its key mutation needed the re-embedding
control above to reach the intended native check.
