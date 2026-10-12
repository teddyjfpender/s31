# Independent case07 fixed-root recommit review

Review target: `72ddde2` (`Recommit explicit alias fixed cells to sealed PCS root`).

## Result

No blocker found for the stated **case07 diagnostic equality** claim. I reviewed the implementation and controls independently. I did not rerun the native package build, because a concurrent timed cost trial needed uncontended machine time; the author ran that focused fresh-package test. My local static fixture check, `python3 src/frontends/s31/tools/formal/alias8_native_fixture.py --check`, passed.

## What the code binds

`public_fixed_commitment.rootFromWords` accepts exactly eight columns of 512 canonical M31 words, preserving column order and row order. Its commitment path matches `stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig` `Circuit.preprocessedRoot`: eight ordered `ColumnEvaluation`s at log size 9, `prepareColumnsForCommitBorrowedForBackend` with `HostMerkleBackend`, blowup 1 and `.never` retention, followed by `CommitmentTreeProver` with `Blake2sM31MerkleChannel.MerkleHasher`. This is also the same preparation and Merkle path used by the production PCS commit operation for the corresponding parameters. The new CLI passes only parsed explicit words into that path; it does not copy or decode the expected root into the computation.

The test gets its explicit columns from the checked-in case07 physical export. Before recommitting, `roster.check_case` parses the source and reconstructs **all** 512 fixed rows with `exact_direct_gate_schedule`, including read multiplicities, then compares every cell of both the fixture and topology to that independent schedule. It also checks source, normalized form, canonical IR, row provenance, 4096-cell digest and sealed root against pinned values. `lean_fixture.render()` checks the same diagnostic fixture against its checked-in Lean literals. The test verifies the package artifact hashes and source digest, obtains a fresh `inspect-topology` export from its source-bound prover, and compares its eight columns and root with the checked fixture and sealed key. Finally, the new CLI recommits those explicit fixture columns and compares the resulting root with the sealed key. Thus the equality check does not simply pass the sealed root back to itself; it recomputes a root from the cells.

The four valid-shape mutations each affect a real fixed cell or column ordering: selector `[0][16]`, source address `[4][0]`, constant-island multiplicity `[7][16]`, and swapping distinct address columns 4 and 5. They must each produce a root different from the sealed one. The noncanonical word and short-column controls must fail at their stated validation errors. Static inspection confirmed row 16 lies in the case07 constant island, all eight source columns have length 512, and columns 4 and 5 differ.

## Scope

This binds a **pinned uncommitted diagnostic export** to its fixed-column PCS root for one source program. It does not authenticate arbitrary proof openings, prove the hash function collision resistant, or establish FRI/LogUp soundness. The CLI deliberately accepts untrusted columns and produces a diagnostic root; it is not a verifier. The static Python schedule and Lean literals are checked against a fixture and current source parser, not formally proven equivalent to the Zig circuit builder for every S31 program.
