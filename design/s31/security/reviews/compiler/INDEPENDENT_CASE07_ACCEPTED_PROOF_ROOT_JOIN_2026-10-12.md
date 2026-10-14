# Independent case07 accepted-proof root join review

Reviewed commits: `72ddde2`, `537d37e`, and `db3b67c`.

## Result

No blocker found for the stated **one case07 fixture/proof-byte regression**. The fresh native result recorded in the acceptance README is an author-run observation; this review did not repeat the package build or proof. I independently ran `alias8_native_fixture.py --check` and `full_native_roster.py --plan-only`; both passed.

## Checked binding

`roster.check_case` reconstructs all 512 fixed rows from the admitted case07 source schedule and compares every column with the pinned diagnostic. It also checks the source, normalized relation, canonical IR, full fixed-column digest, arithmetic rows, and address/value ledger. `lean_fixture.render()` rechecks the pinned fixture against the checked-in Lean literals. The test verifies package artifact hashes and the source text digest, then compares fresh `inspect-topology` cells and sealed root with the admitted fixture. The new native command receives the literal eight 512-word columns, checks shape and canonical M31 words, and uses the production PCS preparation and Merkle path to compute a root. It does not take the expected root as input.

`s31.trial` runs the generated prover and native verifier against the source-derived public assignment and sealed key; a failed verifier call raises before the trial report can be returned. It also requires rejection of a changed public statement. The join requires the expected trial schema, program hash, explicit acceptance, expected changed-output field, positive proof size, and equality between saved proof bytes and the trial's size and SHA-256 report **before** decoding any root. The bounded `proof_roots` parser checks the direct-Gate magic, minimum length, five exact PCS parameters, absent optional lifting parameter, four commitments, canonical bounded varints, and available 64 root bytes. It then reads commitment zero from the already accepted proof and compares it with both the native recommitment and sealed key. The parser intentionally does not validate the rest of the proof; the preceding generated verifier call does that.

The controls cover changed selector, source address, multiplicity, and fixed-column order, each requiring a different recommitted root. A noncanonical word and a short column must fail native input validation. A changed *decoded root value* must fail the three-way comparison; it is not submitted as a forged proof, and the code says so. The README's reported three equal roots, 55,911-byte proof, proof SHA-256, and six controls match the code's output contract, but are not independently reproduced by this review.

## Boundary

This is a case07 fixture/root/proof-byte regression tied to one accepted native proof. It is not a general compiler correspondence theorem, a proof that every PCS opening is authenticated to the displayed rows, or a formal proof of Merkle, FRI, or LogUp soundness. The Python source schedule and the native emitter are compared at this finite fixture; their equivalence for all programs remains open.
