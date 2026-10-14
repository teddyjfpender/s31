# From the control proof's component claims to Gate trace cells

The verifier receives eight public words, eleven component interaction claims,
and four PCS roots. Its final Gate lookup equation adds the eleven claims to
the reciprocal terms for the eight public words and the fixed `u` wire. A
zero sum alone says little about where those eleven claims came from. This
slice identifies them with the component interactions reconstructed from a
specific accepted control proof's committed cells.

## One concrete proof

The noninstalled `control-claim-trace` Zig executable rebuilds the transparent
control circuit from its normalized source and a private assignment. It
checks that the value-bearing and value-free compiler paths have the same
topology, pads them identically, and uses the installed generic circuit
`writeTrace` and `writeInteractionTrace` functions. It then:

1. Checks the eight output cells against the public-only statement.
2. Recommits every base column and compares tree 1's root with the proof.
3. Replays the verifier's transcript through the accepted interaction nonce
   to obtain the exact challenges.
4. Recomputes all eleven component interaction sums from those base cells,
   compares every claimed sum in the proof, and checks the public Gate sum.
5. Recommits every interaction column and compares tree 2's root with the proof.
6. Enumerates every active output tuple produced by QM31 operations, triple
   XOR, M31-to-u32 conversion, and Blake G. It checks each tuple's address,
   limbs, and negative fixed multiplicity against the actual base and fixed
   cells, and rejects duplicate active producer addresses.

The current finite proof has **329** active QM31 producers, **5** conversion
producers, and **0** active triple XOR or Blake G producers. Zero rows are
checked through their fixed multiplicity cells, not inferred from the source
program's apparent operations. Table components and `eq` supply no Gate
output tuples in the pinned engine revision; the test executable is compiled
against that gitlink. The diagnostic emits counts and match booleans only.
The packaged prover and verifier gain no private trace export.

`control_claim_trace_audit.py` first verifies the sealed package, checks the
exact Lean source derivation, and runs the packaged native verifier against
the proof and public-only statement. It also checks the local engine checkout
matches the repository gitlink before invoking the test executable. An
unused private branch value changed from `2` to `3` makes the reconstructed
base root differ. Changing one canonical component claim byte makes the
reconstructed interaction claim differ. The finite control runner checks
both rejections.

## What Lean adds

`ControlGadgetClaimTrace.lean` proves that a six-word Gate event and its
seven-word zero-padded native verifier event have the same reciprocal term.
It lifts this equality to the complete nine-event public list. It then
constructs the external producer roster from the three non-QM31 producer
lists, removing the earlier free `externalProducerCoverage` premise. Given
eleven claims equal to the signed event sums of the committed rows and a
zero native final sum, it derives `GoodGateClosure.closed`; the latter is no
longer an unrelated premise. The existing global Gate theorem then yields
the public event-to-wire equalities.

The arbitrary-proof theorem still assumes that the eleven accepted claims
equal the component sums of authenticated cells, that the fixed producer
roster has unique addresses and matched positive AIR rows, and that the
challenge avoids the explicit exceptional sets. The finite diagnostic checks
these relationships for one honestly generated accepted proof. It does not
establish PCS/FRI authentication for every accepted proof, global LogUp
soundness, or a general compiler correspondence theorem. The release gate
remains closed.

## Reproduce

After producing the transparent `control_air` package, proof, private
assignment, and public-only statement:

```sh
python3 scripts/compiler/control_claim_trace_controls.py \
  "$PACKAGE" "$PROOF" "$STATEMENT" "$ASSIGNMENT" \
  --lean-checker formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.ControlGadgetClaimTrace)
```
