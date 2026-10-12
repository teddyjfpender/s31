# Pinned public Pair record boundary

The [source](record_pair_alias_v2.s31) computes one scalar multiplication and
returns `Pair { square: square, again: square }`. The two named result paths
are different; their descriptor entries both name the existing `square`
relation wire. For `x = 7`, the complete typed public statement claims
`x = 7`, `result.square = 49`, and `result.again = 49`, while the native
eight-word proof input is `[7, 49, 0, 0, 0, 0, 0, 0]`.

The [Lean model](../S31/Gadgets/Functional/RecordPinnedPairAliasV2.lean)
constructs the exact canonical descriptor bytes for this **one** source and
proves that its two serialized output wire names resolve to the two alias
references in the typed model. It proves distinct field paths, one output
proof word, equal native and typed projections, and rejection of changed
first or second alias claims. The
[exact-byte checker](../S31/Audit/RecordPairAliasCheck.lean) compares emitted
source and ABI bytes with the pinned Lean constants. The
[focused tests](../tests/test_record_pair_alias_check.py) run the compiler,
byte checker, canonical digest and statement projection, and descriptor and
statement mutations.

Run the formal-only check after compiling the standalone module:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.RecordPinnedPairAliasV2
python3 -m unittest discover -s tests -p 'test_record_pair_alias_check.py' -q
```

Given a completed native direct-gate package built from the pinned source,
the [package check](../scripts/check_record_pair_native_package.py) also
compares its stored source/relation, ABI artifact, sealed key digest, and a
fresh `prover inspect` result. It does not verify a proof. The native
acceptance control in `src/frontends/s31/tests/acceptance` proves and verifies
the same Pair program and checks statement mutations separately.

This fixture is a narrow byte-level and typed-flattening bridge. It does not
prove that the general Python parser, Zig record validator, AIR emitter,
polynomial commitment, or proof verifier refines the Lean model.
