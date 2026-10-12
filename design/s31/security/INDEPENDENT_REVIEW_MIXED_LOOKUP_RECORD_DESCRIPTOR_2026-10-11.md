# Independent review: mixed lookup count and record descriptor v2

Reviewed on 2026-10-11 at `8da0de1`: `SourceMixedLookupBound.lean`,
`SourceMixedFixedWeightBridge.lean`, `RecordDescriptorValidationV2.lean`,
their generated N1/N8 fixed-row fixture, the N1..8 native producer-roster
fixture, and the production record ABI validator. This is a source and
theorem-premise review, not an assessment of the entire prover or verifier.

## Findings

| Severity | Finding | Consequence |
| --- | --- | --- |
| Blocking for an end-to-end soundness claim; already declared by the modules | The lookup bound is conditional on an ideal source shape and fixed lists. `SourceMixedLookupBound.lean:34-40` introduces `SourceShape`; `:202-209` assumes it and a false exact permutation; `:286-295` assumes a closed rational sum. `SourceMixedFixedWeightBridge.lean:38-60` assumes the modeled rows' ordered multiplicities equal the native export. No theorem derives these premises from accepted PCS openings, the native AIR, or a pre-challenge committed witness. | The `36,491,868 / |QM31|` figure is an ideal fixed-roster challenge bound. It is not a native proof soundness bound or a Fiat–Shamir bound. Keep it labeled conditional until verifier acceptance is shown to imply the exact rational closure and source-to-Lean row/tuple correspondence. |
| Medium refinement gap; explicitly excluded in the Lean header | `RecordDescriptorValidationV2.lean:20-24,134-148` uses arbitrary `String` names and accepts empty or hyphenated nominal/field/root names when the other shape checks pass. Native `record_abi.zig:32-37` rejects those names. For example, a one-field result record named `""` passes `checkDescriptor`; the production parser rejects it with `InvalidRecordAbi`. | Do not use `checkDescriptor_iff` as an equivalence with native JSON validation. Add a proven identifier predicate or prove that the parser's accepted output always supplies valid names before composing the whole-descriptor theorem. |
| Low scope/documentation mismatch | `SourceMixedLookupBound.lean:173,202,241,265` requires only `N ≤ 8`, while nearby prose says one-to-eight calls. The algebraic theorem also covers `N=0` if a caller supplies `SourceShape`. | The wider theorem is safe for the count bound, but callers should not infer source admission from it. State `1 ≤ N` in the source-family contract or describe the algebraic domain as zero-to-eight. |

No count, sign, canonical-value cast, or malformed-list escape was found in
the reviewed ideal algebra. In particular, `joint_lengths` gives
`1033 + 25N` occurrences **on each side**, at most 1,233 for `N≤8`.
`joint_multiplicities_bounded` uses `List.count_le_length`, so its
less-than-`p` result does not assume distinct events. The conservative support
bound is `2·1233=2466`, and `6·2466² + 2·2466 = 36,491,868`. The Gate and
chip relation tags remain disjoint in `joint_events_canonical_tags`. The
N1/N8 bridge computes only the eighth fixed-column totals; it does not
assert equality of full modeled Gate rows or authenticated main trace cells.

## Differential probes

The following already parsed descriptor shapes were evaluated through a
temporary Lean file using `checkDescriptor`, and corresponding JSON programs
were fed to the production `record-descriptor-parser-corpus` executable. The
Zig corpus runner required rejected cases to fail specifically with
`InvalidRecordAbi`; an unrelated parse or relation failure failed the probe.

| Case | Lean shape checker | Native parser | Result |
| --- | --- | --- | --- |
| Zero input roots; one result record | accept | accept | aligned |
| Empty nominal record name | accept | reject | lexical gap |
| Empty field name | accept | reject | lexical gap |
| Hyphenated nominal name | accept | reject | lexical gap |
| Tuple nested below a result record | accept | accept | aligned |
| Tuple at the top-level result root | reject | reject | aligned |
| Result root renamed from `result` | reject | reject | aligned |
| Repeated nominal name with different fields | reject | reject | aligned |
| 1,024 total input/result leaves | permitted by the `≤1024` check | accept | boundary aligned |
| 1,025 total input/result leaves | rejected by `overBudget_rejected` | reject | boundary aligned |

The concrete Lean probe returned
`[true, true, true, true, false, false, false]` for, in order, zero inputs,
empty nominal, empty field, nested tuple, top-level tuple, wrong result name,
and repeated nominal mismatch. The native ten-case corpus returned three accepted
and seven rejected. `checked_global_budget` and `overBudget_rejected`
establish the Lean budget implications for arbitrary descriptors; the native
probe exercised both sides of the boundary with 1,023 or 1,024 distinct
private scalar input roots plus one result leaf. This does not exercise
statement words, relation-wire aliases, or the descriptor digest.

Reproduce the checked-in gates from the repository root:

```sh
cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedLookupBound S31.Gadgets.Air.SourceMixedFixedWeightBridge S31.Gadgets.Functional.RecordDescriptorValidationV2
cd ../..
python3 -m unittest src/frontends/s31/tests/python/generated/test_lean_mixed_fixed_fixture.py
python3 formal/s31/scripts/check_record_layout_corpus_v2.py
zig build --build-file src/frontends/s31/build.zig test-mixed-producer-roster -Doptimize=ReleaseFast -j1 --summary all
```

These passed: focused Lean build 3,386 jobs; seven fixed-row mutation tests;
13 programs, 28 checked record roots and four rejected layout mutations;
native producer-roster fixture 2/2 tests. An independent read of the native
N1/N8 JSON export found 512 rows of width eight in each case and eighth-column
totals 1,041 and 1,097, matching `1033+8N`. The generated fixture also
checks all eight cells' canonicality, all 512 opcode partitions, a full-row
digest, and selected hand-derived rows. These are honest-emitter checks.

For a minimal Lean lexical repro, save the following as `/tmp/s31-name-probe.lean`
and run `cd formal/s31 && lake env lean /tmp/s31-name-probe.lean`:

```lean
import S31.Gadgets.Functional.RecordDescriptorValidationV2
open S31.Functional.RecordDescriptorValidationV2
open S31.Functional.RecordAbiV2
def bad : Descriptor :=
  { inputs := [], result := { name := "result", layout :=
      .record "bad-hyphen" 1 (fun _ => "") (fun _ => .leaf .m31 1) } }
example : checkDescriptor bad = true := by decide
```

For the matching native lexical rejection, from the repository root:

```sh
python3 - <<'PY'
import json
from pathlib import Path
source = {
    "version": 2, "name": "review", "inputs": [],
    "nodes": [{"name": "out", "op": "constant", "constant": 0, "length": 1}],
    "assertions": [], "public_outputs": ["out"],
    "public_abi": {"schema": "s31-public-record-boundary-v2", "inputs": [],
        "result": {"name": "result", "type": {"record": "bad-hyphen",
            "fields": [{"name": "out", "type": {"kind": "m31", "length": 1}}]},
            "leaves": [{"path": [{"root": "result"}, {"field": "out"}],
                        "wire": "out", "kind": "m31", "length": 1}]}}
}
corpus = {"schema": "s31-record-descriptor-native-corpus-v2", "cases": [
    {"label": "lexical", "source": json.dumps(source), "expected_valid": False}]}
Path("/tmp/s31-review-name-corpus.json").write_text(json.dumps(corpus))
PY
zig build --build-file src/frontends/s31/build.zig record-descriptor-parser-corpus -Doptimize=ReleaseFast -j1 -- /tmp/s31-review-name-corpus.json
```

## Remaining proof obligations

1. Relate validated native JSON descriptors and first-order relation wires
   to `NamedLayout`, including names, ordered leaves, visibility, exact wire
   aliases, and nominal serialization. Then relate canonical descriptor
   bytes/digest and public statement words to verifier claims.
2. Relate the source-pinned 512 fixed rows, all witness rows, chip rows and
   bridge rows to the typed `Boundary` and `NativeRow` lists. N1/N8 full
   fixed-row exports and N1..8 producer-roster tests cover the honest emitter,
   not arbitrary accepted proofs.
3. Prove accepted native AIR/LogUp/PCS/FRI claims imply the exact signed
   rational closure used by `source_closed_or_error`, with the native fraction
   scaling and signs, and establish pre-challenge witness binding. Analyze
   the actual Fiat–Shamir transcript before converting the ideal pair count
   to a production failure probability.
