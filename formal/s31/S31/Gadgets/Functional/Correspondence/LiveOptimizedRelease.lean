import S31.Gadgets.Functional.Correspondence.OptimizedSourceAirRows

/-!
The exact five-let source from `release_optimized4/functional.s31` and the
normalized JSON/canonical IR bytes emitted by the production frontend. Both
`c` and its commutative duplicate `d` feed `e`, so deleting an unused let
cannot explain the compact four-gate result. `checkBytes` independently
reparses all three byte streams before applying the modeled Gate AIR theorem.
This remains conditional on the modeled rows and public boundaries; it does
not prove native Zig emission or PCS/FRI authentication.
-/

namespace S31.Functional.Correspondence.LiveOptimizedRelease

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.OptimizedTextBytes
open S31.Functional.Correspondence.OptimizedSourceAirRows

def sourceBytes : SSATextBytes.Token := SSATextBytes.token
  "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {\n    let a = x + x;\n    let b = x .* x;\n    let c = a + b;\n    let d = b + a;\n    let e = c + d;\n    e\n}\n"

def normalizedBytes : SSATextBytes.Token := SSATextBytes.token
  "{\n  \"assertions\": [],\n  \"inputs\": [\n    {\n      \"kind\": \"m31\",\n      \"length\": 4,\n      \"name\": \"x\",\n      \"visibility\": \"public\"\n    }\n  ],\n  \"name\": \"reverse_share\",\n  \"nodes\": [\n    {\n      \"lhs\": \"x\",\n      \"name\": \"a\",\n      \"op\": \"add\",\n      \"rhs\": \"x\"\n    },\n    {\n      \"lhs\": \"x\",\n      \"name\": \"b\",\n      \"op\": \"mul\",\n      \"rhs\": \"x\"\n    },\n    {\n      \"lhs\": \"a\",\n      \"name\": \"c\",\n      \"op\": \"add\",\n      \"rhs\": \"b\"\n    },\n    {\n      \"lhs\": \"b\",\n      \"name\": \"d\",\n      \"op\": \"add\",\n      \"rhs\": \"a\"\n    },\n    {\n      \"lhs\": \"c\",\n      \"name\": \"e\",\n      \"op\": \"add\",\n      \"rhs\": \"d\"\n    }\n  ],\n  \"public_outputs\": [\n    \"e\"\n  ],\n  \"version\": 1\n}\n"

def canonicalBytes : SSATextBytes.Token := SSATextBytes.token
  "{\"version\":1,\"nodes\":[{\"tag\":\"input\",\"kind\":\"m31\",\"length\":4,\"lhs\":null,\"rhs\":null,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":\"x\",\"visibility\":\"public\"},{\"tag\":\"add\",\"kind\":\"m31\",\"length\":4,\"lhs\":0,\"rhs\":0,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null},{\"tag\":\"mul\",\"kind\":\"m31\",\"length\":4,\"lhs\":0,\"rhs\":0,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null},{\"tag\":\"add\",\"kind\":\"m31\",\"length\":4,\"lhs\":1,\"rhs\":2,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null},{\"tag\":\"add\",\"kind\":\"m31\",\"length\":4,\"lhs\":3,\"rhs\":3,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null}],\"assertions\":[],\"public_outputs\":[{\"name\":\"e\",\"id\":4}]}"

def compact : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := false },
       { id := 2, lhs := 0, rhs := 0, multiply := true },
       { id := 3, lhs := 1, rhs := 2, multiply := false },
       { id := 4, lhs := 3, rhs := 3, multiply := false }],
    output := 4 }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem exact_source_normalized_and_canonical_bytes :
    checkBytes sourceBytes normalizedBytes canonicalBytes = some compact := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem five_live_lets_share_four_producers :
    (parseBytes sourceBytes).map (·.raw.instructions.length) = some 5 ∧
    (parseBytes sourceBytes).map (·.compact.instructions.length) = some 4 := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem exact_compact_operation_rows :
    (expectedCells compact (compiledAddRows compact)).map
      ColumnCell.traceRow = [3, 503, 4, 5] ∧
    (expectedCells compact (compiledAddRows compact)).map
      ColumnCell.out = [23, 24, 25, 26] := by decide

/-- For every four-lane input and any locally accepted modeled Gate rows,
the selected public output equals the exact source-byte denotation. -/
theorem accepted_modeled_rows_bind_public_claim
    (observedCells : List ColumnCell) (wire : Nat → Quad)
    (input claimed : Lanes)
    (hcells : observedCells = expectedCells compact (compiledAddRows compact))
    (hinput : InputBoundary compact (compiledAddRows compact) wire input)
    (hlocal : ∀ cell ∈ observedCells, cellAccepts cell wire)
    (houtput : OutputBoundary compact (compiledAddRows compact) wire claimed) :
    denotation sourceBytes input = some claimed := by
  exact optimized_source_public_output_sound sourceBytes normalizedBytes
    canonicalBytes compact observedCells wire input claimed
    exact_source_normalized_and_canonical_bytes hcells hinput hlocal houtput

end S31.Functional.Correspondence.LiveOptimizedRelease
