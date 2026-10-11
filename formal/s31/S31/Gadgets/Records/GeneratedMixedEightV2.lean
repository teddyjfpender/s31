import S31.Gadgets.Records.NamedCodecV2

/-! Source-pinned, finite eight-word mixed record ABI v2 corpus.
The Python generator checks exact compiled source, descriptor and
statement bytes; the native parser checks the same unchanged bytes.
Lean checks only the small structured layout/claim projection. -/
-- Compiled source bytes SHA-256: 48cf2e128b4250382a619127ff748d0cf1b062c7f6ba3c50e91117e1d690368e
-- Canonical descriptor bytes SHA-256: d5b2eb2228a71c8bc607f6e1e7c9102a8dc6444e03d76da28f90d6fcad40959c
-- Canonical statement bytes SHA-256: a304c98d6e3d2dfa3c6474267cc796210af1f3b2b007d1c71a12c5ae24deaa4d
namespace S31.Records.GeneratedMixedEightV2
open S31.Records.NamedCodecV2
open S31.Functional.RecordAbiV2
open S31.Functional.RecordLayoutValidationV2
open S31.Functional.RecordWordBoundaryV2
open S31.Functional.RecordStatementV2

def root0Layout : RawLayout := (.record 2 (fun i => if i.val = 0 then "flag" else "salt") (fun i => if i.val = 0 then (.leaf .bit 1) else (.leaf .m31 2)))
theorem root0Layout_checked : checkNativeRoot root0Layout = true := by decide
theorem root0Layout_paths : paths "request" root0Layout = [[.root "request", .field "flag"], [.root "request", .field "salt"]] := by decide
theorem root0Layout_decode : decode "request" root0Layout [⟨[.root "request", .field "flag"], [1]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩] = some [[1], [5, 6]] := by decide
def root1Layout : RawLayout := (.leaf .m31 4)
theorem root1Layout_checked : checkNativeRoot root1Layout = true := by decide
theorem root1Layout_is_private : encodeInput .priv "x" root1Layout (fun _ => block [1, 2, 3, 4]) = [] := by decide
def root2Layout : RawLayout := (.record 3 (fun i => if i.val = 0 then "flag" else if i.val = 1 then "y" else "again") (fun i => if i.val = 0 then (.leaf .bit 1) else if i.val = 1 then (.leaf .m31 4) else (.leaf .m31 4)))
theorem root2Layout_checked : checkNativeRoot root2Layout = true := by decide
theorem root2Layout_paths : paths "result" root2Layout = [[.root "result", .field "flag"], [.root "result", .field "y"], [.root "result", .field "again"]] := by decide
theorem root2Layout_decode : decode "result" root2Layout [⟨[.root "result", .field "flag"], [1]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178712, 555828162]⟩] = some [[1], [2076908689, 937667208, 532178712, 555828162], [2076908689, 937667208, 532178712, 555828162]] := by decide

def sourceInputWires : List String := ["_s31_abi_input_0", "_s31_abi_input_1", "x"]
def descriptorInputWires : List String := ["_s31_abi_input_0", "_s31_abi_input_1", "x"]
theorem exact_input_wire_order : descriptorInputWires = sourceInputWires := by decide
def sourceOutputWires : List String := ["_s31_abi_input_0", "y"]
def distinctResultWires : List String := ["_s31_abi_input_0", "y"]
theorem exact_distinct_result_order : distinctResultWires = sourceOutputWires := by decide

def leafDescriptors : List (Descriptor 4) := [⟨[.root "request", .field "flag"], .bit, 1, 0⟩, ⟨[.root "request", .field "salt"], .m31, 2, 1⟩, ⟨[.root "result", .field "flag"], .bit, 1, 0⟩, ⟨[.root "result", .field "y"], .m31, 4, 3⟩, ⟨[.root "result", .field "again"], .m31, 4, 3⟩]
def honestClaims : List Claim := [⟨[.root "request", .field "flag"], [1]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩, ⟨[.root "result", .field "flag"], [1]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178712, 555828162]⟩]
def publicInputRefs : List (Fin 4) := [0, 1]
def distinctOutputRefs : List (Fin 4) := [0, 3]
theorem honest_eight_words :
    admitStatement leafDescriptors honestClaims publicInputRefs distinctOutputRefs =
      some [1, 5, 6, 1, 2076908689, 937667208, 532178712, 555828162] := by decide
theorem checked_bit_alias_split_rejected :
    admitStatement leafDescriptors [⟨[.root "request", .field "flag"], [1]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩, ⟨[.root "result", .field "flag"], [0]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178712, 555828162]⟩]
      publicInputRefs distinctOutputRefs = none := by decide
theorem checked_multilane_result_alias_split_rejected :
    admitStatement leafDescriptors [⟨[.root "request", .field "flag"], [1]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩, ⟨[.root "result", .field "flag"], [1]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178713, 555828162]⟩]
      publicInputRefs distinctOutputRefs = none := by decide
theorem out_of_range_bit_rejected :
    admitStatement leafDescriptors [⟨[.root "request", .field "flag"], [2]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩, ⟨[.root "result", .field "flag"], [1]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178712, 555828162]⟩]
      publicInputRefs distinctOutputRefs = none := by decide
theorem consistent_bit_change_is_new_statement :
    admitStatement leafDescriptors [⟨[.root "request", .field "flag"], [0]⟩, ⟨[.root "request", .field "salt"], [5, 6]⟩, ⟨[.root "result", .field "flag"], [0]⟩, ⟨[.root "result", .field "y"], [2076908689, 937667208, 532178712, 555828162]⟩, ⟨[.root "result", .field "again"], [2076908689, 937667208, 532178712, 555828162]⟩]
      publicInputRefs distinctOutputRefs = some [0, 5, 6, 0, 2076908689, 937667208, 532178712, 555828162] := by decide
end S31.Records.GeneratedMixedEightV2
