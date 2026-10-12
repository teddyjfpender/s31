import S31.Gadgets.Functional.RecordStatementV2

/-! Generated, source-pinned ABI statement corpus. Regenerate with
`general_statement_refinement_v2.py --write`; default mode checks exact bytes.
The general theorem lives in RecordStatementV2.lean. Each example here
kernel-checks one independently compiled source/statement pair. -/
-- Source corpus SHA-256: a5e2883c146957858828404f47afec1251a4c8b99929c0ed310bb56a04a2305c
namespace S31.Functional.GeneratedRecordStatementCorpusV2
open RecordAbiV2 RecordStatementV2

-- pair_1: 3 named public leaves, 1 distinct wires.
def case0_pair_1Descriptors : List (Descriptor 1) :=
  [⟨[.root "x"], .m31, 1, 0⟩, ⟨[.root "result", .field "a"], .m31, 1, 0⟩, ⟨[.root "result", .field "b"], .m31, 1, 0⟩]
def case0_pair_1Claims : List Claim :=
  [⟨[.root "x"], [30]⟩, ⟨[.root "result", .field "a"], [30]⟩, ⟨[.root "result", .field "b"], [30]⟩]
def case0_pair_1Inputs : List (Fin 1) := [0]
def case0_pair_1Outputs : List (Fin 1) := [0]
theorem case0_pair_1_accepted :
    admitStatement case0_pair_1Descriptors case0_pair_1Claims
      case0_pair_1Inputs case0_pair_1Outputs = some [30, 30, 0, 0, 0, 0, 0, 0] := by decide
theorem case0_pair_1_consistent_change :
    admitStatement case0_pair_1Descriptors [⟨[.root "x"], [31]⟩, ⟨[.root "result", .field "a"], [31]⟩, ⟨[.root "result", .field "b"], [31]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = some [31, 31, 0, 0, 0, 0, 0, 0] := by decide
theorem case0_pair_1_path_rejected :
    admitStatement case0_pair_1Descriptors [⟨[.root "wrong_root"], [30]⟩, ⟨[.root "result", .field "a"], [30]⟩, ⟨[.root "result", .field "b"], [30]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = none := by decide
theorem case0_pair_1_width_rejected :
    admitStatement case0_pair_1Descriptors [⟨[.root "x"], [30, 1]⟩, ⟨[.root "result", .field "a"], [30]⟩, ⟨[.root "result", .field "b"], [30]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = none := by decide
theorem case0_pair_1_range_rejected :
    admitStatement case0_pair_1Descriptors [⟨[.root "x"], [2147483647]⟩, ⟨[.root "result", .field "a"], [30]⟩, ⟨[.root "result", .field "b"], [30]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = none := by decide
theorem case0_pair_1_missing_leaf_rejected :
    admitStatement case0_pair_1Descriptors [⟨[.root "x"], [30]⟩, ⟨[.root "result", .field "a"], [30]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = none := by decide
theorem case0_pair_1_split_alias_rejected :
    admitStatement case0_pair_1Descriptors [⟨[.root "x"], [30]⟩, ⟨[.root "result", .field "a"], [31]⟩, ⟨[.root "result", .field "b"], [30]⟩]
      case0_pair_1Inputs case0_pair_1Outputs = none := by decide

-- pair_2: 3 named public leaves, 1 distinct wires.
def case1_pair_2Descriptors : List (Descriptor 1) :=
  [⟨[.root "x"], .m31, 2, 0⟩, ⟨[.root "result", .field "a"], .m31, 2, 0⟩, ⟨[.root "result", .field "b"], .m31, 2, 0⟩]
def case1_pair_2Claims : List Claim :=
  [⟨[.root "x"], [59, 60]⟩, ⟨[.root "result", .field "a"], [59, 60]⟩, ⟨[.root "result", .field "b"], [59, 60]⟩]
def case1_pair_2Inputs : List (Fin 1) := [0]
def case1_pair_2Outputs : List (Fin 1) := [0]
theorem case1_pair_2_accepted :
    admitStatement case1_pair_2Descriptors case1_pair_2Claims
      case1_pair_2Inputs case1_pair_2Outputs = some [59, 60, 59, 60, 0, 0, 0, 0] := by decide
theorem case1_pair_2_consistent_change :
    admitStatement case1_pair_2Descriptors [⟨[.root "x"], [60, 60]⟩, ⟨[.root "result", .field "a"], [60, 60]⟩, ⟨[.root "result", .field "b"], [60, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = some [60, 60, 60, 60, 0, 0, 0, 0] := by decide
theorem case1_pair_2_path_rejected :
    admitStatement case1_pair_2Descriptors [⟨[.root "wrong_root"], [59, 60]⟩, ⟨[.root "result", .field "a"], [59, 60]⟩, ⟨[.root "result", .field "b"], [59, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = none := by decide
theorem case1_pair_2_width_rejected :
    admitStatement case1_pair_2Descriptors [⟨[.root "x"], [59, 60, 1]⟩, ⟨[.root "result", .field "a"], [59, 60]⟩, ⟨[.root "result", .field "b"], [59, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = none := by decide
theorem case1_pair_2_range_rejected :
    admitStatement case1_pair_2Descriptors [⟨[.root "x"], [2147483647, 60]⟩, ⟨[.root "result", .field "a"], [59, 60]⟩, ⟨[.root "result", .field "b"], [59, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = none := by decide
theorem case1_pair_2_missing_leaf_rejected :
    admitStatement case1_pair_2Descriptors [⟨[.root "x"], [59, 60]⟩, ⟨[.root "result", .field "a"], [59, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = none := by decide
theorem case1_pair_2_split_alias_rejected :
    admitStatement case1_pair_2Descriptors [⟨[.root "x"], [59, 60]⟩, ⟨[.root "result", .field "a"], [60, 60]⟩, ⟨[.root "result", .field "b"], [59, 60]⟩]
      case1_pair_2Inputs case1_pair_2Outputs = none := by decide

-- pair_3: 3 named public leaves, 1 distinct wires.
def case2_pair_3Descriptors : List (Descriptor 1) :=
  [⟨[.root "x"], .m31, 3, 0⟩, ⟨[.root "result", .field "a"], .m31, 3, 0⟩, ⟨[.root "result", .field "b"], .m31, 3, 0⟩]
def case2_pair_3Claims : List Claim :=
  [⟨[.root "x"], [88, 89, 90]⟩, ⟨[.root "result", .field "a"], [88, 89, 90]⟩, ⟨[.root "result", .field "b"], [88, 89, 90]⟩]
def case2_pair_3Inputs : List (Fin 1) := [0]
def case2_pair_3Outputs : List (Fin 1) := [0]
theorem case2_pair_3_accepted :
    admitStatement case2_pair_3Descriptors case2_pair_3Claims
      case2_pair_3Inputs case2_pair_3Outputs = some [88, 89, 90, 88, 89, 90, 0, 0] := by decide
theorem case2_pair_3_consistent_change :
    admitStatement case2_pair_3Descriptors [⟨[.root "x"], [89, 89, 90]⟩, ⟨[.root "result", .field "a"], [89, 89, 90]⟩, ⟨[.root "result", .field "b"], [89, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = some [89, 89, 90, 89, 89, 90, 0, 0] := by decide
theorem case2_pair_3_path_rejected :
    admitStatement case2_pair_3Descriptors [⟨[.root "wrong_root"], [88, 89, 90]⟩, ⟨[.root "result", .field "a"], [88, 89, 90]⟩, ⟨[.root "result", .field "b"], [88, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = none := by decide
theorem case2_pair_3_width_rejected :
    admitStatement case2_pair_3Descriptors [⟨[.root "x"], [88, 89, 90, 1]⟩, ⟨[.root "result", .field "a"], [88, 89, 90]⟩, ⟨[.root "result", .field "b"], [88, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = none := by decide
theorem case2_pair_3_range_rejected :
    admitStatement case2_pair_3Descriptors [⟨[.root "x"], [2147483647, 89, 90]⟩, ⟨[.root "result", .field "a"], [88, 89, 90]⟩, ⟨[.root "result", .field "b"], [88, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = none := by decide
theorem case2_pair_3_missing_leaf_rejected :
    admitStatement case2_pair_3Descriptors [⟨[.root "x"], [88, 89, 90]⟩, ⟨[.root "result", .field "a"], [88, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = none := by decide
theorem case2_pair_3_split_alias_rejected :
    admitStatement case2_pair_3Descriptors [⟨[.root "x"], [88, 89, 90]⟩, ⟨[.root "result", .field "a"], [89, 89, 90]⟩, ⟨[.root "result", .field "b"], [88, 89, 90]⟩]
      case2_pair_3Inputs case2_pair_3Outputs = none := by decide

-- pair_4: 3 named public leaves, 1 distinct wires.
def case3_pair_4Descriptors : List (Descriptor 1) :=
  [⟨[.root "x"], .m31, 4, 0⟩, ⟨[.root "result", .field "a"], .m31, 4, 0⟩, ⟨[.root "result", .field "b"], .m31, 4, 0⟩]
def case3_pair_4Claims : List Claim :=
  [⟨[.root "x"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [117, 118, 119, 120]⟩]
def case3_pair_4Inputs : List (Fin 1) := [0]
def case3_pair_4Outputs : List (Fin 1) := [0]
theorem case3_pair_4_accepted :
    admitStatement case3_pair_4Descriptors case3_pair_4Claims
      case3_pair_4Inputs case3_pair_4Outputs = some [117, 118, 119, 120, 117, 118, 119, 120] := by decide
theorem case3_pair_4_consistent_change :
    admitStatement case3_pair_4Descriptors [⟨[.root "x"], [118, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [118, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [118, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = some [118, 118, 119, 120, 118, 118, 119, 120] := by decide
theorem case3_pair_4_path_rejected :
    admitStatement case3_pair_4Descriptors [⟨[.root "wrong_root"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [117, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = none := by decide
theorem case3_pair_4_width_rejected :
    admitStatement case3_pair_4Descriptors [⟨[.root "x"], [117, 118, 119, 120, 1]⟩, ⟨[.root "result", .field "a"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [117, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = none := by decide
theorem case3_pair_4_range_rejected :
    admitStatement case3_pair_4Descriptors [⟨[.root "x"], [2147483647, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [117, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = none := by decide
theorem case3_pair_4_missing_leaf_rejected :
    admitStatement case3_pair_4Descriptors [⟨[.root "x"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [117, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = none := by decide
theorem case3_pair_4_split_alias_rejected :
    admitStatement case3_pair_4Descriptors [⟨[.root "x"], [117, 118, 119, 120]⟩, ⟨[.root "result", .field "a"], [118, 118, 119, 120]⟩, ⟨[.root "result", .field "b"], [117, 118, 119, 120]⟩]
      case3_pair_4Inputs case3_pair_4Outputs = none := by decide

-- tuple_1_1: 4 named public leaves, 2 distinct wires.
def case4_tuple_1_1Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "pair", .tuple 0], .m31, 1, 0⟩, ⟨[.root "req", .field "pair", .tuple 1], .m31, 1, 1⟩, ⟨[.root "result", .field "copy"], .m31, 1, 0⟩, ⟨[.root "result", .field "tail"], .m31, 1, 1⟩]
def case4_tuple_1_1Claims : List Claim :=
  [⟨[.root "req", .field "pair", .tuple 0], [146]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [146]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
def case4_tuple_1_1Inputs : List (Fin 2) := [0, 1]
def case4_tuple_1_1Outputs : List (Fin 2) := [0, 1]
theorem case4_tuple_1_1_accepted :
    admitStatement case4_tuple_1_1Descriptors case4_tuple_1_1Claims
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = some [146, 159, 146, 159, 0, 0, 0, 0] := by decide
theorem case4_tuple_1_1_consistent_change :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [147]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [147]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = some [147, 159, 147, 159, 0, 0, 0, 0] := by decide
theorem case4_tuple_1_1_path_rejected :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "wrong_root", .field "pair", .tuple 0], [146]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [146]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = none := by decide
theorem case4_tuple_1_1_width_rejected :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [146, 1]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [146]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = none := by decide
theorem case4_tuple_1_1_range_rejected :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [2147483647]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [146]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = none := by decide
theorem case4_tuple_1_1_missing_leaf_rejected :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [146]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [146]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = none := by decide
theorem case4_tuple_1_1_split_alias_rejected :
    admitStatement case4_tuple_1_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [146]⟩, ⟨[.root "req", .field "pair", .tuple 1], [159]⟩, ⟨[.root "result", .field "copy"], [147]⟩, ⟨[.root "result", .field "tail"], [159]⟩]
      case4_tuple_1_1Inputs case4_tuple_1_1Outputs = none := by decide

-- tuple_2_1: 4 named public leaves, 2 distinct wires.
def case5_tuple_2_1Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "pair", .tuple 0], .m31, 2, 0⟩, ⟨[.root "req", .field "pair", .tuple 1], .m31, 1, 1⟩, ⟨[.root "result", .field "copy"], .m31, 2, 0⟩, ⟨[.root "result", .field "tail"], .m31, 1, 1⟩]
def case5_tuple_2_1Claims : List Claim :=
  [⟨[.root "req", .field "pair", .tuple 0], [175, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [175, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
def case5_tuple_2_1Inputs : List (Fin 2) := [0, 1]
def case5_tuple_2_1Outputs : List (Fin 2) := [0, 1]
theorem case5_tuple_2_1_accepted :
    admitStatement case5_tuple_2_1Descriptors case5_tuple_2_1Claims
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = some [175, 176, 188, 175, 176, 188, 0, 0] := by decide
theorem case5_tuple_2_1_consistent_change :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [176, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [176, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = some [176, 176, 188, 176, 176, 188, 0, 0] := by decide
theorem case5_tuple_2_1_path_rejected :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "wrong_root", .field "pair", .tuple 0], [175, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [175, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = none := by decide
theorem case5_tuple_2_1_width_rejected :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [175, 176, 1]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [175, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = none := by decide
theorem case5_tuple_2_1_range_rejected :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [2147483647, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [175, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = none := by decide
theorem case5_tuple_2_1_missing_leaf_rejected :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [175, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [175, 176]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = none := by decide
theorem case5_tuple_2_1_split_alias_rejected :
    admitStatement case5_tuple_2_1Descriptors [⟨[.root "req", .field "pair", .tuple 0], [175, 176]⟩, ⟨[.root "req", .field "pair", .tuple 1], [188]⟩, ⟨[.root "result", .field "copy"], [176, 176]⟩, ⟨[.root "result", .field "tail"], [188]⟩]
      case5_tuple_2_1Inputs case5_tuple_2_1Outputs = none := by decide

-- tuple_1_2: 4 named public leaves, 2 distinct wires.
def case6_tuple_1_2Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "pair", .tuple 0], .m31, 1, 0⟩, ⟨[.root "req", .field "pair", .tuple 1], .m31, 2, 1⟩, ⟨[.root "result", .field "copy"], .m31, 1, 0⟩, ⟨[.root "result", .field "tail"], .m31, 2, 1⟩]
def case6_tuple_1_2Claims : List Claim :=
  [⟨[.root "req", .field "pair", .tuple 0], [204]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [204]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
def case6_tuple_1_2Inputs : List (Fin 2) := [0, 1]
def case6_tuple_1_2Outputs : List (Fin 2) := [0, 1]
theorem case6_tuple_1_2_accepted :
    admitStatement case6_tuple_1_2Descriptors case6_tuple_1_2Claims
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = some [204, 217, 218, 204, 217, 218, 0, 0] := by decide
theorem case6_tuple_1_2_consistent_change :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [205]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [205]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = some [205, 217, 218, 205, 217, 218, 0, 0] := by decide
theorem case6_tuple_1_2_path_rejected :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "wrong_root", .field "pair", .tuple 0], [204]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [204]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = none := by decide
theorem case6_tuple_1_2_width_rejected :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [204, 1]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [204]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = none := by decide
theorem case6_tuple_1_2_range_rejected :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [2147483647]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [204]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = none := by decide
theorem case6_tuple_1_2_missing_leaf_rejected :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [204]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [204]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = none := by decide
theorem case6_tuple_1_2_split_alias_rejected :
    admitStatement case6_tuple_1_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [204]⟩, ⟨[.root "req", .field "pair", .tuple 1], [217, 218]⟩, ⟨[.root "result", .field "copy"], [205]⟩, ⟨[.root "result", .field "tail"], [217, 218]⟩]
      case6_tuple_1_2Inputs case6_tuple_1_2Outputs = none := by decide

-- tuple_2_2: 4 named public leaves, 2 distinct wires.
def case7_tuple_2_2Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "pair", .tuple 0], .m31, 2, 0⟩, ⟨[.root "req", .field "pair", .tuple 1], .m31, 2, 1⟩, ⟨[.root "result", .field "copy"], .m31, 2, 0⟩, ⟨[.root "result", .field "tail"], .m31, 2, 1⟩]
def case7_tuple_2_2Claims : List Claim :=
  [⟨[.root "req", .field "pair", .tuple 0], [233, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [233, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
def case7_tuple_2_2Inputs : List (Fin 2) := [0, 1]
def case7_tuple_2_2Outputs : List (Fin 2) := [0, 1]
theorem case7_tuple_2_2_accepted :
    admitStatement case7_tuple_2_2Descriptors case7_tuple_2_2Claims
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = some [233, 234, 246, 247, 233, 234, 246, 247] := by decide
theorem case7_tuple_2_2_consistent_change :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [234, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [234, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = some [234, 234, 246, 247, 234, 234, 246, 247] := by decide
theorem case7_tuple_2_2_path_rejected :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "wrong_root", .field "pair", .tuple 0], [233, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [233, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = none := by decide
theorem case7_tuple_2_2_width_rejected :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [233, 234, 1]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [233, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = none := by decide
theorem case7_tuple_2_2_range_rejected :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [2147483647, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [233, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = none := by decide
theorem case7_tuple_2_2_missing_leaf_rejected :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [233, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [233, 234]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = none := by decide
theorem case7_tuple_2_2_split_alias_rejected :
    admitStatement case7_tuple_2_2Descriptors [⟨[.root "req", .field "pair", .tuple 0], [233, 234]⟩, ⟨[.root "req", .field "pair", .tuple 1], [246, 247]⟩, ⟨[.root "result", .field "copy"], [234, 234]⟩, ⟨[.root "result", .field "tail"], [246, 247]⟩]
      case7_tuple_2_2Inputs case7_tuple_2_2Outputs = none := by decide

-- bit_1: 3 named public leaves, 2 distinct wires.
def case8_bit_1Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "flag"], .bit, 1, 0⟩, ⟨[.root "req", .field "x"], .m31, 1, 1⟩, ⟨[.root "result", .field "y"], .m31, 1, 1⟩]
def case8_bit_1Claims : List Claim :=
  [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [275]⟩]
def case8_bit_1Inputs : List (Fin 2) := [0, 1]
def case8_bit_1Outputs : List (Fin 2) := [1]
theorem case8_bit_1_accepted :
    admitStatement case8_bit_1Descriptors case8_bit_1Claims
      case8_bit_1Inputs case8_bit_1Outputs = some [1, 275, 275, 0, 0, 0, 0, 0] := by decide
theorem case8_bit_1_consistent_change :
    admitStatement case8_bit_1Descriptors [⟨[.root "req", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [275]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = some [0, 275, 275, 0, 0, 0, 0, 0] := by decide
theorem case8_bit_1_path_rejected :
    admitStatement case8_bit_1Descriptors [⟨[.root "wrong_root", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [275]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = none := by decide
theorem case8_bit_1_width_rejected :
    admitStatement case8_bit_1Descriptors [⟨[.root "req", .field "flag"], [1, 1]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [275]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = none := by decide
theorem case8_bit_1_range_rejected :
    admitStatement case8_bit_1Descriptors [⟨[.root "req", .field "flag"], [2]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [275]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = none := by decide
theorem case8_bit_1_missing_leaf_rejected :
    admitStatement case8_bit_1Descriptors [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [275]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = none := by decide
theorem case8_bit_1_split_alias_rejected :
    admitStatement case8_bit_1Descriptors [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [275]⟩, ⟨[.root "result", .field "y"], [276]⟩]
      case8_bit_1Inputs case8_bit_1Outputs = none := by decide

-- bit_2: 3 named public leaves, 2 distinct wires.
def case9_bit_2Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "flag"], .bit, 1, 0⟩, ⟨[.root "req", .field "x"], .m31, 2, 1⟩, ⟨[.root "result", .field "y"], .m31, 2, 1⟩]
def case9_bit_2Claims : List Claim :=
  [⟨[.root "req", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [304, 305]⟩]
def case9_bit_2Inputs : List (Fin 2) := [0, 1]
def case9_bit_2Outputs : List (Fin 2) := [1]
theorem case9_bit_2_accepted :
    admitStatement case9_bit_2Descriptors case9_bit_2Claims
      case9_bit_2Inputs case9_bit_2Outputs = some [0, 304, 305, 304, 305, 0, 0, 0] := by decide
theorem case9_bit_2_consistent_change :
    admitStatement case9_bit_2Descriptors [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [304, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = some [1, 304, 305, 304, 305, 0, 0, 0] := by decide
theorem case9_bit_2_path_rejected :
    admitStatement case9_bit_2Descriptors [⟨[.root "wrong_root", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [304, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = none := by decide
theorem case9_bit_2_width_rejected :
    admitStatement case9_bit_2Descriptors [⟨[.root "req", .field "flag"], [0, 1]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [304, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = none := by decide
theorem case9_bit_2_range_rejected :
    admitStatement case9_bit_2Descriptors [⟨[.root "req", .field "flag"], [2]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [304, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = none := by decide
theorem case9_bit_2_missing_leaf_rejected :
    admitStatement case9_bit_2Descriptors [⟨[.root "req", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = none := by decide
theorem case9_bit_2_split_alias_rejected :
    admitStatement case9_bit_2Descriptors [⟨[.root "req", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [304, 305]⟩, ⟨[.root "result", .field "y"], [305, 305]⟩]
      case9_bit_2Inputs case9_bit_2Outputs = none := by decide

-- bit_3: 3 named public leaves, 2 distinct wires.
def case10_bit_3Descriptors : List (Descriptor 2) :=
  [⟨[.root "req", .field "flag"], .bit, 1, 0⟩, ⟨[.root "req", .field "x"], .m31, 3, 1⟩, ⟨[.root "result", .field "y"], .m31, 3, 1⟩]
def case10_bit_3Claims : List Claim :=
  [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [333, 334, 335]⟩]
def case10_bit_3Inputs : List (Fin 2) := [0, 1]
def case10_bit_3Outputs : List (Fin 2) := [1]
theorem case10_bit_3_accepted :
    admitStatement case10_bit_3Descriptors case10_bit_3Claims
      case10_bit_3Inputs case10_bit_3Outputs = some [1, 333, 334, 335, 333, 334, 335, 0] := by decide
theorem case10_bit_3_consistent_change :
    admitStatement case10_bit_3Descriptors [⟨[.root "req", .field "flag"], [0]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [333, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = some [0, 333, 334, 335, 333, 334, 335, 0] := by decide
theorem case10_bit_3_path_rejected :
    admitStatement case10_bit_3Descriptors [⟨[.root "wrong_root", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [333, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = none := by decide
theorem case10_bit_3_width_rejected :
    admitStatement case10_bit_3Descriptors [⟨[.root "req", .field "flag"], [1, 1]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [333, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = none := by decide
theorem case10_bit_3_range_rejected :
    admitStatement case10_bit_3Descriptors [⟨[.root "req", .field "flag"], [2]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [333, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = none := by decide
theorem case10_bit_3_missing_leaf_rejected :
    admitStatement case10_bit_3Descriptors [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = none := by decide
theorem case10_bit_3_split_alias_rejected :
    admitStatement case10_bit_3Descriptors [⟨[.root "req", .field "flag"], [1]⟩, ⟨[.root "req", .field "x"], [333, 334, 335]⟩, ⟨[.root "result", .field "y"], [334, 334, 335]⟩]
      case10_bit_3Inputs case10_bit_3Outputs = none := by decide

-- private_1: 4 named public leaves, 3 distinct wires.
def case11_private_1Descriptors : List (Descriptor 3) :=
  [⟨[.root "req", .field "left"], .m31, 1, 0⟩, ⟨[.root "req", .field "right"], .m31, 1, 1⟩, ⟨[.root "result", .field "out"], .m31, 1, 2⟩, ⟨[.root "result", .field "alias"], .m31, 1, 2⟩]
def case11_private_1Claims : List Claim :=
  [⟨[.root "req", .field "left"], [349]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [375]⟩]
def case11_private_1Inputs : List (Fin 3) := [0, 1]
def case11_private_1Outputs : List (Fin 3) := [2]
theorem case11_private_1_accepted :
    admitStatement case11_private_1Descriptors case11_private_1Claims
      case11_private_1Inputs case11_private_1Outputs = some [349, 362, 375, 0, 0, 0, 0, 0] := by decide
theorem case11_private_1_consistent_change :
    admitStatement case11_private_1Descriptors [⟨[.root "req", .field "left"], [350]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [375]⟩]
      case11_private_1Inputs case11_private_1Outputs = some [350, 362, 375, 0, 0, 0, 0, 0] := by decide
theorem case11_private_1_path_rejected :
    admitStatement case11_private_1Descriptors [⟨[.root "wrong_root", .field "left"], [349]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [375]⟩]
      case11_private_1Inputs case11_private_1Outputs = none := by decide
theorem case11_private_1_width_rejected :
    admitStatement case11_private_1Descriptors [⟨[.root "req", .field "left"], [349, 1]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [375]⟩]
      case11_private_1Inputs case11_private_1Outputs = none := by decide
theorem case11_private_1_range_rejected :
    admitStatement case11_private_1Descriptors [⟨[.root "req", .field "left"], [2147483647]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [375]⟩]
      case11_private_1Inputs case11_private_1Outputs = none := by decide
theorem case11_private_1_missing_leaf_rejected :
    admitStatement case11_private_1Descriptors [⟨[.root "req", .field "left"], [349]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩]
      case11_private_1Inputs case11_private_1Outputs = none := by decide
theorem case11_private_1_split_alias_rejected :
    admitStatement case11_private_1Descriptors [⟨[.root "req", .field "left"], [349]⟩, ⟨[.root "req", .field "right"], [362]⟩, ⟨[.root "result", .field "out"], [375]⟩, ⟨[.root "result", .field "alias"], [376]⟩]
      case11_private_1Inputs case11_private_1Outputs = none := by decide

-- private_2: 4 named public leaves, 3 distinct wires.
def case12_private_2Descriptors : List (Descriptor 3) :=
  [⟨[.root "req", .field "left"], .m31, 2, 0⟩, ⟨[.root "req", .field "right"], .m31, 2, 1⟩, ⟨[.root "result", .field "out"], .m31, 2, 2⟩, ⟨[.root "result", .field "alias"], .m31, 2, 2⟩]
def case12_private_2Claims : List Claim :=
  [⟨[.root "req", .field "left"], [378, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [404, 405]⟩]
def case12_private_2Inputs : List (Fin 3) := [0, 1]
def case12_private_2Outputs : List (Fin 3) := [2]
theorem case12_private_2_accepted :
    admitStatement case12_private_2Descriptors case12_private_2Claims
      case12_private_2Inputs case12_private_2Outputs = some [378, 379, 391, 392, 404, 405, 0, 0] := by decide
theorem case12_private_2_consistent_change :
    admitStatement case12_private_2Descriptors [⟨[.root "req", .field "left"], [379, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [404, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = some [379, 379, 391, 392, 404, 405, 0, 0] := by decide
theorem case12_private_2_path_rejected :
    admitStatement case12_private_2Descriptors [⟨[.root "wrong_root", .field "left"], [378, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [404, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = none := by decide
theorem case12_private_2_width_rejected :
    admitStatement case12_private_2Descriptors [⟨[.root "req", .field "left"], [378, 379, 1]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [404, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = none := by decide
theorem case12_private_2_range_rejected :
    admitStatement case12_private_2Descriptors [⟨[.root "req", .field "left"], [2147483647, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [404, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = none := by decide
theorem case12_private_2_missing_leaf_rejected :
    admitStatement case12_private_2Descriptors [⟨[.root "req", .field "left"], [378, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = none := by decide
theorem case12_private_2_split_alias_rejected :
    admitStatement case12_private_2Descriptors [⟨[.root "req", .field "left"], [378, 379]⟩, ⟨[.root "req", .field "right"], [391, 392]⟩, ⟨[.root "result", .field "out"], [404, 405]⟩, ⟨[.root "result", .field "alias"], [405, 405]⟩]
      case12_private_2Inputs case12_private_2Outputs = none := by decide

end S31.Functional.GeneratedRecordStatementCorpusV2
