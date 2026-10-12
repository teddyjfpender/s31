import S31.Gadgets.Functional.RecordLayoutValidationV2

/-! Generated from the 13-layout ABI source corpus. Default script mode checks
exact bytes; --write explicitly regenerates after review. These cases check
compiler-emitted type trees and leaves against the Lean raw layout walk.
They do not model general JSON parsing or native proof authentication. -/
-- Source corpus SHA-256: a5e2883c146957858828404f47afec1251a4c8b99929c0ed310bb56a04a2305c
namespace S31.Functional.GeneratedRecordLayoutCorpusV2
open RecordAbiV2 RecordLayoutValidationV2

-- pair_1, root x: 1 declaration-order leaves.
def case0_pair_1_root0 : RawLayout := (.leaf .m31 1)
theorem case0_pair_1_root0_checked : checkNativeRoot case0_pair_1_root0 = true := by decide
theorem case0_pair_1_root0_paths :
    ((orderedRootLeaves "x" (erase case0_pair_1_root0)
      (leafWidthAt case0_pair_1_root0)).map Prod.fst) = [[.root "x"]] := by decide
theorem case0_pair_1_root0_widths :
    ((orderedRootLeaves "x" (erase case0_pair_1_root0)
      (leafWidthAt case0_pair_1_root0)).map Prod.snd) = [1] := by decide

-- pair_1, root result: 2 declaration-order leaves.
def case0_pair_1_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("a") else ("b")) (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 1))))
theorem case0_pair_1_root1_checked : checkNativeRoot case0_pair_1_root1 = true := by decide
theorem case0_pair_1_root1_paths :
    ((orderedRootLeaves "result" (erase case0_pair_1_root1)
      (leafWidthAt case0_pair_1_root1)).map Prod.fst) = [[.root "result", .field "a"], [.root "result", .field "b"]] := by decide
theorem case0_pair_1_root1_widths :
    ((orderedRootLeaves "result" (erase case0_pair_1_root1)
      (leafWidthAt case0_pair_1_root1)).map Prod.snd) = [1, 1] := by decide

-- pair_2, root x: 1 declaration-order leaves.
def case1_pair_2_root0 : RawLayout := (.leaf .m31 2)
theorem case1_pair_2_root0_checked : checkNativeRoot case1_pair_2_root0 = true := by decide
theorem case1_pair_2_root0_paths :
    ((orderedRootLeaves "x" (erase case1_pair_2_root0)
      (leafWidthAt case1_pair_2_root0)).map Prod.fst) = [[.root "x"]] := by decide
theorem case1_pair_2_root0_widths :
    ((orderedRootLeaves "x" (erase case1_pair_2_root0)
      (leafWidthAt case1_pair_2_root0)).map Prod.snd) = [2] := by decide

-- pair_2, root result: 2 declaration-order leaves.
def case1_pair_2_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("a") else ("b")) (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 2))))
theorem case1_pair_2_root1_checked : checkNativeRoot case1_pair_2_root1 = true := by decide
theorem case1_pair_2_root1_paths :
    ((orderedRootLeaves "result" (erase case1_pair_2_root1)
      (leafWidthAt case1_pair_2_root1)).map Prod.fst) = [[.root "result", .field "a"], [.root "result", .field "b"]] := by decide
theorem case1_pair_2_root1_widths :
    ((orderedRootLeaves "result" (erase case1_pair_2_root1)
      (leafWidthAt case1_pair_2_root1)).map Prod.snd) = [2, 2] := by decide

-- pair_3, root x: 1 declaration-order leaves.
def case2_pair_3_root0 : RawLayout := (.leaf .m31 3)
theorem case2_pair_3_root0_checked : checkNativeRoot case2_pair_3_root0 = true := by decide
theorem case2_pair_3_root0_paths :
    ((orderedRootLeaves "x" (erase case2_pair_3_root0)
      (leafWidthAt case2_pair_3_root0)).map Prod.fst) = [[.root "x"]] := by decide
theorem case2_pair_3_root0_widths :
    ((orderedRootLeaves "x" (erase case2_pair_3_root0)
      (leafWidthAt case2_pair_3_root0)).map Prod.snd) = [3] := by decide

-- pair_3, root result: 2 declaration-order leaves.
def case2_pair_3_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("a") else ("b")) (fun index => if index.val = 0 then ((.leaf .m31 3)) else ((.leaf .m31 3))))
theorem case2_pair_3_root1_checked : checkNativeRoot case2_pair_3_root1 = true := by decide
theorem case2_pair_3_root1_paths :
    ((orderedRootLeaves "result" (erase case2_pair_3_root1)
      (leafWidthAt case2_pair_3_root1)).map Prod.fst) = [[.root "result", .field "a"], [.root "result", .field "b"]] := by decide
theorem case2_pair_3_root1_widths :
    ((orderedRootLeaves "result" (erase case2_pair_3_root1)
      (leafWidthAt case2_pair_3_root1)).map Prod.snd) = [3, 3] := by decide

-- pair_4, root x: 1 declaration-order leaves.
def case3_pair_4_root0 : RawLayout := (.leaf .m31 4)
theorem case3_pair_4_root0_checked : checkNativeRoot case3_pair_4_root0 = true := by decide
theorem case3_pair_4_root0_paths :
    ((orderedRootLeaves "x" (erase case3_pair_4_root0)
      (leafWidthAt case3_pair_4_root0)).map Prod.fst) = [[.root "x"]] := by decide
theorem case3_pair_4_root0_widths :
    ((orderedRootLeaves "x" (erase case3_pair_4_root0)
      (leafWidthAt case3_pair_4_root0)).map Prod.snd) = [4] := by decide

-- pair_4, root result: 2 declaration-order leaves.
def case3_pair_4_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("a") else ("b")) (fun index => if index.val = 0 then ((.leaf .m31 4)) else ((.leaf .m31 4))))
theorem case3_pair_4_root1_checked : checkNativeRoot case3_pair_4_root1 = true := by decide
theorem case3_pair_4_root1_paths :
    ((orderedRootLeaves "result" (erase case3_pair_4_root1)
      (leafWidthAt case3_pair_4_root1)).map Prod.fst) = [[.root "result", .field "a"], [.root "result", .field "b"]] := by decide
theorem case3_pair_4_root1_widths :
    ((orderedRootLeaves "result" (erase case3_pair_4_root1)
      (leafWidthAt case3_pair_4_root1)).map Prod.snd) = [4, 4] := by decide

-- tuple_1_1, root req: 2 declaration-order leaves.
def case4_tuple_1_1_root0 : RawLayout := (.record 1 (fun _ => ("pair")) (fun _ => ((.tuple 2 (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 1)))))))
theorem case4_tuple_1_1_root0_checked : checkNativeRoot case4_tuple_1_1_root0 = true := by decide
theorem case4_tuple_1_1_root0_paths :
    ((orderedRootLeaves "req" (erase case4_tuple_1_1_root0)
      (leafWidthAt case4_tuple_1_1_root0)).map Prod.fst) = [[.root "req", .field "pair", .tuple 0], [.root "req", .field "pair", .tuple 1]] := by decide
theorem case4_tuple_1_1_root0_widths :
    ((orderedRootLeaves "req" (erase case4_tuple_1_1_root0)
      (leafWidthAt case4_tuple_1_1_root0)).map Prod.snd) = [1, 1] := by decide

-- tuple_1_1, root result: 2 declaration-order leaves.
def case4_tuple_1_1_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("copy") else ("tail")) (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 1))))
theorem case4_tuple_1_1_root1_checked : checkNativeRoot case4_tuple_1_1_root1 = true := by decide
theorem case4_tuple_1_1_root1_paths :
    ((orderedRootLeaves "result" (erase case4_tuple_1_1_root1)
      (leafWidthAt case4_tuple_1_1_root1)).map Prod.fst) = [[.root "result", .field "copy"], [.root "result", .field "tail"]] := by decide
theorem case4_tuple_1_1_root1_widths :
    ((orderedRootLeaves "result" (erase case4_tuple_1_1_root1)
      (leafWidthAt case4_tuple_1_1_root1)).map Prod.snd) = [1, 1] := by decide

-- tuple_2_1, root req: 2 declaration-order leaves.
def case5_tuple_2_1_root0 : RawLayout := (.record 1 (fun _ => ("pair")) (fun _ => ((.tuple 2 (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 1)))))))
theorem case5_tuple_2_1_root0_checked : checkNativeRoot case5_tuple_2_1_root0 = true := by decide
theorem case5_tuple_2_1_root0_paths :
    ((orderedRootLeaves "req" (erase case5_tuple_2_1_root0)
      (leafWidthAt case5_tuple_2_1_root0)).map Prod.fst) = [[.root "req", .field "pair", .tuple 0], [.root "req", .field "pair", .tuple 1]] := by decide
theorem case5_tuple_2_1_root0_widths :
    ((orderedRootLeaves "req" (erase case5_tuple_2_1_root0)
      (leafWidthAt case5_tuple_2_1_root0)).map Prod.snd) = [2, 1] := by decide

-- tuple_2_1, root result: 2 declaration-order leaves.
def case5_tuple_2_1_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("copy") else ("tail")) (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 1))))
theorem case5_tuple_2_1_root1_checked : checkNativeRoot case5_tuple_2_1_root1 = true := by decide
theorem case5_tuple_2_1_root1_paths :
    ((orderedRootLeaves "result" (erase case5_tuple_2_1_root1)
      (leafWidthAt case5_tuple_2_1_root1)).map Prod.fst) = [[.root "result", .field "copy"], [.root "result", .field "tail"]] := by decide
theorem case5_tuple_2_1_root1_widths :
    ((orderedRootLeaves "result" (erase case5_tuple_2_1_root1)
      (leafWidthAt case5_tuple_2_1_root1)).map Prod.snd) = [2, 1] := by decide

-- tuple_1_2, root req: 2 declaration-order leaves.
def case6_tuple_1_2_root0 : RawLayout := (.record 1 (fun _ => ("pair")) (fun _ => ((.tuple 2 (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 2)))))))
theorem case6_tuple_1_2_root0_checked : checkNativeRoot case6_tuple_1_2_root0 = true := by decide
theorem case6_tuple_1_2_root0_paths :
    ((orderedRootLeaves "req" (erase case6_tuple_1_2_root0)
      (leafWidthAt case6_tuple_1_2_root0)).map Prod.fst) = [[.root "req", .field "pair", .tuple 0], [.root "req", .field "pair", .tuple 1]] := by decide
theorem case6_tuple_1_2_root0_widths :
    ((orderedRootLeaves "req" (erase case6_tuple_1_2_root0)
      (leafWidthAt case6_tuple_1_2_root0)).map Prod.snd) = [1, 2] := by decide

-- tuple_1_2, root result: 2 declaration-order leaves.
def case6_tuple_1_2_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("copy") else ("tail")) (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 2))))
theorem case6_tuple_1_2_root1_checked : checkNativeRoot case6_tuple_1_2_root1 = true := by decide
theorem case6_tuple_1_2_root1_paths :
    ((orderedRootLeaves "result" (erase case6_tuple_1_2_root1)
      (leafWidthAt case6_tuple_1_2_root1)).map Prod.fst) = [[.root "result", .field "copy"], [.root "result", .field "tail"]] := by decide
theorem case6_tuple_1_2_root1_widths :
    ((orderedRootLeaves "result" (erase case6_tuple_1_2_root1)
      (leafWidthAt case6_tuple_1_2_root1)).map Prod.snd) = [1, 2] := by decide

-- tuple_2_2, root req: 2 declaration-order leaves.
def case7_tuple_2_2_root0 : RawLayout := (.record 1 (fun _ => ("pair")) (fun _ => ((.tuple 2 (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 2)))))))
theorem case7_tuple_2_2_root0_checked : checkNativeRoot case7_tuple_2_2_root0 = true := by decide
theorem case7_tuple_2_2_root0_paths :
    ((orderedRootLeaves "req" (erase case7_tuple_2_2_root0)
      (leafWidthAt case7_tuple_2_2_root0)).map Prod.fst) = [[.root "req", .field "pair", .tuple 0], [.root "req", .field "pair", .tuple 1]] := by decide
theorem case7_tuple_2_2_root0_widths :
    ((orderedRootLeaves "req" (erase case7_tuple_2_2_root0)
      (leafWidthAt case7_tuple_2_2_root0)).map Prod.snd) = [2, 2] := by decide

-- tuple_2_2, root result: 2 declaration-order leaves.
def case7_tuple_2_2_root1 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("copy") else ("tail")) (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 2))))
theorem case7_tuple_2_2_root1_checked : checkNativeRoot case7_tuple_2_2_root1 = true := by decide
theorem case7_tuple_2_2_root1_paths :
    ((orderedRootLeaves "result" (erase case7_tuple_2_2_root1)
      (leafWidthAt case7_tuple_2_2_root1)).map Prod.fst) = [[.root "result", .field "copy"], [.root "result", .field "tail"]] := by decide
theorem case7_tuple_2_2_root1_widths :
    ((orderedRootLeaves "result" (erase case7_tuple_2_2_root1)
      (leafWidthAt case7_tuple_2_2_root1)).map Prod.snd) = [2, 2] := by decide

-- bit_1, root req: 2 declaration-order leaves.
def case8_bit_1_root0 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("flag") else ("x")) (fun index => if index.val = 0 then ((.leaf .bit 1)) else ((.leaf .m31 1))))
theorem case8_bit_1_root0_checked : checkNativeRoot case8_bit_1_root0 = true := by decide
theorem case8_bit_1_root0_paths :
    ((orderedRootLeaves "req" (erase case8_bit_1_root0)
      (leafWidthAt case8_bit_1_root0)).map Prod.fst) = [[.root "req", .field "flag"], [.root "req", .field "x"]] := by decide
theorem case8_bit_1_root0_widths :
    ((orderedRootLeaves "req" (erase case8_bit_1_root0)
      (leafWidthAt case8_bit_1_root0)).map Prod.snd) = [1, 1] := by decide

-- bit_1, root result: 1 declaration-order leaves.
def case8_bit_1_root1 : RawLayout := (.record 1 (fun _ => ("y")) (fun _ => ((.leaf .m31 1))))
theorem case8_bit_1_root1_checked : checkNativeRoot case8_bit_1_root1 = true := by decide
theorem case8_bit_1_root1_paths :
    ((orderedRootLeaves "result" (erase case8_bit_1_root1)
      (leafWidthAt case8_bit_1_root1)).map Prod.fst) = [[.root "result", .field "y"]] := by decide
theorem case8_bit_1_root1_widths :
    ((orderedRootLeaves "result" (erase case8_bit_1_root1)
      (leafWidthAt case8_bit_1_root1)).map Prod.snd) = [1] := by decide

-- bit_2, root req: 2 declaration-order leaves.
def case9_bit_2_root0 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("flag") else ("x")) (fun index => if index.val = 0 then ((.leaf .bit 1)) else ((.leaf .m31 2))))
theorem case9_bit_2_root0_checked : checkNativeRoot case9_bit_2_root0 = true := by decide
theorem case9_bit_2_root0_paths :
    ((orderedRootLeaves "req" (erase case9_bit_2_root0)
      (leafWidthAt case9_bit_2_root0)).map Prod.fst) = [[.root "req", .field "flag"], [.root "req", .field "x"]] := by decide
theorem case9_bit_2_root0_widths :
    ((orderedRootLeaves "req" (erase case9_bit_2_root0)
      (leafWidthAt case9_bit_2_root0)).map Prod.snd) = [1, 2] := by decide

-- bit_2, root result: 1 declaration-order leaves.
def case9_bit_2_root1 : RawLayout := (.record 1 (fun _ => ("y")) (fun _ => ((.leaf .m31 2))))
theorem case9_bit_2_root1_checked : checkNativeRoot case9_bit_2_root1 = true := by decide
theorem case9_bit_2_root1_paths :
    ((orderedRootLeaves "result" (erase case9_bit_2_root1)
      (leafWidthAt case9_bit_2_root1)).map Prod.fst) = [[.root "result", .field "y"]] := by decide
theorem case9_bit_2_root1_widths :
    ((orderedRootLeaves "result" (erase case9_bit_2_root1)
      (leafWidthAt case9_bit_2_root1)).map Prod.snd) = [2] := by decide

-- bit_3, root req: 2 declaration-order leaves.
def case10_bit_3_root0 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("flag") else ("x")) (fun index => if index.val = 0 then ((.leaf .bit 1)) else ((.leaf .m31 3))))
theorem case10_bit_3_root0_checked : checkNativeRoot case10_bit_3_root0 = true := by decide
theorem case10_bit_3_root0_paths :
    ((orderedRootLeaves "req" (erase case10_bit_3_root0)
      (leafWidthAt case10_bit_3_root0)).map Prod.fst) = [[.root "req", .field "flag"], [.root "req", .field "x"]] := by decide
theorem case10_bit_3_root0_widths :
    ((orderedRootLeaves "req" (erase case10_bit_3_root0)
      (leafWidthAt case10_bit_3_root0)).map Prod.snd) = [1, 3] := by decide

-- bit_3, root result: 1 declaration-order leaves.
def case10_bit_3_root1 : RawLayout := (.record 1 (fun _ => ("y")) (fun _ => ((.leaf .m31 3))))
theorem case10_bit_3_root1_checked : checkNativeRoot case10_bit_3_root1 = true := by decide
theorem case10_bit_3_root1_paths :
    ((orderedRootLeaves "result" (erase case10_bit_3_root1)
      (leafWidthAt case10_bit_3_root1)).map Prod.fst) = [[.root "result", .field "y"]] := by decide
theorem case10_bit_3_root1_widths :
    ((orderedRootLeaves "result" (erase case10_bit_3_root1)
      (leafWidthAt case10_bit_3_root1)).map Prod.snd) = [3] := by decide

-- private_1, root req: 2 declaration-order leaves.
def case11_private_1_root0 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("left") else ("right")) (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 1))))
theorem case11_private_1_root0_checked : checkNativeRoot case11_private_1_root0 = true := by decide
theorem case11_private_1_root0_paths :
    ((orderedRootLeaves "req" (erase case11_private_1_root0)
      (leafWidthAt case11_private_1_root0)).map Prod.fst) = [[.root "req", .field "left"], [.root "req", .field "right"]] := by decide
theorem case11_private_1_root0_widths :
    ((orderedRootLeaves "req" (erase case11_private_1_root0)
      (leafWidthAt case11_private_1_root0)).map Prod.snd) = [1, 1] := by decide

-- private_1, root hidden: 1 declaration-order leaves.
def case11_private_1_root1 : RawLayout := (.record 1 (fun _ => ("mask")) (fun _ => ((.leaf .m31 1))))
theorem case11_private_1_root1_checked : checkNativeRoot case11_private_1_root1 = true := by decide
theorem case11_private_1_root1_paths :
    ((orderedRootLeaves "hidden" (erase case11_private_1_root1)
      (leafWidthAt case11_private_1_root1)).map Prod.fst) = [[.root "hidden", .field "mask"]] := by decide
theorem case11_private_1_root1_widths :
    ((orderedRootLeaves "hidden" (erase case11_private_1_root1)
      (leafWidthAt case11_private_1_root1)).map Prod.snd) = [1] := by decide

-- private_1, root result: 2 declaration-order leaves.
def case11_private_1_root2 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("out") else ("alias")) (fun index => if index.val = 0 then ((.leaf .m31 1)) else ((.leaf .m31 1))))
theorem case11_private_1_root2_checked : checkNativeRoot case11_private_1_root2 = true := by decide
theorem case11_private_1_root2_paths :
    ((orderedRootLeaves "result" (erase case11_private_1_root2)
      (leafWidthAt case11_private_1_root2)).map Prod.fst) = [[.root "result", .field "out"], [.root "result", .field "alias"]] := by decide
theorem case11_private_1_root2_widths :
    ((orderedRootLeaves "result" (erase case11_private_1_root2)
      (leafWidthAt case11_private_1_root2)).map Prod.snd) = [1, 1] := by decide

-- private_2, root req: 2 declaration-order leaves.
def case12_private_2_root0 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("left") else ("right")) (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 2))))
theorem case12_private_2_root0_checked : checkNativeRoot case12_private_2_root0 = true := by decide
theorem case12_private_2_root0_paths :
    ((orderedRootLeaves "req" (erase case12_private_2_root0)
      (leafWidthAt case12_private_2_root0)).map Prod.fst) = [[.root "req", .field "left"], [.root "req", .field "right"]] := by decide
theorem case12_private_2_root0_widths :
    ((orderedRootLeaves "req" (erase case12_private_2_root0)
      (leafWidthAt case12_private_2_root0)).map Prod.snd) = [2, 2] := by decide

-- private_2, root hidden: 1 declaration-order leaves.
def case12_private_2_root1 : RawLayout := (.record 1 (fun _ => ("mask")) (fun _ => ((.leaf .m31 2))))
theorem case12_private_2_root1_checked : checkNativeRoot case12_private_2_root1 = true := by decide
theorem case12_private_2_root1_paths :
    ((orderedRootLeaves "hidden" (erase case12_private_2_root1)
      (leafWidthAt case12_private_2_root1)).map Prod.fst) = [[.root "hidden", .field "mask"]] := by decide
theorem case12_private_2_root1_widths :
    ((orderedRootLeaves "hidden" (erase case12_private_2_root1)
      (leafWidthAt case12_private_2_root1)).map Prod.snd) = [2] := by decide

-- private_2, root result: 2 declaration-order leaves.
def case12_private_2_root2 : RawLayout := (.record 2 (fun index => if index.val = 0 then ("out") else ("alias")) (fun index => if index.val = 0 then ((.leaf .m31 2)) else ((.leaf .m31 2))))
theorem case12_private_2_root2_checked : checkNativeRoot case12_private_2_root2 = true := by decide
theorem case12_private_2_root2_paths :
    ((orderedRootLeaves "result" (erase case12_private_2_root2)
      (leafWidthAt case12_private_2_root2)).map Prod.fst) = [[.root "result", .field "out"], [.root "result", .field "alias"]] := by decide
theorem case12_private_2_root2_widths :
    ((orderedRootLeaves "result" (erase case12_private_2_root2)
      (leafWidthAt case12_private_2_root2)).map Prod.snd) = [2, 2] := by decide

-- Adversarial raw trees exercise the executable validation premise.
def duplicateFields : RawLayout :=
  .record 2 (fun _ => "same") (fun _ => .leaf .m31 1)
theorem duplicateFields_rejected : checkRoot duplicateFields = false := by decide
def oversizedM31 : RawLayout := .leaf .m31 9
theorem oversizedM31_rejected : checkRoot oversizedM31 = false := by decide
def oversizedBit : RawLayout := .leaf .bit 2
theorem oversizedBit_rejected : checkRoot oversizedBit = false := by decide
def emptyTuple : RawLayout := .tuple 0 (fun _ => .leaf .m31 1)
theorem emptyTuple_rejected : checkRoot emptyTuple = false := by decide
def tupleRoot : RawLayout := .tuple 1 (fun _ => .leaf .m31 1)
theorem tupleRoot_rejected : checkNativeRoot tupleRoot = false := by decide
def emptyRecord : RawLayout :=
  .record 0 (fun _ => "unreachable") (fun _ => .leaf .m31 1)
theorem emptyRecord_rejected : checkRoot emptyRecord = false := by decide
def tooWideNode : RawLayout := .tuple 65 (fun _ => .leaf .m31 1)
theorem tooWideNode_rejected : checkRoot tooWideNode = false := by decide
def tooDeep : Nat → RawLayout
  | 0 => .leaf .m31 1
  | n + 1 => .tuple 1 (fun _ => tooDeep n)
theorem tooDeep_rejected : checkRoot (tooDeep 33) = false := by decide

end S31.Functional.GeneratedRecordLayoutCorpusV2
