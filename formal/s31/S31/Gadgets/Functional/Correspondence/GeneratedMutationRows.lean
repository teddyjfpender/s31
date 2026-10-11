import S31.Gadgets.Functional.SSAAliasTextBytes
import S31.Gadgets.Functional.SSAAirColumnCells

/-!
Kernel-reduced samples for the bounded direct-Gate source grammar.
The independent positional generator and this renderer pin 16 DAGs
with 1..16 arithmetic instructions, aliases, and earlier returns.
Full Python mutation corpus SHA-256: 332b31c1cf5c85dc91378b7d2dbc2c5b3724601bf09ce9140a387bc12a8685c8
Selected source-byte SHA-256: 3dbe1c1da5219db4f3f4e447a7ef5cad999a398263a45ae562c6096440f7b34f
Each certificate, row address/selector position, and use count is
an explicit datum checked by Lean's byte parser and row projection.
The `totalAddRows` values come from the independent Python schedule.
The native exporter equality, actual AIR fixed columns, proof
authentication, and verifier soundness remain external obligations.
-/

namespace S31.Functional.Correspondence.GeneratedMutationRows

open S31.Functional.SSACertificate
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

-- 00:direct: 1 producers; returned wire 1.
def case00Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 48, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 112, 49, 32,
    125
  ]
def case00MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 48, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 112, 49, 32, 125
  ]
def case00Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := true }],
    output := 1 }
def case00Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 503, multiply := true, in0 := 22, in1 := 22, out := 23 }
    ]
def case00Uses : List Nat := [2, 4]
theorem case00Checks :
    (parseAliasBytes case00Bytes).map (fun parsed => parsed.certificate) =
      some case00Certificate ∧
    expectedRows case00Certificate 475 = case00Rows ∧
    (List.range 2).map (sourceUses case00Certificate) =
      case00Uses ∧
    (parseAliasBytes case00MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case00Certificate := by decide

-- 01:aliases: 2 producers; returned wire 1.
def case01Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 112, 49, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117,
    114, 110, 101, 100, 32, 61, 32, 40, 40, 112, 49, 41, 41, 59, 32, 114,
    101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case01MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 112, 49, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117,
    114, 110, 101, 100, 32, 61, 32, 40, 40, 112, 50, 41, 41, 59, 32, 114,
    101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case01Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 1, rhs := 1, multiply := true }],
    output := 1 }
def case01Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 503, multiply := true, in0 := 23, in1 := 23, out := 24 }
    ]
def case01Uses : List Nat := [2, 6, 0]
theorem case01Checks :
    (parseAliasBytes case01Bytes).map (fun parsed => parsed.certificate) =
      some case01Certificate ∧
    expectedRows case01Certificate 475 = case01Rows ∧
    (List.range 3).map (sourceUses case01Certificate) =
      case01Uses ∧
    (parseAliasBytes case01MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case01Certificate := by decide

-- 02:direct: 3 producers; returned wire 3.
def case02Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 50, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101,
    116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 50, 59,
    32, 112, 51, 32, 125
  ]
def case02MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 50, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101,
    116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 50, 59,
    32, 112, 49, 32, 125
  ]
def case02Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 1, multiply := true },
      { id := 3, lhs := 1, rhs := 2, multiply := true }],
    output := 3 }
def case02Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 502, multiply := true, in0 := 22, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 503, multiply := true, in0 := 23, in1 := 24, out := 25 }
    ]
def case02Uses : List Nat := [3, 2, 1, 4]
theorem case02Checks :
    (parseAliasBytes case02Bytes).map (fun parsed => parsed.certificate) =
      some case02Certificate ∧
    expectedRows case02Certificate 474 = case02Rows ∧
    (List.range 4).map (sourceUses case02Certificate) =
      case02Uses ∧
    (parseAliasBytes case02MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case02Certificate := by decide

-- 03:aliases: 4 producers; returned wire 2.
def case03Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 51, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 120,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 52,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32, 112, 50,
    59, 32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61,
    32, 40, 40, 112, 50, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101,
    100, 32, 125
  ]
def case03MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 51, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 120,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 52,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32, 112, 50,
    59, 32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61,
    32, 40, 40, 112, 49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101,
    100, 32, 125
  ]
def case03Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 0, multiply := true },
      { id := 3, lhs := 0, rhs := 2, multiply := false },
      { id := 4, lhs := 0, rhs := 2, multiply := true }],
    output := 2 }
def case03Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 502, multiply := true, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 4, multiply := false, in0 := 22, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 503, multiply := true, in0 := 22, in1 := 24, out := 26 }
    ]
def case03Uses : List Nat := [6, 0, 6, 0, 0]
theorem case03Checks :
    (parseAliasBytes case03Bytes).map (fun parsed => parsed.certificate) =
      some case03Certificate ∧
    expectedRows case03Certificate 474 = case03Rows ∧
    (List.range 5).map (sourceUses case03Certificate) =
      case03Uses ∧
    (parseAliasBytes case03MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case03Certificate := by decide

-- 04:direct: 5 producers; returned wire 5.
def case04Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 52, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 43, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 49, 32, 43, 32, 112,
    49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 52, 59, 32, 112, 53, 32, 125
  ]
def case04MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 52, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 43, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 49, 32, 43, 32, 112,
    49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 52, 59, 32, 112, 49, 32, 125
  ]
def case04Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 1, rhs := 1, multiply := true },
      { id := 3, lhs := 1, rhs := 2, multiply := false },
      { id := 4, lhs := 1, rhs := 1, multiply := false },
      { id := 5, lhs := 2, rhs := 4, multiply := false }],
    output := 5 }
def case04Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 503, multiply := true, in0 := 23, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 4, multiply := false, in0 := 23, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 5, multiply := false, in0 := 23, in1 := 23, out := 26 },
      { circuitRow := 10, traceRow := 6, multiply := false, in0 := 24, in1 := 26, out := 27 }
    ]
def case04Uses : List Nat := [2, 5, 2, 0, 1, 4]
theorem case04Checks :
    (parseAliasBytes case04Bytes).map (fun parsed => parsed.certificate) =
      some case04Certificate ∧
    expectedRows case04Certificate 475 = case04Rows ∧
    (List.range 6).map (sourceUses case04Certificate) =
      case04Uses ∧
    (parseAliasBytes case04MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case04Certificate := by decide

-- 05:aliases: 6 producers; returned wire 3.
def case05Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 53, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 112,
    49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97,
    115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112,
    52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 43, 32, 112, 49,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 52, 32, 46, 42,
    32, 112, 52, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 54,
    32, 61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 54, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 52, 59, 32,
    108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40,
    40, 112, 51, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32,
    125
  ]
def case05MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 53, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 112,
    49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97,
    115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112,
    52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 43, 32, 112, 49,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 52, 32, 46, 42,
    32, 112, 52, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 54,
    32, 61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 54, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 52, 59, 32,
    108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40,
    40, 112, 49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32,
    125
  ]
def case05Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 0, multiply := true },
      { id := 3, lhs := 1, rhs := 2, multiply := false },
      { id := 4, lhs := 0, rhs := 1, multiply := false },
      { id := 5, lhs := 4, rhs := 4, multiply := true },
      { id := 6, lhs := 2, rhs := 4, multiply := false }],
    output := 3 }
def case05Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 502, multiply := true, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 4, multiply := false, in0 := 23, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 5, multiply := false, in0 := 22, in1 := 23, out := 26 },
      { circuitRow := 10, traceRow := 503, multiply := true, in0 := 26, in1 := 26, out := 27 },
      { circuitRow := 11, traceRow := 6, multiply := false, in0 := 24, in1 := 26, out := 28 }
    ]
def case05Uses : List Nat := [5, 2, 2, 4, 3, 0, 0]
theorem case05Checks :
    (parseAliasBytes case05Bytes).map (fun parsed => parsed.certificate) =
      some case05Certificate ∧
    expectedRows case05Certificate 474 = case05Rows ∧
    (List.range 7).map (sourceUses case05Certificate) =
      case05Uses ∧
    (parseAliasBytes case05MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case05Certificate := by decide

-- 06:direct: 7 producers; returned wire 7.
def case06Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 54, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 43, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43, 32,
    112, 52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 52, 32,
    43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112,
    51, 32, 46, 42, 32, 112, 51, 59, 32, 112, 55, 32, 125
  ]
def case06MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 54, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 43, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43, 32,
    112, 52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 52, 32,
    43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112,
    51, 32, 46, 42, 32, 112, 51, 59, 32, 112, 49, 32, 125
  ]
def case06Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 1, rhs := 1, multiply := true },
      { id := 3, lhs := 0, rhs := 2, multiply := true },
      { id := 4, lhs := 0, rhs := 3, multiply := false },
      { id := 5, lhs := 2, rhs := 4, multiply := false },
      { id := 6, lhs := 4, rhs := 4, multiply := false },
      { id := 7, lhs := 3, rhs := 3, multiply := true }],
    output := 7 }
def case06Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 501, multiply := true, in0 := 23, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 502, multiply := true, in0 := 22, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 4, multiply := false, in0 := 22, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 5, multiply := false, in0 := 24, in1 := 26, out := 27 },
      { circuitRow := 11, traceRow := 6, multiply := false, in0 := 26, in1 := 26, out := 28 },
      { circuitRow := 12, traceRow := 503, multiply := true, in0 := 25, in1 := 25, out := 29 }
    ]
def case06Uses : List Nat := [4, 2, 2, 3, 3, 0, 0, 4]
theorem case06Checks :
    (parseAliasBytes case06Bytes).map (fun parsed => parsed.certificate) =
      some case06Certificate ∧
    expectedRows case06Certificate 473 = case06Rows ∧
    (List.range 8).map (sourceUses case06Certificate) =
      case06Uses ∧
    (parseAliasBytes case06MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case06Certificate := by decide

-- 07:aliases: 8 producers; returned wire 4.
def case07Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 55, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 112,
    50, 32, 46, 42, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116,
    32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 43, 32,
    112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 120, 32, 43,
    32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 54,
    32, 61, 32, 40, 112, 52, 41, 59, 32, 108, 101, 116, 32, 112, 54, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 53, 59, 32,
    108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51, 32, 46, 42, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32, 61,
    32, 40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 46, 42, 32, 112, 52, 59, 32, 108,
    101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40, 40,
    112, 52, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case07MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 55, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32, 108,
    101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50, 32,
    43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32, 112,
    50, 32, 46, 42, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116,
    32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 43, 32,
    112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 120, 32, 43,
    32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 54,
    32, 61, 32, 40, 112, 52, 41, 59, 32, 108, 101, 116, 32, 112, 54, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 53, 59, 32,
    108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51, 32, 46, 42, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32, 61,
    32, 40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 46, 42, 32, 112, 52, 59, 32, 108,
    101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40, 40,
    112, 49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case07Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 1, multiply := false },
      { id := 3, lhs := 2, rhs := 2, multiply := true },
      { id := 4, lhs := 3, rhs := 3, multiply := false },
      { id := 5, lhs := 0, rhs := 3, multiply := false },
      { id := 6, lhs := 4, rhs := 5, multiply := false },
      { id := 7, lhs := 3, rhs := 3, multiply := true },
      { id := 8, lhs := 1, rhs := 4, multiply := true }],
    output := 4 }
def case07Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 4, multiply := false, in0 := 22, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 501, multiply := true, in0 := 24, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 5, multiply := false, in0 := 25, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 6, multiply := false, in0 := 22, in1 := 25, out := 27 },
      { circuitRow := 11, traceRow := 7, multiply := false, in0 := 26, in1 := 27, out := 28 },
      { circuitRow := 12, traceRow := 502, multiply := true, in0 := 25, in1 := 25, out := 29 },
      { circuitRow := 13, traceRow := 503, multiply := true, in0 := 23, in1 := 26, out := 30 }
    ]
def case07Uses : List Nat := [4, 2, 2, 5, 6, 1, 0, 0, 0]
theorem case07Checks :
    (parseAliasBytes case07Bytes).map (fun parsed => parsed.certificate) =
      some case07Certificate ∧
    expectedRows case07Certificate 473 = case07Rows ∧
    (List.range 9).map (sourceUses case07Certificate) =
      case07Uses ∧
    (parseAliasBytes case07MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case07Certificate := by decide

-- 08:direct: 9 producers; returned wire 9.
def case08Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 56, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59, 32, 108,
    101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 46, 42, 32, 112, 51, 59,
    32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 52, 32, 43, 32, 112,
    52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 53, 32, 46,
    42, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112,
    51, 32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61,
    32, 120, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 57, 32,
    61, 32, 112, 53, 32, 43, 32, 112, 56, 59, 32, 112, 57, 32, 125
  ]
def case08MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 56, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32,
    112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59, 32, 108,
    101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 46, 42, 32, 112, 51, 59,
    32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 52, 32, 43, 32, 112,
    52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 53, 32, 46,
    42, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112,
    51, 32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61,
    32, 120, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 57, 32,
    61, 32, 112, 53, 32, 43, 32, 112, 56, 59, 32, 112, 49, 32, 125
  ]
def case08Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 0, multiply := true },
      { id := 3, lhs := 0, rhs := 2, multiply := true },
      { id := 4, lhs := 0, rhs := 3, multiply := true },
      { id := 5, lhs := 4, rhs := 4, multiply := false },
      { id := 6, lhs := 5, rhs := 5, multiply := true },
      { id := 7, lhs := 3, rhs := 5, multiply := false },
      { id := 8, lhs := 0, rhs := 1, multiply := false },
      { id := 9, lhs := 5, rhs := 8, multiply := false }],
    output := 9 }
def case08Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 500, multiply := true, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 501, multiply := true, in0 := 22, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 502, multiply := true, in0 := 22, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 4, multiply := false, in0 := 26, in1 := 26, out := 27 },
      { circuitRow := 11, traceRow := 503, multiply := true, in0 := 27, in1 := 27, out := 28 },
      { circuitRow := 12, traceRow := 5, multiply := false, in0 := 25, in1 := 27, out := 29 },
      { circuitRow := 13, traceRow := 6, multiply := false, in0 := 22, in1 := 23, out := 30 },
      { circuitRow := 14, traceRow := 7, multiply := false, in0 := 27, in1 := 30, out := 31 }
    ]
def case08Uses : List Nat := [7, 1, 1, 2, 2, 4, 0, 0, 1, 4]
theorem case08Checks :
    (parseAliasBytes case08Bytes).map (fun parsed => parsed.certificate) =
      some case08Certificate ∧
    expectedRows case08Certificate 472 = case08Rows ∧
    (List.range 10).map (sourceUses case08Certificate) =
      case08Uses ∧
    (parseAliasBytes case08MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case08Certificate := by decide

-- 09:aliases: 10 producers; returned wire 5.
def case09Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 57, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61,
    32, 112, 49, 32, 46, 42, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97,
    108, 105, 97, 115, 95, 52, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108,
    101, 116, 32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32,
    43, 32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112,
    51, 32, 46, 42, 32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 54, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108, 101, 116,
    32, 112, 54, 32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42,
    32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51,
    32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 56, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 56, 32, 46, 42, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 57, 32, 61, 32, 112, 50, 32, 46, 42,
    32, 112, 56, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49,
    48, 32, 61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49,
    48, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112,
    57, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32,
    61, 32, 40, 40, 112, 53, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110,
    101, 100, 32, 125
  ]
def case09MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 57, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109, 51,
    49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105, 99,
    32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116, 32,
    112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61,
    32, 112, 49, 32, 46, 42, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97,
    108, 105, 97, 115, 95, 52, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108,
    101, 116, 32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32,
    43, 32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112,
    51, 32, 46, 42, 32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 54, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108, 101, 116,
    32, 112, 54, 32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42,
    32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51,
    32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 56, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 56, 32, 46, 42, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 57, 32, 61, 32, 112, 50, 32, 46, 42,
    32, 112, 56, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49,
    48, 32, 61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49,
    48, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112,
    57, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32,
    61, 32, 40, 40, 112, 49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110,
    101, 100, 32, 125
  ]
def case09Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := true },
      { id := 2, lhs := 0, rhs := 1, multiply := true },
      { id := 3, lhs := 1, rhs := 2, multiply := true },
      { id := 4, lhs := 1, rhs := 3, multiply := false },
      { id := 5, lhs := 3, rhs := 3, multiply := true },
      { id := 6, lhs := 1, rhs := 5, multiply := true },
      { id := 7, lhs := 3, rhs := 5, multiply := false },
      { id := 8, lhs := 0, rhs := 3, multiply := true },
      { id := 9, lhs := 2, rhs := 8, multiply := true },
      { id := 10, lhs := 2, rhs := 9, multiply := false }],
    output := 5 }
def case09Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 497, multiply := true, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 498, multiply := true, in0 := 22, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 499, multiply := true, in0 := 23, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 3, multiply := false, in0 := 23, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 500, multiply := true, in0 := 25, in1 := 25, out := 27 },
      { circuitRow := 11, traceRow := 501, multiply := true, in0 := 23, in1 := 27, out := 28 },
      { circuitRow := 12, traceRow := 4, multiply := false, in0 := 25, in1 := 27, out := 29 },
      { circuitRow := 13, traceRow := 502, multiply := true, in0 := 22, in1 := 25, out := 30 },
      { circuitRow := 14, traceRow := 503, multiply := true, in0 := 24, in1 := 30, out := 31 },
      { circuitRow := 15, traceRow := 5, multiply := false, in0 := 24, in1 := 31, out := 32 }
    ]
def case09Uses : List Nat := [4, 4, 3, 5, 0, 6, 0, 0, 1, 1, 0]
theorem case09Checks :
    (parseAliasBytes case09Bytes).map (fun parsed => parsed.certificate) =
      some case09Certificate ∧
    expectedRows case09Certificate 469 = case09Rows ∧
    (List.range 11).map (sourceUses case09Certificate) =
      case09Uses ∧
    (parseAliasBytes case09MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case09Certificate := by decide

-- 10:direct: 11 producers; returned wire 11.
def case10Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 48, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 51, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 50, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 120, 32,
    43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 120,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    112, 50, 32, 43, 32, 112, 55, 59, 32, 108, 101, 116, 32, 112, 57, 32,
    61, 32, 112, 51, 32, 43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112,
    49, 48, 32, 61, 32, 112, 51, 32, 43, 32, 112, 57, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 120, 32, 43, 32, 112, 57, 59, 32,
    112, 49, 49, 32, 125
  ]
def case10MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 48, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 112, 51, 32, 61, 32, 112, 49, 32, 46, 42, 32, 112, 49, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 51, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 50, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 120, 32,
    43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 120,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    112, 50, 32, 43, 32, 112, 55, 59, 32, 108, 101, 116, 32, 112, 57, 32,
    61, 32, 112, 51, 32, 43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112,
    49, 48, 32, 61, 32, 112, 51, 32, 43, 32, 112, 57, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 120, 32, 43, 32, 112, 57, 59, 32,
    112, 49, 32, 125
  ]
def case10Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 0, multiply := true },
      { id := 3, lhs := 1, rhs := 1, multiply := true },
      { id := 4, lhs := 3, rhs := 3, multiply := false },
      { id := 5, lhs := 2, rhs := 2, multiply := false },
      { id := 6, lhs := 0, rhs := 5, multiply := false },
      { id := 7, lhs := 0, rhs := 2, multiply := false },
      { id := 8, lhs := 2, rhs := 7, multiply := false },
      { id := 9, lhs := 3, rhs := 4, multiply := false },
      { id := 10, lhs := 3, rhs := 9, multiply := false },
      { id := 11, lhs := 0, rhs := 9, multiply := false }],
    output := 11 }
def case10Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 502, multiply := true, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 503, multiply := true, in0 := 23, in1 := 23, out := 25 },
      { circuitRow := 9, traceRow := 4, multiply := false, in0 := 25, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 5, multiply := false, in0 := 24, in1 := 24, out := 27 },
      { circuitRow := 11, traceRow := 6, multiply := false, in0 := 22, in1 := 27, out := 28 },
      { circuitRow := 12, traceRow := 7, multiply := false, in0 := 22, in1 := 24, out := 29 },
      { circuitRow := 13, traceRow := 8, multiply := false, in0 := 24, in1 := 29, out := 30 },
      { circuitRow := 14, traceRow := 9, multiply := false, in0 := 25, in1 := 26, out := 31 },
      { circuitRow := 15, traceRow := 10, multiply := false, in0 := 25, in1 := 31, out := 32 },
      { circuitRow := 16, traceRow := 11, multiply := false, in0 := 22, in1 := 31, out := 33 }
    ]
def case10Uses : List Nat := [7, 2, 4, 4, 1, 1, 0, 1, 0, 2, 0, 4]
theorem case10Checks :
    (parseAliasBytes case10Bytes).map (fun parsed => parsed.certificate) =
      some case10Certificate ∧
    expectedRows case10Certificate 474 = case10Rows ∧
    (List.range 12).map (sourceUses case10Certificate) =
      case10Uses ∧
    (parseAliasBytes case10MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case10Certificate := by decide

-- 11:aliases: 12 producers; returned wire 6.
def case11Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 49, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32,
    120, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32,
    112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32,
    112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 51, 32,
    43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    54, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42, 32, 112, 53,
    59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 120, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32, 61,
    32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116,
    32, 112, 57, 32, 61, 32, 112, 56, 32, 46, 42, 32, 112, 56, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32, 40,
    112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 53, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 120, 32, 43, 32, 112, 52, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 61, 32, 40,
    112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 57, 59, 32, 108, 101,
    116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40, 40, 112,
    54, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case11MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 49, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59, 32,
    108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95, 50,
    32, 46, 42, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32,
    120, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32,
    112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32,
    112, 51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 51, 32,
    43, 32, 112, 52, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    54, 32, 61, 32, 40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42, 32, 112, 53,
    59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 120, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32, 61,
    32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116,
    32, 112, 57, 32, 61, 32, 112, 56, 32, 46, 42, 32, 112, 56, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32, 40,
    112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 53, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 120, 32, 43, 32, 112, 52, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 61, 32, 40,
    112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 57, 59, 32, 108, 101,
    116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32, 40, 40, 112,
    49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case11Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 0, multiply := true },
      { id := 3, lhs := 0, rhs := 1, multiply := true },
      { id := 4, lhs := 0, rhs := 3, multiply := true },
      { id := 5, lhs := 3, rhs := 4, multiply := false },
      { id := 6, lhs := 1, rhs := 5, multiply := true },
      { id := 7, lhs := 0, rhs := 3, multiply := false },
      { id := 8, lhs := 0, rhs := 1, multiply := false },
      { id := 9, lhs := 8, rhs := 8, multiply := true },
      { id := 10, lhs := 3, rhs := 5, multiply := false },
      { id := 11, lhs := 0, rhs := 4, multiply := false },
      { id := 12, lhs := 3, rhs := 9, multiply := false }],
    output := 6 }
def case11Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 499, multiply := true, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 500, multiply := true, in0 := 22, in1 := 23, out := 25 },
      { circuitRow := 9, traceRow := 501, multiply := true, in0 := 22, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 4, multiply := false, in0 := 25, in1 := 26, out := 27 },
      { circuitRow := 11, traceRow := 502, multiply := true, in0 := 23, in1 := 27, out := 28 },
      { circuitRow := 12, traceRow := 5, multiply := false, in0 := 22, in1 := 25, out := 29 },
      { circuitRow := 13, traceRow := 6, multiply := false, in0 := 22, in1 := 23, out := 30 },
      { circuitRow := 14, traceRow := 503, multiply := true, in0 := 30, in1 := 30, out := 31 },
      { circuitRow := 15, traceRow := 7, multiply := false, in0 := 25, in1 := 27, out := 32 },
      { circuitRow := 16, traceRow := 8, multiply := false, in0 := 22, in1 := 26, out := 33 },
      { circuitRow := 17, traceRow := 9, multiply := false, in0 := 25, in1 := 31, out := 34 }
    ]
def case11Uses : List Nat := [9, 3, 0, 5, 2, 2, 4, 0, 2, 1, 0, 0, 0]
theorem case11Checks :
    (parseAliasBytes case11Bytes).map (fun parsed => parsed.certificate) =
      some case11Certificate ∧
    expectedRows case11Certificate 471 = case11Rows ∧
    (List.range 13).map (sourceUses case11Certificate) =
      case11Uses ∧
    (parseAliasBytes case11MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case11Certificate := by decide

-- 12:direct: 13 producers; returned wire 13.
def case12Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 50, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 43, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 51, 32, 46, 42,
    32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 49,
    32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32,
    112, 50, 32, 43, 32, 112, 54, 59, 32, 108, 101, 116, 32, 112, 56, 32,
    61, 32, 112, 51, 32, 43, 32, 112, 55, 59, 32, 108, 101, 116, 32, 112,
    57, 32, 61, 32, 112, 55, 32, 43, 32, 112, 56, 59, 32, 108, 101, 116,
    32, 112, 49, 48, 32, 61, 32, 112, 54, 32, 46, 42, 32, 112, 55, 59,
    32, 108, 101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 50, 32, 46, 42,
    32, 112, 56, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32, 112,
    49, 32, 46, 42, 32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 49, 51,
    32, 61, 32, 120, 32, 43, 32, 112, 49, 48, 59, 32, 112, 49, 51, 32,
    125
  ]
def case12MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 50, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 112, 50, 32, 61, 32, 120, 32, 46, 42, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 120, 32, 43, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 51, 32, 46, 42,
    32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112, 49,
    32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32,
    112, 50, 32, 43, 32, 112, 54, 59, 32, 108, 101, 116, 32, 112, 56, 32,
    61, 32, 112, 51, 32, 43, 32, 112, 55, 59, 32, 108, 101, 116, 32, 112,
    57, 32, 61, 32, 112, 55, 32, 43, 32, 112, 56, 59, 32, 108, 101, 116,
    32, 112, 49, 48, 32, 61, 32, 112, 54, 32, 46, 42, 32, 112, 55, 59,
    32, 108, 101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 50, 32, 46, 42,
    32, 112, 56, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32, 112,
    49, 32, 46, 42, 32, 112, 51, 59, 32, 108, 101, 116, 32, 112, 49, 51,
    32, 61, 32, 120, 32, 43, 32, 112, 49, 48, 59, 32, 112, 49, 32, 125
  ]
def case12Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 0, rhs := 1, multiply := true },
      { id := 3, lhs := 0, rhs := 2, multiply := true },
      { id := 4, lhs := 0, rhs := 3, multiply := false },
      { id := 5, lhs := 3, rhs := 3, multiply := true },
      { id := 6, lhs := 1, rhs := 1, multiply := false },
      { id := 7, lhs := 2, rhs := 6, multiply := false },
      { id := 8, lhs := 3, rhs := 7, multiply := false },
      { id := 9, lhs := 7, rhs := 8, multiply := false },
      { id := 10, lhs := 6, rhs := 7, multiply := true },
      { id := 11, lhs := 2, rhs := 8, multiply := true },
      { id := 12, lhs := 1, rhs := 3, multiply := true },
      { id := 13, lhs := 0, rhs := 10, multiply := false }],
    output := 13 }
def case12Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 498, multiply := true, in0 := 22, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 499, multiply := true, in0 := 22, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 4, multiply := false, in0 := 22, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 500, multiply := true, in0 := 25, in1 := 25, out := 27 },
      { circuitRow := 11, traceRow := 5, multiply := false, in0 := 23, in1 := 23, out := 28 },
      { circuitRow := 12, traceRow := 6, multiply := false, in0 := 24, in1 := 28, out := 29 },
      { circuitRow := 13, traceRow := 7, multiply := false, in0 := 25, in1 := 29, out := 30 },
      { circuitRow := 14, traceRow := 8, multiply := false, in0 := 29, in1 := 30, out := 31 },
      { circuitRow := 15, traceRow := 501, multiply := true, in0 := 28, in1 := 29, out := 32 },
      { circuitRow := 16, traceRow := 502, multiply := true, in0 := 24, in1 := 30, out := 33 },
      { circuitRow := 17, traceRow := 503, multiply := true, in0 := 23, in1 := 25, out := 34 },
      { circuitRow := 18, traceRow := 9, multiply := false, in0 := 22, in1 := 32, out := 35 }
    ]
def case12Uses : List Nat := [6, 4, 3, 5, 0, 0, 2, 3, 2, 0, 1, 0, 0, 4]
theorem case12Checks :
    (parseAliasBytes case12Bytes).map (fun parsed => parsed.certificate) =
      some case12Certificate ∧
    expectedRows case12Certificate 470 = case12Rows ∧
    (List.range 14).map (sourceUses case12Certificate) =
      case12Uses ∧
    (parseAliasBytes case12MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case12Certificate := by decide

-- 13:aliases: 14 producers; returned wire 7.
def case13Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 51, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59,
    32, 108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95,
    50, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32,
    112, 49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32,
    112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32,
    112, 49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 49, 32,
    43, 32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    54, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51, 32, 43, 32,
    112, 54, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32,
    61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 55, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 112, 53, 32, 43, 32, 112, 53, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32, 40,
    112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 54, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 112, 51, 32, 46, 42, 32, 112, 55,
    59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 61,
    32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 53, 59, 32, 108,
    101, 116, 32, 112, 49, 51, 32, 61, 32, 112, 57, 32, 43, 32, 112, 49,
    49, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32,
    61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49, 52, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32, 43, 32, 112, 57, 59,
    32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32,
    40, 40, 112, 55, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100,
    32, 125
  ]
def case13MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 51, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 120, 41, 59,
    32, 108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95,
    50, 32, 43, 32, 120, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61, 32,
    112, 49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105,
    97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32,
    112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42, 32,
    112, 49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 49, 32,
    43, 32, 112, 51, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    54, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 46, 42, 32, 112, 51,
    59, 32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 51, 32, 43, 32,
    112, 54, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32,
    61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 55, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 112, 53, 32, 43, 32, 112, 53, 59, 32,
    108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32, 40,
    112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32, 97,
    108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 54, 59, 32, 108, 101,
    116, 32, 112, 49, 49, 32, 61, 32, 112, 51, 32, 46, 42, 32, 112, 55,
    59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 61,
    32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 53, 59, 32, 108,
    101, 116, 32, 112, 49, 51, 32, 61, 32, 112, 57, 32, 43, 32, 112, 49,
    49, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32,
    61, 32, 40, 112, 50, 41, 59, 32, 108, 101, 116, 32, 112, 49, 52, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32, 43, 32, 112, 57, 59,
    32, 108, 101, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 61, 32,
    40, 40, 112, 49, 41, 41, 59, 32, 114, 101, 116, 117, 114, 110, 101, 100,
    32, 125
  ]
def case13Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := true },
      { id := 2, lhs := 0, rhs := 0, multiply := false },
      { id := 3, lhs := 1, rhs := 2, multiply := false },
      { id := 4, lhs := 0, rhs := 1, multiply := true },
      { id := 5, lhs := 1, rhs := 3, multiply := false },
      { id := 6, lhs := 3, rhs := 3, multiply := true },
      { id := 7, lhs := 3, rhs := 6, multiply := false },
      { id := 8, lhs := 0, rhs := 7, multiply := false },
      { id := 9, lhs := 5, rhs := 5, multiply := false },
      { id := 10, lhs := 2, rhs := 6, multiply := false },
      { id := 11, lhs := 3, rhs := 7, multiply := true },
      { id := 12, lhs := 0, rhs := 5, multiply := false },
      { id := 13, lhs := 9, rhs := 11, multiply := false },
      { id := 14, lhs := 2, rhs := 9, multiply := false }],
    output := 7 }
def case13Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 500, multiply := true, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 24 },
      { circuitRow := 8, traceRow := 4, multiply := false, in0 := 23, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 501, multiply := true, in0 := 22, in1 := 23, out := 26 },
      { circuitRow := 10, traceRow := 5, multiply := false, in0 := 23, in1 := 25, out := 27 },
      { circuitRow := 11, traceRow := 502, multiply := true, in0 := 25, in1 := 25, out := 28 },
      { circuitRow := 12, traceRow := 6, multiply := false, in0 := 25, in1 := 28, out := 29 },
      { circuitRow := 13, traceRow := 7, multiply := false, in0 := 22, in1 := 29, out := 30 },
      { circuitRow := 14, traceRow := 8, multiply := false, in0 := 27, in1 := 27, out := 31 },
      { circuitRow := 15, traceRow := 9, multiply := false, in0 := 24, in1 := 28, out := 32 },
      { circuitRow := 16, traceRow := 503, multiply := true, in0 := 25, in1 := 29, out := 33 },
      { circuitRow := 17, traceRow := 10, multiply := false, in0 := 22, in1 := 27, out := 34 },
      { circuitRow := 18, traceRow := 11, multiply := false, in0 := 31, in1 := 33, out := 35 },
      { circuitRow := 19, traceRow := 12, multiply := false, in0 := 24, in1 := 31, out := 36 }
    ]
def case13Uses : List Nat := [7, 3, 3, 5, 0, 3, 2, 6, 0, 2, 0, 1, 0, 0, 0]
theorem case13Checks :
    (parseAliasBytes case13Bytes).map (fun parsed => parsed.certificate) =
      some case13Certificate ∧
    expectedRows case13Certificate 472 = case13Rows ∧
    (List.range 15).map (sourceUses case13Certificate) =
      case13Uses ∧
    (parseAliasBytes case13MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case13Certificate := by decide

-- 14:direct: 15 producers; returned wire 15.
def case14Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 52, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 112, 50, 32, 61, 32, 120, 32, 43, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 49, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 46,
    42, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112,
    49, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 55, 32,
    61, 32, 112, 51, 32, 46, 42, 32, 112, 54, 59, 32, 108, 101, 116, 32,
    112, 56, 32, 61, 32, 112, 51, 32, 43, 32, 112, 51, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 120, 32, 43, 32, 112, 51, 59, 32, 108,
    101, 116, 32, 112, 49, 48, 32, 61, 32, 112, 49, 32, 43, 32, 112, 49,
    59, 32, 108, 101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 54, 32, 46,
    42, 32, 112, 49, 48, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61,
    32, 112, 49, 32, 46, 42, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112,
    49, 51, 32, 61, 32, 112, 52, 32, 43, 32, 112, 52, 59, 32, 108, 101,
    116, 32, 112, 49, 52, 32, 61, 32, 112, 53, 32, 46, 42, 32, 112, 55,
    59, 32, 108, 101, 116, 32, 112, 49, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 57, 59, 32, 112, 49, 53, 32, 125
  ]
def case14MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 52, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 46, 42, 32, 120, 59, 32, 108, 101,
    116, 32, 112, 50, 32, 61, 32, 120, 32, 43, 32, 112, 49, 59, 32, 108,
    101, 116, 32, 112, 51, 32, 61, 32, 120, 32, 46, 42, 32, 112, 50, 59,
    32, 108, 101, 116, 32, 112, 52, 32, 61, 32, 112, 49, 32, 43, 32, 112,
    51, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50, 32, 46,
    42, 32, 112, 52, 59, 32, 108, 101, 116, 32, 112, 54, 32, 61, 32, 112,
    49, 32, 46, 42, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 55, 32,
    61, 32, 112, 51, 32, 46, 42, 32, 112, 54, 59, 32, 108, 101, 116, 32,
    112, 56, 32, 61, 32, 112, 51, 32, 43, 32, 112, 51, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 120, 32, 43, 32, 112, 51, 59, 32, 108,
    101, 116, 32, 112, 49, 48, 32, 61, 32, 112, 49, 32, 43, 32, 112, 49,
    59, 32, 108, 101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 54, 32, 46,
    42, 32, 112, 49, 48, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32, 61,
    32, 112, 49, 32, 46, 42, 32, 112, 53, 59, 32, 108, 101, 116, 32, 112,
    49, 51, 32, 61, 32, 112, 52, 32, 43, 32, 112, 52, 59, 32, 108, 101,
    116, 32, 112, 49, 52, 32, 61, 32, 112, 53, 32, 46, 42, 32, 112, 55,
    59, 32, 108, 101, 116, 32, 112, 49, 53, 32, 61, 32, 112, 50, 32, 43,
    32, 112, 57, 59, 32, 112, 49, 32, 125
  ]
def case14Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := true },
      { id := 2, lhs := 0, rhs := 1, multiply := false },
      { id := 3, lhs := 0, rhs := 2, multiply := true },
      { id := 4, lhs := 1, rhs := 3, multiply := false },
      { id := 5, lhs := 2, rhs := 4, multiply := true },
      { id := 6, lhs := 1, rhs := 1, multiply := true },
      { id := 7, lhs := 3, rhs := 6, multiply := true },
      { id := 8, lhs := 3, rhs := 3, multiply := false },
      { id := 9, lhs := 0, rhs := 3, multiply := false },
      { id := 10, lhs := 1, rhs := 1, multiply := false },
      { id := 11, lhs := 6, rhs := 10, multiply := true },
      { id := 12, lhs := 1, rhs := 5, multiply := true },
      { id := 13, lhs := 4, rhs := 4, multiply := false },
      { id := 14, lhs := 5, rhs := 7, multiply := true },
      { id := 15, lhs := 2, rhs := 9, multiply := false }],
    output := 15 }
def case14Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 496, multiply := true, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 3, multiply := false, in0 := 22, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 497, multiply := true, in0 := 22, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 4, multiply := false, in0 := 23, in1 := 25, out := 26 },
      { circuitRow := 10, traceRow := 498, multiply := true, in0 := 24, in1 := 26, out := 27 },
      { circuitRow := 11, traceRow := 499, multiply := true, in0 := 23, in1 := 23, out := 28 },
      { circuitRow := 12, traceRow := 500, multiply := true, in0 := 25, in1 := 28, out := 29 },
      { circuitRow := 13, traceRow := 5, multiply := false, in0 := 25, in1 := 25, out := 30 },
      { circuitRow := 14, traceRow := 6, multiply := false, in0 := 22, in1 := 25, out := 31 },
      { circuitRow := 15, traceRow := 7, multiply := false, in0 := 23, in1 := 23, out := 32 },
      { circuitRow := 16, traceRow := 501, multiply := true, in0 := 28, in1 := 32, out := 33 },
      { circuitRow := 17, traceRow := 502, multiply := true, in0 := 23, in1 := 27, out := 34 },
      { circuitRow := 18, traceRow := 8, multiply := false, in0 := 26, in1 := 26, out := 35 },
      { circuitRow := 19, traceRow := 503, multiply := true, in0 := 27, in1 := 29, out := 36 },
      { circuitRow := 20, traceRow := 9, multiply := false, in0 := 24, in1 := 31, out := 37 }
    ]
def case14Uses : List Nat := [5, 7, 3, 5, 3, 2, 2, 1, 0, 1, 1, 0, 0, 0, 0, 4]
theorem case14Checks :
    (parseAliasBytes case14Bytes).map (fun parsed => parsed.certificate) =
      some case14Certificate ∧
    expectedRows case14Certificate 468 = case14Rows ∧
    (List.range 16).map (sourceUses case14Certificate) =
      case14Uses ∧
    (parseAliasBytes case14MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case14Certificate := by decide

-- 15:aliases: 16 producers; returned wire 8.
def case15Bytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 53, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 112, 49, 41, 59,
    32, 108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95,
    50, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61,
    32, 112, 49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108,
    105, 97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116,
    32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42,
    32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 54, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 52, 59,
    32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 50, 32, 46, 42, 32,
    112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32,
    61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 53, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 112, 52, 32, 46, 42, 32, 112, 52, 59,
    32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32,
    40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 52, 59, 32, 108,
    101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 52, 32, 46, 42, 32, 112,
    55, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32,
    61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 55, 59,
    32, 108, 101, 116, 32, 112, 49, 51, 32, 61, 32, 112, 52, 32, 46, 42,
    32, 112, 49, 49, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    49, 52, 32, 61, 32, 40, 112, 54, 41, 59, 32, 108, 101, 116, 32, 112,
    49, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32, 43, 32,
    112, 57, 59, 32, 108, 101, 116, 32, 112, 49, 53, 32, 61, 32, 112, 49,
    48, 32, 46, 42, 32, 112, 49, 49, 59, 32, 108, 101, 116, 32, 97, 108,
    105, 97, 115, 95, 49, 54, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108,
    101, 116, 32, 112, 49, 54, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49,
    54, 32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117,
    114, 110, 101, 100, 32, 61, 32, 40, 40, 112, 56, 41, 41, 59, 32, 114,
    101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case15MutatedBytes : List Nat := [
    99, 105, 114, 99, 117, 105, 116, 32, 109, 117, 116, 97, 116, 105, 111, 110,
    95, 49, 53, 40, 112, 117, 98, 108, 105, 99, 32, 120, 58, 32, 91, 109,
    51, 49, 59, 32, 52, 93, 41, 32, 45, 62, 32, 112, 117, 98, 108, 105,
    99, 32, 91, 109, 51, 49, 59, 32, 52, 93, 32, 123, 32, 108, 101, 116,
    32, 112, 49, 32, 61, 32, 120, 32, 43, 32, 120, 59, 32, 108, 101, 116,
    32, 97, 108, 105, 97, 115, 95, 50, 32, 61, 32, 40, 112, 49, 41, 59,
    32, 108, 101, 116, 32, 112, 50, 32, 61, 32, 97, 108, 105, 97, 115, 95,
    50, 32, 43, 32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 51, 32, 61,
    32, 112, 49, 32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108,
    105, 97, 115, 95, 52, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116,
    32, 112, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 52, 32, 46, 42,
    32, 112, 49, 59, 32, 108, 101, 116, 32, 112, 53, 32, 61, 32, 112, 50,
    32, 43, 32, 112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115,
    95, 54, 32, 61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 54,
    32, 61, 32, 97, 108, 105, 97, 115, 95, 54, 32, 43, 32, 112, 52, 59,
    32, 108, 101, 116, 32, 112, 55, 32, 61, 32, 112, 50, 32, 46, 42, 32,
    112, 50, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 56, 32,
    61, 32, 40, 120, 41, 59, 32, 108, 101, 116, 32, 112, 56, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 56, 32, 43, 32, 112, 53, 59, 32, 108, 101,
    116, 32, 112, 57, 32, 61, 32, 112, 52, 32, 46, 42, 32, 112, 52, 59,
    32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 48, 32, 61, 32,
    40, 112, 49, 41, 59, 32, 108, 101, 116, 32, 112, 49, 48, 32, 61, 32,
    97, 108, 105, 97, 115, 95, 49, 48, 32, 43, 32, 112, 52, 59, 32, 108,
    101, 116, 32, 112, 49, 49, 32, 61, 32, 112, 52, 32, 46, 42, 32, 112,
    55, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32,
    61, 32, 40, 112, 51, 41, 59, 32, 108, 101, 116, 32, 112, 49, 50, 32,
    61, 32, 97, 108, 105, 97, 115, 95, 49, 50, 32, 43, 32, 112, 55, 59,
    32, 108, 101, 116, 32, 112, 49, 51, 32, 61, 32, 112, 52, 32, 46, 42,
    32, 112, 49, 49, 59, 32, 108, 101, 116, 32, 97, 108, 105, 97, 115, 95,
    49, 52, 32, 61, 32, 40, 112, 54, 41, 59, 32, 108, 101, 116, 32, 112,
    49, 52, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49, 52, 32, 43, 32,
    112, 57, 59, 32, 108, 101, 116, 32, 112, 49, 53, 32, 61, 32, 112, 49,
    48, 32, 46, 42, 32, 112, 49, 49, 59, 32, 108, 101, 116, 32, 97, 108,
    105, 97, 115, 95, 49, 54, 32, 61, 32, 40, 112, 51, 41, 59, 32, 108,
    101, 116, 32, 112, 49, 54, 32, 61, 32, 97, 108, 105, 97, 115, 95, 49,
    54, 32, 43, 32, 112, 53, 59, 32, 108, 101, 116, 32, 114, 101, 116, 117,
    114, 110, 101, 100, 32, 61, 32, 40, 40, 112, 49, 41, 41, 59, 32, 114,
    101, 116, 117, 114, 110, 101, 100, 32, 125
  ]
def case15Certificate : Certificate :=
  { instructions := [
      { id := 1, lhs := 0, rhs := 0, multiply := false },
      { id := 2, lhs := 1, rhs := 1, multiply := false },
      { id := 3, lhs := 1, rhs := 2, multiply := false },
      { id := 4, lhs := 0, rhs := 1, multiply := true },
      { id := 5, lhs := 2, rhs := 2, multiply := false },
      { id := 6, lhs := 0, rhs := 4, multiply := false },
      { id := 7, lhs := 2, rhs := 2, multiply := true },
      { id := 8, lhs := 0, rhs := 5, multiply := false },
      { id := 9, lhs := 4, rhs := 4, multiply := true },
      { id := 10, lhs := 1, rhs := 4, multiply := false },
      { id := 11, lhs := 4, rhs := 7, multiply := true },
      { id := 12, lhs := 3, rhs := 7, multiply := false },
      { id := 13, lhs := 4, rhs := 11, multiply := true },
      { id := 14, lhs := 6, rhs := 9, multiply := false },
      { id := 15, lhs := 10, rhs := 11, multiply := true },
      { id := 16, lhs := 3, rhs := 5, multiply := false }],
    output := 8 }
def case15Rows : List NativeSourceRow :=
  [
      { circuitRow := 6, traceRow := 3, multiply := false, in0 := 22, in1 := 22, out := 23 },
      { circuitRow := 7, traceRow := 4, multiply := false, in0 := 23, in1 := 23, out := 24 },
      { circuitRow := 8, traceRow := 5, multiply := false, in0 := 23, in1 := 24, out := 25 },
      { circuitRow := 9, traceRow := 498, multiply := true, in0 := 22, in1 := 23, out := 26 },
      { circuitRow := 10, traceRow := 6, multiply := false, in0 := 24, in1 := 24, out := 27 },
      { circuitRow := 11, traceRow := 7, multiply := false, in0 := 22, in1 := 26, out := 28 },
      { circuitRow := 12, traceRow := 499, multiply := true, in0 := 24, in1 := 24, out := 29 },
      { circuitRow := 13, traceRow := 8, multiply := false, in0 := 22, in1 := 27, out := 30 },
      { circuitRow := 14, traceRow := 500, multiply := true, in0 := 26, in1 := 26, out := 31 },
      { circuitRow := 15, traceRow := 9, multiply := false, in0 := 23, in1 := 26, out := 32 },
      { circuitRow := 16, traceRow := 501, multiply := true, in0 := 26, in1 := 29, out := 33 },
      { circuitRow := 17, traceRow := 10, multiply := false, in0 := 25, in1 := 29, out := 34 },
      { circuitRow := 18, traceRow := 502, multiply := true, in0 := 26, in1 := 33, out := 35 },
      { circuitRow := 19, traceRow := 11, multiply := false, in0 := 28, in1 := 31, out := 36 },
      { circuitRow := 20, traceRow := 503, multiply := true, in0 := 32, in1 := 33, out := 37 },
      { circuitRow := 21, traceRow := 12, multiply := false, in0 := 25, in1 := 27, out := 38 }
    ]
def case15Uses : List Nat := [5, 5, 5, 2, 6, 2, 1, 2, 4, 1, 1, 2, 0, 0, 0, 0, 0]
theorem case15Checks :
    (parseAliasBytes case15Bytes).map (fun parsed => parsed.certificate) =
      some case15Certificate ∧
    expectedRows case15Certificate 470 = case15Rows ∧
    (List.range 17).map (sourceUses case15Certificate) =
      case15Uses ∧
    (parseAliasBytes case15MutatedBytes).map (fun parsed => parsed.certificate) ≠
      some case15Certificate := by decide

end S31.Functional.Correspondence.GeneratedMutationRows
