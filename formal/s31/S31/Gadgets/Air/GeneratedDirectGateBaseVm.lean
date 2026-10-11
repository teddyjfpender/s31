-- Generated from the checked first 38 STWZEVA/1 Gate base instructions.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Native opcode switch wording is checked by the exporter; Zig execution is external.
import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

namespace S31.Gadgets.Air.GeneratedDirectGateBaseVm

open S31.Gadgets.Air.DirectGatePolynomial

inductive BaseOp where
  | fixed (column : Fin 8)
  | main (column : Fin 12)
  | constant (value : Nat)
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)

structure Instruction where
  dst : Nat
  op : BaseOp

def execute {K : Type*} [CommRing K] (cells : ArithmeticCells K)
    (registers : Nat → K) (instruction : Instruction) : Nat → K :=
  let value := match instruction.op with
    | .fixed column => cells.localFixed column
    | .main column => cells.main column
    | .constant n => (n : K)
    | .add left right => registers left + registers right
    | .sub left right => registers left - registers right
    | .mul left right => registers left * registers right
  fun index => if index == instruction.dst then value else registers index

def executeAll {K : Type*} [CommRing K] (cells : ArithmeticCells K)
    (instructions : List Instruction) : Nat → K :=
  instructions.foldl (execute cells) (fun _ => 0)

/-- Exactly the installed base instruction prefix through register 37. -/
def flagPrefix : List Instruction := [
  ⟨0, .fixed 0⟩,
  ⟨1, .fixed 1⟩,
  ⟨2, .fixed 2⟩,
  ⟨3, .fixed 3⟩,
  ⟨4, .fixed 4⟩,
  ⟨5, .fixed 5⟩,
  ⟨6, .fixed 6⟩,
  ⟨7, .fixed 7⟩,
  ⟨8, .main 0⟩,
  ⟨9, .main 1⟩,
  ⟨10, .main 2⟩,
  ⟨11, .main 3⟩,
  ⟨12, .main 4⟩,
  ⟨13, .main 5⟩,
  ⟨14, .main 6⟩,
  ⟨15, .main 7⟩,
  ⟨16, .main 8⟩,
  ⟨17, .main 9⟩,
  ⟨18, .main 10⟩,
  ⟨19, .main 11⟩,
  ⟨20, .add 0 3⟩,
  ⟨21, .add 20 1⟩,
  ⟨22, .add 21 2⟩,
  ⟨23, .constant 1⟩,
  ⟨24, .sub 22 23⟩,
  ⟨25, .constant 0⟩,
  ⟨26, .constant 1⟩,
  ⟨27, .sub 0 26⟩,
  ⟨28, .mul 0 27⟩,
  ⟨29, .constant 1⟩,
  ⟨30, .sub 3 29⟩,
  ⟨31, .mul 3 30⟩,
  ⟨32, .constant 1⟩,
  ⟨33, .sub 1 32⟩,
  ⟨34, .mul 1 33⟩,
  ⟨35, .constant 1⟩,
  ⟨36, .sub 2 35⟩,
  ⟨37, .mul 2 36⟩
]

def flagRoots {K : Type*} [CommRing K] (cells : ArithmeticCells K) : List K :=
  let registers := executeAll cells flagPrefix
  [registers 24, registers 28, registers 31, registers 34, registers 37]

/-- The reflected opcode interpreter agrees with the first five
generated Gate arithmetic roots for every commutative ring, including
QM31 samples. This does not prove native Zig executes the opcode switch. -/
theorem flagRoots_eq_generated {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) :
    flagRoots cells =
      (GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver cells).take 5 := by
  simp [flagRoots, executeAll, flagPrefix, execute,
    GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver]

/-- These interpreted roots are the first five Gate AIR polynomials. -/
theorem flagRoots_eq_modeled {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) :
    flagRoots cells = (modeledArithmetic cells).take 5 := by
  rw [flagRoots_eq_generated,
    GeneratedDirectGateBytecodeArithmetic.bytecode_arithmetic_over_eq]

end S31.Gadgets.Air.GeneratedDirectGateBaseVm
