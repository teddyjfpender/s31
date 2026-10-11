-- Generated from the checked first 122 STWZEVA/1 Gate base instructions.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Native opcode switch wording is checked by the exporter; Zig execution is external.
import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

namespace S31.Gadgets.Air.GeneratedDirectGateBaseVm

open S31.Gadgets.Air.DirectGatePolynomial

set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

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

/-- Remaining arithmetic instructions, before interaction reads. -/
def arithmeticTail : List Instruction := [
  ⟨38, .mul 8 12⟩,
  ⟨39, .mul 9 13⟩,
  ⟨40, .sub 38 39⟩,
  ⟨41, .mul 10 14⟩,
  ⟨42, .mul 11 15⟩,
  ⟨43, .sub 41 42⟩,
  ⟨44, .constant 2⟩,
  ⟨45, .mul 44 43⟩,
  ⟨46, .add 40 45⟩,
  ⟨47, .mul 10 15⟩,
  ⟨48, .sub 46 47⟩,
  ⟨49, .mul 11 14⟩,
  ⟨50, .sub 48 49⟩,
  ⟨51, .mul 50 1⟩,
  ⟨52, .add 8 12⟩,
  ⟨53, .mul 52 0⟩,
  ⟨54, .add 51 53⟩,
  ⟨55, .sub 8 12⟩,
  ⟨56, .mul 55 3⟩,
  ⟨57, .add 54 56⟩,
  ⟨58, .mul 8 12⟩,
  ⟨59, .mul 58 2⟩,
  ⟨60, .add 57 59⟩,
  ⟨61, .sub 16 60⟩,
  ⟨62, .mul 8 13⟩,
  ⟨63, .mul 9 12⟩,
  ⟨64, .add 62 63⟩,
  ⟨65, .mul 10 15⟩,
  ⟨66, .mul 11 14⟩,
  ⟨67, .add 65 66⟩,
  ⟨68, .constant 2⟩,
  ⟨69, .mul 68 67⟩,
  ⟨70, .add 64 69⟩,
  ⟨71, .mul 10 14⟩,
  ⟨72, .add 70 71⟩,
  ⟨73, .mul 11 15⟩,
  ⟨74, .sub 72 73⟩,
  ⟨75, .mul 74 1⟩,
  ⟨76, .add 9 13⟩,
  ⟨77, .mul 76 0⟩,
  ⟨78, .add 75 77⟩,
  ⟨79, .sub 9 13⟩,
  ⟨80, .mul 79 3⟩,
  ⟨81, .add 78 80⟩,
  ⟨82, .mul 9 13⟩,
  ⟨83, .mul 82 2⟩,
  ⟨84, .add 81 83⟩,
  ⟨85, .sub 17 84⟩,
  ⟨86, .mul 8 14⟩,
  ⟨87, .mul 9 15⟩,
  ⟨88, .sub 86 87⟩,
  ⟨89, .mul 10 12⟩,
  ⟨90, .add 88 89⟩,
  ⟨91, .mul 11 13⟩,
  ⟨92, .sub 90 91⟩,
  ⟨93, .mul 92 1⟩,
  ⟨94, .add 10 14⟩,
  ⟨95, .mul 94 0⟩,
  ⟨96, .add 93 95⟩,
  ⟨97, .sub 10 14⟩,
  ⟨98, .mul 97 3⟩,
  ⟨99, .add 96 98⟩,
  ⟨100, .mul 10 14⟩,
  ⟨101, .mul 100 2⟩,
  ⟨102, .add 99 101⟩,
  ⟨103, .sub 18 102⟩,
  ⟨104, .mul 8 15⟩,
  ⟨105, .mul 9 14⟩,
  ⟨106, .add 104 105⟩,
  ⟨107, .mul 10 13⟩,
  ⟨108, .add 106 107⟩,
  ⟨109, .mul 11 12⟩,
  ⟨110, .add 108 109⟩,
  ⟨111, .mul 110 1⟩,
  ⟨112, .add 11 15⟩,
  ⟨113, .mul 112 0⟩,
  ⟨114, .add 111 113⟩,
  ⟨115, .sub 11 15⟩,
  ⟨116, .mul 115 3⟩,
  ⟨117, .add 114 116⟩,
  ⟨118, .mul 11 15⟩,
  ⟨119, .mul 118 2⟩,
  ⟨120, .add 117 119⟩,
  ⟨121, .sub 19 120⟩
]

def arithmeticProgram : List Instruction := flagPrefix ++ arithmeticTail

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

def arithmeticRoots {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) : List K :=
  let registers := executeAll cells arithmeticProgram
  [registers 24, registers 28, registers 31, registers 34, registers 37,
   registers 61, registers 85, registers 103, registers 121]

/-- The reflected 122-opcode base interpreter gives all nine
selected arithmetic roots for arbitrary ring-valued cells. -/
theorem arithmeticRoots_eq_generated {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) :
    arithmeticRoots cells =
      GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver cells := by
  simp [arithmeticRoots, arithmeticProgram, arithmeticTail, flagPrefix,
    executeAll, execute,
    GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver]

theorem arithmeticRoots_eq_modeled {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) :
    arithmeticRoots cells = modeledArithmetic cells := by
  rw [arithmeticRoots_eq_generated,
    GeneratedDirectGateBytecodeArithmetic.bytecode_arithmetic_over_eq]

end S31.Gadgets.Air.GeneratedDirectGateBaseVm
