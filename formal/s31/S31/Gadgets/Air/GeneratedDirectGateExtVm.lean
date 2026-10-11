-- Generated from checked STWZEVA/1 Gate extension instructions 9–96.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Native extension loop is source checked; Zig execution remains external.
import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp

namespace S31.Gadgets.Air.GeneratedDirectGateExtVm

open S31.Gadgets.Air.DirectGateOodsArithmetic

open S31.Gadgets.Air.DirectGateOodsLogUp

set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

inductive ExtOp where
  | secure (a b c d : Nat)
  | param (slot : Nat)
  | constant (value : Nat)
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  | neg (source : Nat)

structure Instruction where
  dst : Nat
  op : ExtOp

def baseRead (cells : Cells) : Nat → QM
  | 4 => cells.localFixed 4
  | 5 => cells.localFixed 5
  | 6 => cells.localFixed 6
  | 7 => cells.localFixed 7
  | 8 => cells.main 0
  | 9 => cells.main 1
  | 10 => cells.main 2
  | 11 => cells.main 3
  | 12 => cells.main 4
  | 13 => cells.main 5
  | 14 => cells.main 6
  | 15 => cells.main 7
  | 16 => cells.main 8
  | 17 => cells.main 9
  | 18 => cells.main 10
  | 19 => cells.main 11
  | 25 => 0
  | 122 => cells.interaction 0
  | 123 => cells.interaction 1
  | 124 => cells.interaction 2
  | 125 => cells.interaction 3
  | 126 => cells.previousInteraction 4
  | 127 => cells.interaction 4
  | 128 => cells.previousInteraction 5
  | 129 => cells.interaction 5
  | 130 => cells.previousInteraction 6
  | 131 => cells.interaction 6
  | 132 => cells.previousInteraction 7
  | 133 => cells.interaction 7
  | _ => 0

def paramRead (alpha z claimedScaled : QM) : Nat → QM
  | 0 => alpha ^ 1
  | 1 => alpha ^ 2
  | 2 => alpha ^ 3
  | 3 => alpha ^ 4
  | 4 => alpha ^ 5
  | 5 => z
  | 6 => claimedScaled
  | _ => 0

def execute (cells : Cells) (alpha z claimedScaled : QM)
    (registers : Nat → QM) (instruction : Instruction) : Nat → QM :=
  let value := match instruction.op with
    | .secure a b c d => fromPartialEvals
        (baseRead cells a) (baseRead cells b)
        (baseRead cells c) (baseRead cells d)
    | .param slot => paramRead alpha z claimedScaled slot
    | .constant n => (n : QM)
    | .add left right => registers left + registers right
    | .sub left right => registers left - registers right
    | .mul left right => registers left * registers right
    | .neg source => -registers source
  fun index => if index == instruction.dst then value else registers index

def extensionProgram : List Instruction := [
  ⟨9, .param 0⟩,
  ⟨10, .secure 4 25 25 25⟩,
  ⟨11, .mul 9 10⟩,
  ⟨12, .constant 378353459⟩,
  ⟨13, .add 12 11⟩,
  ⟨14, .param 1⟩,
  ⟨15, .secure 8 25 25 25⟩,
  ⟨16, .mul 14 15⟩,
  ⟨17, .add 13 16⟩,
  ⟨18, .param 2⟩,
  ⟨19, .secure 9 25 25 25⟩,
  ⟨20, .mul 18 19⟩,
  ⟨21, .add 17 20⟩,
  ⟨22, .param 3⟩,
  ⟨23, .secure 10 25 25 25⟩,
  ⟨24, .mul 22 23⟩,
  ⟨25, .add 21 24⟩,
  ⟨26, .param 4⟩,
  ⟨27, .secure 11 25 25 25⟩,
  ⟨28, .mul 26 27⟩,
  ⟨29, .add 25 28⟩,
  ⟨30, .param 5⟩,
  ⟨31, .sub 29 30⟩,
  ⟨32, .param 0⟩,
  ⟨33, .secure 5 25 25 25⟩,
  ⟨34, .mul 32 33⟩,
  ⟨35, .constant 378353459⟩,
  ⟨36, .add 35 34⟩,
  ⟨37, .param 1⟩,
  ⟨38, .secure 12 25 25 25⟩,
  ⟨39, .mul 37 38⟩,
  ⟨40, .add 36 39⟩,
  ⟨41, .param 2⟩,
  ⟨42, .secure 13 25 25 25⟩,
  ⟨43, .mul 41 42⟩,
  ⟨44, .add 40 43⟩,
  ⟨45, .param 3⟩,
  ⟨46, .secure 14 25 25 25⟩,
  ⟨47, .mul 45 46⟩,
  ⟨48, .add 44 47⟩,
  ⟨49, .param 4⟩,
  ⟨50, .secure 15 25 25 25⟩,
  ⟨51, .mul 49 50⟩,
  ⟨52, .add 48 51⟩,
  ⟨53, .param 5⟩,
  ⟨54, .sub 52 53⟩,
  ⟨55, .secure 7 25 25 25⟩,
  ⟨56, .neg 55⟩,
  ⟨57, .param 0⟩,
  ⟨58, .secure 6 25 25 25⟩,
  ⟨59, .mul 57 58⟩,
  ⟨60, .constant 378353459⟩,
  ⟨61, .add 60 59⟩,
  ⟨62, .param 1⟩,
  ⟨63, .secure 16 25 25 25⟩,
  ⟨64, .mul 62 63⟩,
  ⟨65, .add 61 64⟩,
  ⟨66, .param 2⟩,
  ⟨67, .secure 17 25 25 25⟩,
  ⟨68, .mul 66 67⟩,
  ⟨69, .add 65 68⟩,
  ⟨70, .param 3⟩,
  ⟨71, .secure 18 25 25 25⟩,
  ⟨72, .mul 70 71⟩,
  ⟨73, .add 69 72⟩,
  ⟨74, .param 4⟩,
  ⟨75, .secure 19 25 25 25⟩,
  ⟨76, .mul 74 75⟩,
  ⟨77, .add 73 76⟩,
  ⟨78, .param 5⟩,
  ⟨79, .sub 77 78⟩,
  ⟨80, .constant 1⟩,
  ⟨81, .mul 54 80⟩,
  ⟨82, .constant 1⟩,
  ⟨83, .mul 31 82⟩,
  ⟨84, .add 81 83⟩,
  ⟨85, .mul 31 54⟩,
  ⟨86, .secure 122 123 124 125⟩,
  ⟨87, .mul 86 85⟩,
  ⟨88, .sub 87 84⟩,
  ⟨89, .secure 126 128 130 132⟩,
  ⟨90, .secure 127 129 131 133⟩,
  ⟨91, .sub 90 89⟩,
  ⟨92, .sub 91 86⟩,
  ⟨93, .param 6⟩,
  ⟨94, .add 92 93⟩,
  ⟨95, .mul 94 79⟩,
  ⟨96, .sub 95 56⟩
]

def logupRoots (cells : Cells) (alpha z claimedScaled : QM) : QM × QM :=
  let registers := extensionProgram.foldl
    (execute cells alpha z claimedScaled) (fun _ => 0)
  (registers 88, registers 96)

/-- The interpreted selected extension suffix yields exactly the two
source-bound LogUp roots at arbitrary QM31 OODS cells. -/
theorem logupRoots_eq_generated (cells : Cells)
    (alpha z claimedScaled : QM) :
    logupRoots cells alpha z claimedScaled =
      GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled := by
  simp [logupRoots, extensionProgram, execute, baseRead, paramRead,
    GeneratedDirectGateBytecodeLogUp.bytecodeLogup]

end S31.Gadgets.Air.GeneratedDirectGateExtVm
