import S31.Gadgets.Functional.SSANativeTopologyCheck
import S31.Semantics.Program

/-!
The bounded text-package correspondence checker admits user-chosen names;
the older `SSANamedProgram.encode` fixes names to `x`, `w1`, and so on. This
module models a complete name table for the same one-input four-lane SSA
fragment and composes exact normalized-Program equality with the executable
native source-gate topology check.

This is a structural and field-value theorem. It does not prove the Python
lexer/serializer implements `encodeNamed`, nor a universal equivalence
between arbitrary-name `Program.evaluate` and positional SSA execution.
The latter needs an independent named-environment induction. The native
topology, Gate lookup, AIR and PCS boundaries are inherited explicitly from
`SSANativeTopologyCheck`.
-/

namespace S31.Functional.SSAGeneralNamedTopology

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSANativeTopologyCheck

/-- Position zero is the public input; position `k > 0` names instruction
`k`. Source syntax identifier validity remains an external parser premise. -/
def nameAt (names : List String) (id : Nat) : String :=
  names.getD id ""

def instructionNode (names : List String)
    (instruction : Instruction) : Node :=
  { name := nameAt names instruction.id,
    op := if instruction.multiply then .mul else .add,
    lhs := some (nameAt names instruction.lhs),
    rhs := some (nameAt names instruction.rhs) }

/-- Exact normalized shape for the one-public-input, one-public-output
M31x4 arithmetic fragment. Metadata such as the program name is part of the
equality checked below. -/
def encodeNamed (programName : String) (names : List String)
    (certificate : Certificate) : Program :=
  { name := programName,
    inputs := [{ name := nameAt names 0, shape := ⟨.m31, 4⟩,
      visibility := .«public» }],
    nodes := certificate.instructions.map (instructionNode names),
    assertions := [],
    outputs := [nameAt names certificate.output] }

/-- The table is neither short, ambiguous nor allowed to designate the
input as a returned let binding. `Program.validate` separately checks named
operand resolution and shape. -/
def NameTableValid (names : List String)
    (certificate : Certificate) : Prop :=
  names.length = certificate.instructions.length + 1 ∧
  names.Nodup ∧
  "" ∉ names ∧
  certificate.output ≠ 0

/-- One executable Lean admission decision for source certificate, name
table, normalized relation and projected native arithmetic source gates. -/
def checkNamedSourceRows (source : Source 1)
    (certificate : Certificate) (programName : String)
    (names : List String) (program : Program)
    (gates : List Gate) : Option (List Nat) := do
  let addresses ← checkSourceRows source certificate gates
  if NameTableValid names certificate then
    if program = encodeNamed programName names certificate then
      match program.validate with
      | .error _ => none
      | .ok _ => some addresses
    else none
  else none

/-- Checker acceptance fixes the complete named node sequence, input and
output declarations, source certificate, and native source-gate schedule. -/
theorem checked_named_structure (source : Source 1)
    (certificate : Certificate) (programName : String)
    (names : List String) (program : Program)
    (gates : List Gate) (finalAddresses : List Nat)
    (hcheck : checkNamedSourceRows source certificate programName names
      program gates = some finalAddresses) :
    NameTableValid names certificate ∧
    program = encodeNamed programName names certificate ∧
    (∃ shapes, program.validate = .ok shapes) ∧
    checkSourceRows source certificate gates = some finalAddresses := by
  unfold checkNamedSourceRows at hcheck
  cases hsource : checkSourceRows source certificate gates with
  | none => simp [hsource] at hcheck
  | some addresses =>
      by_cases hnames : NameTableValid names certificate
      · by_cases hprogram :
            program = encodeNamed programName names certificate
        · cases hvalid : program.validate with
          | error err => simp [hsource, hnames, hprogram, hvalid] at hcheck
          | ok shapes =>
              have haddresses : addresses = finalAddresses := by
                simpa [hsource, hnames, hprogram, hvalid] using hcheck
              subst addresses
              exact ⟨hnames, hprogram, ⟨shapes, hvalid⟩, hsource⟩
        · simp [hsource, hnames, hprogram] at hcheck
      · simp [hsource, hnames] at hcheck

theorem checked_named_nodes (source : Source 1)
    (certificate : Certificate) (programName : String)
    (names : List String) (program : Program)
    (gates : List Gate) (finalAddresses : List Nat)
    (hcheck : checkNamedSourceRows source certificate programName names
      program gates = some finalAddresses) :
    program.inputs = [{ name := nameAt names 0,
      shape := ⟨.m31, 4⟩, visibility := .«public» }] ∧
    program.nodes = certificate.instructions.map (instructionNode names) ∧
    program.outputs = [nameAt names certificate.output] := by
  have hp := (checked_named_structure source certificate programName names
    program gates finalAddresses hcheck).2.1
  subst program
  exact ⟨rfl, rfl, rfl⟩

/-- The user names cannot change a claimed field value once the complete
named relation and native source gates have passed the composite checker.
The theorem still assumes authenticated addressed row values. -/
theorem checked_named_source_value (source : Source 1)
    (certificate : Certificate) (programName : String)
    (names : List String) (program : Program)
    (input claimed : Lanes) (rows : List Row)
    (finalAddresses : List Nat) (finalValues : List Lanes)
    (hcheck : checkNamedSourceRows source certificate programName names
      program (rows.map Row.gate) = some finalAddresses)
    (hauth : AuthenticatedRows [0] [input] rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  have hsource := (checked_named_structure source certificate programName
    names program (rows.map Row.gate) finalAddresses hcheck).2.2.2
  exact checked_source_rows_sound source certificate input claimed rows
    finalAddresses finalValues hsource hauth hclaim

/-- A concrete program with user-chosen names, accepted by the same
composite checker used in the general theorem. -/
def renamedSquareProgram : Program :=
  encodeNamed "pow4" ["input", "square", "fourth"]
    sharedSquareCertificate

theorem renamed_square_checked :
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "fourth"] renamedSquareProgram
      sharedSquareGates = some [0, 37, 83] := by decide

theorem malformed_name_tables_rejected :
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "square"] renamedSquareProgram
      sharedSquareGates = none ∧
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "", "fourth"] renamedSquareProgram
      sharedSquareGates = none ∧
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square"] renamedSquareProgram
      sharedSquareGates = none := by decide

theorem changed_named_relation_rejected :
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "fourth"]
      { renamedSquareProgram with outputs := ["square"] }
      sharedSquareGates = none ∧
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "fourth"]
      { renamedSquareProgram with nodes :=
        [{ name := "square", op := .mul,
           lhs := some "fourth", rhs := some "input" },
         { name := "fourth", op := .mul,
           lhs := some "square", rhs := some "square" }] }
      sharedSquareGates = none := by decide

end S31.Functional.SSAGeneralNamedTopology
