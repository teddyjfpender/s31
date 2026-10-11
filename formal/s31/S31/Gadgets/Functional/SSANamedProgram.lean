import S31.Gadgets.Functional.SSAEmitterProof
import S31.Semantics.Program

/-!
A deliberately small, canonical named serialization of the checked four-lane
SSA fragment. This is a Lean model of normalized `Program.nodes`, not a proof
about the production Python parser or JSON serializer. Exact structural
equality to `encode` prevents an accepted program from changing names, edge
order, operations, outputs, or metadata. Native `Program.validate` enforces
name uniqueness, operand resolution, shape, and public word bounds.
-/

namespace S31.Functional.SSANamedProgram

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSAEmitterProof

def wireName (id : Nat) : String :=
  if id == 0 then "x" else "w" ++ toString id

def Instruction.toNode (instruction : Instruction) : Node :=
  { name := wireName instruction.id,
    op := if instruction.multiply then .mul else .add,
    lhs := some (wireName instruction.lhs),
    rhs := some (wireName instruction.rhs) }

def encode (certificate : Certificate) : Program :=
  { name := "ssa_four_lanes",
    inputs := [{ name := "x", shape := ⟨.m31, 4⟩, visibility := .«public» }],
    nodes := certificate.instructions.map Instruction.toNode,
    assertions := [],
    outputs := [wireName certificate.output] }

/-- The named checker accepts only the exact serialization of a checked SSA
certificate and a program accepted by the actual S31 normalized validator.
This checks canonical output, unique names, valid backward operand resolution,
and the four-lane public statement shape. -/
def checkNamed (source : Source 1) (certificate : Certificate)
    (program : Program) : Option Unit := do
  let _ ← check source certificate
  if program != encode certificate then none else
  match program.validate with
  | .error _ => none
  | .ok _ => some ()

theorem checkNamed_positional (source : Source 1)
    (certificate : Certificate) (program : Program)
    (h : checkNamed source certificate program = some ()) :
    check source certificate = some () := by
  unfold checkNamed at h
  cases hc : check source certificate with
  | none => simp [hc] at h
  | some found =>
      cases found
      simpa using hc

theorem checkNamed_canonical (source : Source 1)
    (certificate : Certificate) (program : Program)
    (h : checkNamed source certificate program = some ()) :
    program = encode certificate := by
  unfold checkNamed at h
  cases hc : check source certificate with
  | none => simp [hc] at h
  | some found =>
      cases found
      by_cases hp : program = encode certificate
      · exact hp
      · simp [hc, hp] at h

theorem checkNamed_valid (source : Source 1)
    (certificate : Certificate) (program : Program)
    (h : checkNamed source certificate program = some ()) :
    ∃ shapes, program.validate = .ok shapes := by
  unfold checkNamed at h
  cases hc : check source certificate with
  | none => simp [hc] at h
  | some found =>
      cases found
      cases hv : program.validate with
      | error err => simp [hc, hv] at h
      | ok shapes => exact ⟨shapes, rfl⟩

/-- Accepted named programs represent exactly the checked positional trace,
which evaluates every arithmetic step with the actual `evaluateNode`. -/
theorem checked_named_trace_sound (source : Source 1)
    (certificate : Certificate) (program : Program) (input : Lanes)
    (h : checkNamed source certificate program = some ()) :
    program.nodes = certificate.instructions.map Instruction.toNode ∧
    program.outputs = [wireName certificate.output] ∧
    executeNormalized certificate input =
      some (source.value (fun _ => input)) := by
  have hp := checkNamed_canonical source certificate program h
  have hc := checkNamed_positional source certificate program h
  constructor
  · simpa [hp, encode]
  constructor
  · simpa [hp, encode]
  · exact checked_certificate_normalized_sound source certificate input hc

def sharedSquareProgram : Program := encode sharedSquareCertificate

theorem shared_square_named_accepted :
    checkNamed sharedSquare sharedSquareCertificate sharedSquareProgram =
      some () := by decide

/-- The concrete named node list itself, with real name lookup and
`evaluateNode`, computes the fourth power on arbitrary field inputs. This is
stronger than testing a single assignment, but still one source instance. -/
theorem shared_square_named_nodes_correct (a b c d : M31) :
    (sharedSquareProgram.nodes.foldlM (fun env node => do
      return env ++ [(node.name, ← evaluateNode env node)])
        [("x", ⟨.m31, [a, b, c, d]⟩)]) =
      .ok ([("x", ⟨.m31, [a, b, c, d]⟩)] ++
        [("w1", ⟨.m31, [a * a, b * b, c * c, d * d]⟩),
         ("w2", ⟨.m31, [(a * a) * (a * a),
           (b * b) * (b * b), (c * c) * (c * c),
           (d * d) * (d * d)]⟩)]) := by
  rfl

def reorderedNodes : Program :=
  { sharedSquareProgram with nodes := sharedSquareProgram.nodes.reverse }

def duplicateNode : Program :=
  { sharedSquareProgram with nodes :=
      [Instruction.toNode
          { id := 1, lhs := 0, rhs := 0, multiply := true },
       Instruction.toNode
          { id := 1, lhs := 0, rhs := 0, multiply := true }] }

def unboundOperand : Program :=
  { sharedSquareProgram with nodes :=
      [{ (Instruction.toNode
          { id := 1, lhs := 0, rhs := 0, multiply := true }) with
          lhs := some "missing" },
       Instruction.toNode
          { id := 2, lhs := 1, rhs := 1, multiply := true }] }

def malformedOutput : Program :=
  { sharedSquareProgram with outputs := ["missing"] }

theorem malformed_named_programs_rejected :
    checkNamed sharedSquare sharedSquareCertificate reorderedNodes = none ∧
    checkNamed sharedSquare sharedSquareCertificate duplicateNode = none ∧
    checkNamed sharedSquare sharedSquareCertificate unboundOperand = none ∧
    checkNamed sharedSquare sharedSquareCertificate malformedOutput = none :=
  by decide

/-- The production-shaped validator independently detects each malformed
named graph, before the certificate comparison is considered. -/
theorem malformed_named_graphs_invalid :
    reorderedNodes.validate = .error .unknownOperand ∧
    duplicateNode.validate = .error .malformed ∧
    unboundOperand.validate = .error .unknownOperand ∧
    malformedOutput.validate = .error .unknownOperand := by decide

/-- Concrete execution also exercises the real named environment: the
second node reads the first node's result by its declared wire name. -/
def squareAssignment : Assignment :=
  { publicInputs := [("x", [2, 3, 4, 5])],
    publicOutputs := [("w2", [16, 81, 256, 625])] }

theorem shared_square_named_evaluates :
    sharedSquareProgram.evaluate squareAssignment =
      .ok ([2, 3, 4, 5, 16, 81, 256, 625].map
        RiscvRefinement.M31.reduce) := by decide

end S31.Functional.SSANamedProgram
