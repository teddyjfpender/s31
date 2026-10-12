import S31.Gadgets.Functional.SSANamedExecution
import S31.Gadgets.Functional.SSAAirRows
import S31.Gadgets.Functional.TextSquare4Statement

/-!
One source-bound compiler chain for functional_square4.s31. A checked
let-sharing SSA certificate is alpha-renamed to the actual generated
normalized Program; the two generated multiplication nodes agree with two
packed QM31 AIR rows; an accepted public claim agrees with source semantics.
The alpha-renaming and generated Program are checked as concrete data, not
claimed as a theorem about arbitrary Python source serialization.
-/

namespace S31.Functional.TextSquare4CompilerChain

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSANamedProgram
open S31.Functional.TextSquare4Air
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Packed

private def x : Source 1 := .var ⟨0, by decide⟩

/-- Duplicating the square subtree emits one extra multiplication. -/
def duplicatedSquare : Source 1 := .mul (.mul x x) (.mul x x)

theorem shared_and_duplicated_same_value (input : Lanes) :
    sharedSquare.value (fun _ => input) =
      duplicatedSquare.value (fun _ => input) := by
  rfl

theorem sharing_saves_one_multiplication :
    (compile sharedSquare).instructions.length = 2 ∧
    (compile duplicatedSquare).instructions.length = 3 := by decide

def alphaName (name : String) : String :=
  if name == "w1" then "_s31_i1_0"
  else if name == "w2" then "result"
  else name

def alphaNode (node : Node) : Node :=
  { node with
    name := alphaName node.name,
    lhs := node.lhs.map alphaName,
    rhs := node.rhs.map alphaName }

def alphaProgram (program : Program) : Program :=
  { program with
    name := "functional_square4",
    nodes := program.nodes.map alphaNode,
    outputs := program.outputs.map alphaName }

/-- The actual source-bound normalized Program is the complete canonical
checked SSA program up to this explicit bijective renaming on its live wires.
This checks inputs, operations, metadata, order, output, and public shape. -/
theorem generated_program_is_checked_ssa :
    TextSquare4.compiled =
      alphaProgram (encode sharedSquareCertificate) := by decide

theorem formal_source_is_fourth (input : Lanes) :
    sharedSquare.value (fun _ => input) = fourth input := by rfl

/-- The generated named-node computation and both packed AIR rows agree
exactly when the claimed four-lane result has the checked source value. The
AIR premise is the local nine-residual Qm31Ops relation; lookup
authentication and native row emission remain separate. -/
theorem generated_nodes_and_air_iff_source
    (a b c d : M31) (claimed : Lanes) :
    ((TextSquare4.compiled.nodes.foldlM (fun env node => do
        return env ++ [(node.name, ← evaluateNode env node)])
          (TextSquare4Proof.inputEnv a b c d)) =
        .ok (TextSquare4Proof.inputEnv a b c d ++ [
          ("_s31_i1_0", ⟨.m31,
            [a * a, b * b, c * c, d * d]⟩),
          ("result", ⟨.m31, List.ofFn claimed⟩)]) ∧
      twoRows ![a, b, c, d] (packM31 claimed)) ↔
      claimed = sharedSquare.value (fun _ => ![a, b, c, d]) := by
  rw [compiled_nodes_iff_two_rows, two_rows_iff_values]
  simp [formal_source_is_fourth]

/-- The normalized evaluator's public-output binding rejects a forged
claim for the generated program, and the accepted claim is the same checked
source value used by the two packed AIR equations. -/
theorem accepted_public_claim_is_source
    (assignment : Assignment) (a b c d : M31)
    (claimed : Lanes) (statement : List M31)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok ⟨.m31, [a, b, c, d]⟩)
    (houtput : assigned assignment.publicOutputs "result" ⟨.m31, 4⟩ =
      .ok ⟨.m31, List.ofFn claimed⟩)
    (haccepted : TextSquare4.compiled.evaluate assignment = .ok statement) :
    claimed = sharedSquare.value (fun _ => ![a, b, c, d]) := by
  have hactual :=
    TextSquare4Statement.successful_output_is_fourth assignment
      a b c d statement hprivate hinput haccepted
  rw [houtput] at hactual
  have hwords := congrArg Value.words (Except.ok.inj hactual)
  have hclaim : claimed = fourth ![a, b, c, d] := by
    apply List.ofFn_injective
    simpa [fourth, square, List.ofFn] using hwords
  simpa [formal_source_is_fourth] using hclaim

end S31.Functional.TextSquare4CompilerChain
