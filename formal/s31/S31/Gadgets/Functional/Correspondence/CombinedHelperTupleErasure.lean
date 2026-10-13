import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

/-!
An exact-source example that composes a named helper with tuple construction
and projection. The byte parser resolves `pair.0`, `pair.1`, then the helper's
formal parameters before assigning the sole arithmetic SSA node. The same
package admission theorem checks canonical certificate, relation, ABI,
assignment and public statement bytes against actual `Program.evaluate`.
This is a bounded source-language model; Python parser equivalence and native
row/PCS authentication are separate obligations.
-/

namespace S31.Functional.Correspondence.CombinedHelperTupleErasure

open S31.Functional.Correspondence
open GeneralLinearSSAEffectsSourceBytes
open GeneralLinearSSAEffectsPackageCheck

def exampleSource : List Nat :=
  ("fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }\n" ++
  "circuit combined_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {\n" ++
  "    let pair = (x, y);\n    let left = pair.0;\n    let right = pair.1;\n" ++
  "    let out = subtract(left, right);\n    out\n}\n").toList.map Char.toNat

def exampleSSA : GeneralLinearSSAEffects.EmittedSSA :=
  { lane_count := 2,
    inputs := [{ id := 0, name := "x", visibility := "public" },
      { id := 1, name := "y", visibility := "public" }],
    nodes := [{ id := 2, name := "out", op := "sub", lhs := 0, rhs := some 1, constant := none }],
    assertions := [], output := 2 }

theorem example_meaning :
    sourceMeaning exampleSSA = some
      { output := .binary .sub (.input 0) (.input 1), assertions := [] } := by
  decide

def swappedSource : List Nat :=
  ("fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }\n" ++
  "circuit combined_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {\n" ++
  "    let pair = (x, y);\n    let left = pair.1;\n    let right = pair.0;\n" ++
  "    let out = subtract(left, right);\n    out\n}\n").toList.map Char.toNat

/-- Successful exact-byte package admission reaches the actual normalized
interpreter and proves the public claim satisfies the independently parsed
source denotation for arbitrary canonical M31 input lanes. The package checker
derives `values` from typed assignment bytes; callers cannot provide an
unrelated witness. The runtime audit checks the concrete one-subtraction SSA.
-/
theorem checked_example_program_evaluate
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (publicWords : List Nat)
    (run : GeneralLinearSSAEffectsByteRun.EffectsByteRun)
    (hcheck : checkRun exampleSource certificateBytes relationBytes abiBytes
      assignmentBytes publicWords = .ok run) :
    ∃ (n : Nat) (values : Nat → GeneralLinearSSA.Lanes n)
      (claimed : GeneralLinearSSA.Lanes n),
      denotation exampleSource values claimed ∧
      publicWords = GeneralLinearSSAPublicABI.publicWordBytes
        (GeneralLinearSSAPublicABI.orderedPublicWords run.ssa.inputs values claimed) ∧
      run.program.evaluate run.assignment = .ok run.words := by
  obtain ⟨n, values, claimed, hsource, hwords, _, heval⟩ :=
    checked_run_sound exampleSource certificateBytes relationBytes abiBytes
      assignmentBytes publicWords run hcheck
  exact ⟨n, values, claimed, hsource, hwords, heval⟩

/-- If the concrete parser result checked by the runtime audit is provided
as a premise, the accepted public claim is the ordered lane subtraction.
The theorem does not turn that executable parser result into a kernel proof;
the unconditional result above is the exact-byte source denotation theorem. -/
theorem checked_example_subtraction_given_parse
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (publicWords : List Nat)
    (run : GeneralLinearSSAEffectsByteRun.EffectsByteRun)
    (hparse : parseSource exampleSource = some exampleSSA)
    (hcheck : checkRun exampleSource certificateBytes relationBytes abiBytes
      assignmentBytes publicWords = .ok run) :
    ∃ (n : Nat) (values : Nat → GeneralLinearSSA.Lanes n)
      (claimed : GeneralLinearSSA.Lanes n),
      claimed = (fun i => values 0 i - values 1 i) ∧
      run.program.evaluate run.assignment = .ok run.words := by
  obtain ⟨n, values, claimed, ⟨ssa, meaning, hsource, hmeaning, haccept⟩,
    _, heval⟩ := checked_example_program_evaluate certificateBytes
      relationBytes abiBytes assignmentBytes publicWords run hcheck
  have hssa : ssa = exampleSSA := Option.some.inj (hsource.symm.trans hparse)
  subst ssa
  have hm : meaning =
      { output := .binary .sub (.input 0) (.input 1), assertions := [] } :=
    Option.some.inj (hmeaning.symm.trans example_meaning)
  subst meaning
  exact ⟨n, values, claimed, by simpa [GeneralLinearSSAEffects.Source.accepts,
    GeneralLinearSSAEffects.Term.eval, SourceFunctionBytes.Op.eval] using
    haccept.1, heval⟩

end S31.Functional.Correspondence.CombinedHelperTupleErasure
