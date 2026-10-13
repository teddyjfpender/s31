import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

/-!
A concrete byte-level product specialization of the generic checked-run
theorem. The source tuple is statically constructed from existing M31 array
wires; `p.0` and `p.1` select those exact producers. The independent parser
derives one add node with no constructor or projection node. The package
checker connects this source-derived graph to the actual normalized
`Program.evaluate` interpreter for any checked typed assignment. Native AIR
row ownership and PCS/FRI remain separate obligations.
-/

namespace S31.Functional.Correspondence.StaticTupleErasure

open S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes
open S31.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

def exampleSource : List Nat :=
  ("circuit tuple_case(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] { let p = (x, y); let out = p.0 + p.1; out }\n".toUTF8.toList.map UInt8.toNat)

/-- For this checked product source, the generic exact-byte theorem reaches
the real normalized interpreter and its source denotation. The program,
assignment, ABI, relation, and certificate are all inputs to `checkRun`.
This theorem makes no claim about the native prover or FRI. -/
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

end S31.Functional.Correspondence.StaticTupleErasure
