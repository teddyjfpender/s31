import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsBytes

/-!
Runtime check of the actual three-lane affine/assertion production fixture.
The source meaning and expected indexed roster below are handwritten Lean
objects. This test does not prove the Python source parser or native rows.
-/

namespace S31.Audit.GeneralLinearSSAEffectsCertificateCheck

open S31.Functional.Correspondence.GeneralLinearSSAEffects
open S31.Functional.Correspondence.GeneralLinearSSAEffectsBytes
open S31.Functional.Correspondence.SourceFunctionBytes (Op)

def affineSource : Source :=
  { output := .binary .sub (.input 1) (.input 0),
    assertions := [(.input 1,
      .constant true (.constant false (.input 0) 7) 9)] }

def affineSSA : EmittedSSA :=
  { lane_count := 3,
    inputs := [
      { id := 0, name := "x", visibility := "public" },
      { id := 1, name := "y", visibility := "private" }],
    nodes := [
      { id := 2, name := "shifted", op := "add_const", lhs := 0,
        rhs := none, constant := some 7 },
      { id := 3, name := "scaled", op := "mul_const", lhs := 2,
        rhs := none, constant := some 9 },
      { id := 4, name := "out", op := "sub", lhs := 1,
        rhs := some 0, constant := none }],
    assertions := [(1, 3)], output := 4 }

def affineCertificate : Certificate :=
  { inputs := 2,
    steps := [.constant 2 0 7 false, .constant 3 2 9 true,
      .binary 4 1 0 .sub],
    assertions := [(1, 3)], output := 4 }

def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let bytes ← IO.FS.readFile path
      match checkCertificate bytes affineSource with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok (ssa, certificate) =>
          if ssa = affineSSA ∧ certificate = affineCertificate then
            IO.println "accepted: independently decoded M31 effects fixture"
            return 0
          else
            IO.eprintln "rejected: effects roster differs from reviewed fixture"
            return 1
  | _ =>
      IO.eprintln "usage: s31-general-linear-effects-certificate-check PATH"
      return 2

end S31.Audit.GeneralLinearSSAEffectsCertificateCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAEffectsCertificateCheck.run args
