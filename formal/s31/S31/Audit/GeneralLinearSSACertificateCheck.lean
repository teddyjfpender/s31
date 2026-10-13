import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes

/-!
Runtime control for the reviewed two-input, five-lane certificate fixture.
It runs Lean's independent JSON and arithmetic-graph checker on the actual
file bytes. The expected source term is a handwritten Lean expression; this
control does not prove the S31 text compiler or native PCS/FRI sound.
-/

namespace S31.Audit.GeneralLinearSSACertificateCheck

open S31.Functional.Correspondence.GeneralLinearSSA
open S31.Functional.Correspondence.GeneralLinearSSABytes

def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let bytes ← IO.FS.readFile path
      match checkCertificate bytes subtractionThenDoubleSource with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok (ssa, certificate) =>
          if ssa = subtractionThenDoubleEmitted ∧
              certificate = subtractionThenDouble then
            IO.println "accepted: independently decoded linear M31 SSA fixture"
            return 0
          else
            IO.eprintln "rejected: decoded SSA differs from reviewed fixture"
            return 1
  | _ =>
      IO.eprintln "usage: s31-general-linear-certificate-check PATH"
      return 2

end S31.Audit.GeneralLinearSSACertificateCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSACertificateCheck.run args
