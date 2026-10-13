import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes

/-! Runtime control for source bytes and the effectful SSA certificate. -/

namespace S31.Audit.GeneralLinearSSAEffectsSourceCheck

open S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, certificatePath] =>
      let source ← IO.FS.readBinFile sourcePath
      let certificate ← IO.FS.readFile certificatePath
      match checkSourceCertificate (source.toList.map UInt8.toNat) certificate with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok (ssa, _, _) =>
          IO.println s!"accepted: {ssa.inputs.length} inputs, {ssa.nodes.length} nodes, {ssa.assertions.length} assertions, {ssa.lane_count} lanes"
          return 0
  | _ =>
      IO.eprintln "usage: s31-general-linear-effects-source-check SOURCE.s31 CERTIFICATE.json"
      return 2

end S31.Audit.GeneralLinearSSAEffectsSourceCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAEffectsSourceCheck.run args
