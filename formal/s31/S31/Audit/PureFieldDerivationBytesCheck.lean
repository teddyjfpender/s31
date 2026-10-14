import S31.Gadgets.Functional.Correspondence.PureFieldDerivationBytes

/-! Command-line gate for the bounded pure-field exact-byte correspondence. -/

namespace S31.Audit.PureFieldDerivationBytesCheck

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, certificatePath, relationPath] =>
      let source ← IO.FS.readBinFile sourcePath
      let certificate ← IO.FS.readFile certificatePath
      let relation ← IO.FS.readFile relationPath
      match S31.Functional.Correspondence.PureFieldDerivationBytes.checkBytes
          (source.toList.map UInt8.toNat) certificate relation with
      | .ok _ =>
          IO.println "accepted: exact source, typed derivation, normalized relation"
          return 0
      | .error reason =>
          IO.eprintln s!"rejected: {reason}"
          return 1
  | _ =>
      IO.eprintln "usage: SOURCE CERTIFICATE RELATION"
      return 2

end S31.Audit.PureFieldDerivationBytesCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.PureFieldDerivationBytesCheck.run args
