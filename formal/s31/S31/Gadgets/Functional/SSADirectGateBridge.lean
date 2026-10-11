import S31.Gadgets.Functional.SSACertificate

/-!
A narrow bridge between a checked positional certificate and the source
arithmetic rows in the native direct-gate trace. The Python package checker
independently parses the source bytes and checks the entire 512-row native
topology. A generated Lean instance can then check the exact source SSA and
the observed gate addresses/row positions against this model.

The model does not parse source bytes, derive the non-source constant rows,
authenticate the preprocessed root, or prove the Gate lookup and PCS argument.
-/

namespace S31.Functional.SSADirectGateBridge

open S31.Functional.SSACertificate

structure NativeSourceRow where
  circuitRow : Nat
  traceRow : Nat
  multiply : Bool
  in0 : Nat
  in1 : Nat
  out : Nat
deriving DecidableEq, Repr

/-- Direct input packing ends at circuit wire 22. SSA wire `id` therefore
occupies direct-circuit address `22 + id`. -/
def address (id : Nat) : Nat := 22 + id

/-- The native writer groups add gates before sub, multiply, and pointwise
multiply gates. Three input-pack adds precede source adds. The checked bounded
profile has one constant sub and 27 ordinary mul gates, so source pointwise
rows begin at `totalAddRows + 28`. The Python checker separately checks these
counts and every other native row. -/
def expectedRows (certificate : Certificate) (totalAddRows : Nat) :
    List NativeSourceRow :=
  let (_, _, rows) := certificate.instructions.foldl
    (fun (state : Nat × Nat × List NativeSourceRow) instruction =>
      let (priorAdds, priorMuls, rows) := state
      let row : NativeSourceRow :=
        { circuitRow := 5 + instruction.id,
          traceRow := if instruction.multiply then
              totalAddRows + 28 + priorMuls else 3 + priorAdds,
          multiply := instruction.multiply,
          in0 := address instruction.lhs,
          in1 := address instruction.rhs,
          out := address instruction.id }
      (priorAdds + if instruction.multiply then 0 else 1,
       priorMuls + if instruction.multiply then 1 else 0,
       rows ++ [row]))
    (0, 0, [])
  rows

/-- An accepted concrete source certificate and exact observed source rows
inherit the established arbitrary-input SSA semantic theorem. This theorem
keeps the row equality premise explicit: the Python package checker supplies
it from the native exporter; Lean does not establish that the exporter is
faithful or that committed columns match this artifact. -/
theorem checked_rows_source_sound (source : Source 1)
    (certificate : Certificate) (input : Lanes)
    (observedRows : List NativeSourceRow) (totalAddRows : Nat)
    (hsource : check source certificate = some ())
    (hrows : observedRows = expectedRows certificate totalAddRows) :
    observedRows = expectedRows certificate totalAddRows ∧
      executeNormalized certificate input =
        some (source.value (fun _ => input)) :=
  ⟨hrows, checked_certificate_normalized_sound source certificate input hsource⟩

end S31.Functional.SSADirectGateBridge
