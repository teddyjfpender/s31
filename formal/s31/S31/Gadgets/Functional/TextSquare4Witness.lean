import S31.Gadgets.Functional.TextSquare4NativeBoundary

/-!
One concrete honest witness for the source-generated input-to-output circuit
path. This prevents the local-row soundness theorem from being vacuous. It is
not a witness for every other native range/representation component row.
-/

namespace S31.Functional.TextSquare4Witness

open S31.Gadgets.Packed
open S31.Functional.TextSquare4NativeBoundary

def zeroWire (address : Nat) : Quad :=
  if address = 1 then unit ⟨0, by decide⟩
  else if address = 2 then unit ⟨2, by decide⟩
  else if address = 15 then unit ⟨1, by decide⟩
  else if address = 16 then unit ⟨3, by decide⟩
  else if address = 27 then unitInverse ⟨1, by decide⟩
  else if address = 30 then unitInverse ⟨2, by decide⟩
  else if address = 33 then unitInverse ⟨3, by decide⟩
  else base 0

set_option maxRecDepth 4096 in
theorem zero_claim_has_native_path_witness :
    inputBoundary zeroWire (fun _ : Fin 4 => 0) ∧
    arithmeticGateRows zeroWire ∧
    nativeOutputRows zeroWire (fun _ : Fin 4 => 0) := by
  unfold inputBoundary arithmeticGateRows nativeOutputRows
  simp only [S31.Gadgets.Air.Qm31Ops.accepts_encoded]
  decide

theorem zero_wire_forged_one_rejected :
    ¬ nativeOutputRows zeroWire (fun _ : Fin 4 => 1) := by
  intro hforged
  have hhonest := zero_claim_has_native_path_witness
  have hclaim := native_public_claim_sound zeroWire
    (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 1)
    hhonest.1 hhonest.2.1 hforged
  have hfirst := congrFun hclaim ⟨0, by decide⟩
  have hbad : (1 : S31.M31) = 0 := by
    simpa [S31.Functional.TextSquare4Air.fourth,
      S31.Functional.TextSquare4Air.square] using hfirst
  exact (by decide : (1 : S31.M31) ≠ 0) hbad

end S31.Functional.TextSquare4Witness
