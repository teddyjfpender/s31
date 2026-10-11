import S31.Gadgets.Air.DirectGateOodsComposition

/-!
Pure mapping from the selected Gate verifier's lookup draw and claimed-sum
field element to the seven extension parameters consumed by STWZEVA/1.
Transcript origin and M31-to-QM31 implementation correspondence are checked
source premises, not consequences of this algebraic theorem.
-/

namespace S31.Gadgets.Air.DirectGateTranscriptParams

open S31.Gadgets.Packed
open S31.Gadgets.Air.DirectGateOodsArithmetic

/-- Native `M31.fromCanonical(1 << 9).inv()` lifted to QM31. -/
def claimScale : QM := algebraMap F QM ((512 : F)⁻¹)

theorem claim_scale_eq_qm_inverse : claimScale = (512 : QM)⁻¹ := by
  simp only [claimScale, map_inv₀]
  exact congrArg Inv.inv (map_ofNat (algebraMap F QM) 512)

def claimedScaled (claimed : QM) : QM := claimed * claimScale

theorem claimed_scaled_eq_div (claimed : QM) :
    claimedScaled claimed = claimed / 512 := by
  rw [claimedScaled, claim_scale_eq_qm_inverse]
  rfl

/-- The selected component's installed extension source table is
`alpha¹,alpha²,alpha³,alpha⁴,alpha⁵,z,claimed/512`. -/
def extensionParam (z alpha claimed : QM) (slot : Fin 7) : QM :=
  match slot.val with
  | 0 => alpha
  | 1 => alpha ^ 2
  | 2 => alpha ^ 3
  | 3 => alpha ^ 4
  | 4 => alpha ^ 5
  | 5 => z
  | _ => claimedScaled claimed

theorem extension_param_order (z alpha claimed : QM) :
    List.ofFn (extensionParam z alpha claimed) =
      [alpha, alpha ^ 2, alpha ^ 3, alpha ^ 4, alpha ^ 5,
        z, claimed / 512] := by
  have h : List.ofFn (extensionParam z alpha claimed) =
      [alpha, alpha ^ 2, alpha ^ 3, alpha ^ 4, alpha ^ 5,
        z, claimedScaled claimed] := by
    rfl
  rw [h, claimed_scaled_eq_div]

end S31.Gadgets.Air.DirectGateTranscriptParams
