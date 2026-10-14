import S31.Gadgets.Air.GateAddConstComposition
import S31.Gadgets.Functional.Correspondence.StructuralNativeFixedConstant

/-!
The literal-seven case of `add_const` closes its value premise through the
native finalization chain. The physical add row must read the same address as
the chain's last Mul output. AIR validity, Gate event/cell authentication,
and the public `u` anchor remain explicit assumptions for an accepted proof.
-/

namespace S31.Gadgets.Air.GateAddConstSevenFinalization

open S31.Gadgets.Air.GateAddConstComposition
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeGateOwnership
open S31.Functional.Correspondence.StructuralNativeFixedConstant

/-- For every active lane, an `add_const 7` physical row reads the value
forced by the installed seven-finalization path, so no separate assumption
that the constant cell contains seven is needed. `hread` is the trace-gather
and Gate lookup address/value join; its authentication is outside this local
AIR theorem. -/
theorem active_lanes_seven_sound (length : Nat)
    (input output : Fin length → S31.M31)
    (rows : Nat → S31.Gadgets.Air.GateSourcePhysicalRows.PhysicalRow)
    (wire : Nat → Quad)
    (gates : List Gate) (mulGates : List MulGate) (path : SevenPath)
    (hpublicU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hpath : path.owned gates mulGates)
    (hlinear : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates)
    (hop : ∀ index : Fin length, (rows (index.val / 4)).op = .add)
    (hfixed : ∀ index : Fin length,
      (rows (index.val / 4)).flags =
        S31.Gadgets.Air.Qm31Ops.encode (rows (index.val / 4)).op)
    (hair : ∀ index : Fin length, ∀ residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals
        (rows (index.val / 4)).flags (rows (index.val / 4)).lhs
        (rows (index.val / 4)).rhs (rows (index.val / 4)).output,
        residual = 0)
    (hread : ∀ index : Fin length,
      (rows (index.val / 4)).rhs =
        S31.Gadgets.Air.Qm31Ops.packM31 (wire path.broadcast7))
    (hinput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (rows (index.val / 4)).lhs
        (activeLane index.val) = S31.Field.toZMod (input index))
    (houtput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (rows (index.val / 4)).output
        (activeLane index.val) = S31.Field.toZMod (output index)) :
    ∀ index : Fin length,
      output index = input index + RiscvRefinement.M31.reduce 7 := by
  have hseven := seven_path_air_sound wire gates mulGates path
    hpublicU hpath hlinear hmul
  apply active_lanes_m31_sound length (RiscvRefinement.M31.reduce 7)
    input output rows hop hfixed hair
  · intro index
    rw [hread index, hseven]
    simp [broadcast, S31.Field.toZMod_reduce]
  · exact hinput
  · exact houtput

end S31.Gadgets.Air.GateAddConstSevenFinalization
