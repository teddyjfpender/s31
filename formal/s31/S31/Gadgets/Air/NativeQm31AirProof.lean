import S31.Gadgets.Air.NativeQm31Air

namespace S31.Gadgets.Air.NativeQm31AirProof
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- Every expression in the exact native `qm31_ops` AIR tree agrees with the
nine Lean local residuals, including all four packed multiplication limbs. -/
theorem native_residuals_eq (f : Flags) (x y output : Quad) :
    NativeQm31Air.residuals f x y output =
      Qm31Ops.residuals f x y output := by
  simp [NativeQm31Air.residuals, Qm31Ops.residuals,
    Qm31Ops.weighted, Packed.mul]
  constructor <;> left <;> ring

theorem native_accepts_iff (f : Flags) (x y output : Quad) :
    (∀ r ∈ NativeQm31Air.residuals f x y output, r = 0) ↔
      ∃ op, f = encode op ∧ output = evaluate op x y := by
  rw [native_residuals_eq]
  exact accepts_iff f x y output

end S31.Gadgets.Air.NativeQm31AirProof
