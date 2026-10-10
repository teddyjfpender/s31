import S31.Gadgets.Air.NativeLogUpBatchesProof
import S31.Gadgets.Air.NativeQm31AirProof
import Mathlib.Algebra.Polynomial.Roots

namespace S31.Gadgets.Air.CompositionFold
open Polynomial

variable {K : Type*} [Field K]

/-- The verifier's Horner fold of a fixed ordered constraint list. -/
def fold (coeff : K) (constraints : List K) : K :=
  constraints.foldl (fun value constraint => value * coeff + constraint) 0

/-- The corresponding formal polynomial in the composition coefficient. -/
noncomputable def polynomial (constraints : List K) : K[X] :=
  constraints.foldl (fun value constraint => value * X + C constraint) 0

theorem eval_polynomial (constraints : List K) (coeff : K) :
    eval coeff (polynomial constraints) = fold coeff constraints := by
  have hgeneral (start : K[X]) (xs : List K) :
      eval coeff (xs.foldl (fun value c => value * X + C c) start) =
        xs.foldl (fun value c => value * coeff + c) (eval coeff start) := by
    induction xs generalizing start with
    | nil => rfl
    | cons c rest ih =>
        have hstep : eval coeff (start * X + C c) =
            eval coeff start * coeff + c := by simp
        have h := ih (start * X + C c)
        rw [hstep] at h
        simpa only [List.foldl_cons] using h
  simpa [polynomial, fold] using hgeneral 0 constraints

private theorem step_zero_iff (start : K[X]) (constraint : K) :
    start * X + C constraint = 0 ↔ start = 0 ∧ constraint = 0 := by
  constructor
  · intro h
    have hc : constraint = 0 := by
      have heval := congrArg (eval (0 : K)) h
      simpa using heval
    subst constraint
    simp only [map_zero, add_zero] at h
    exact ⟨(mul_eq_zero.mp h).resolve_right X_ne_zero, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem polynomial_eq_zero_iff (constraints : List K) :
    polynomial constraints = 0 ↔
      ∀ constraint ∈ constraints, constraint = 0 := by
  have hgeneral (start : K[X]) (xs : List K) :
      xs.foldl (fun value c => value * X + C c) start = 0 ↔
        start = 0 ∧ ∀ c ∈ xs, c = 0 := by
    induction xs generalizing start with
    | nil => simp
    | cons c rest ih =>
        rw [List.foldl_cons, ih, step_zero_iff]
        simp only [List.mem_cons, forall_eq_or_imp]
        tauto
  simpa [polynomial] using hgeneral 0 constraints

private theorem foldl_natDegree_le (start : K[X]) (xs : List K) :
    (xs.foldl (fun value c => value * X + C c) start).natDegree ≤
      start.natDegree + xs.length := by
  induction xs generalizing start with
  | nil => simp
  | cons c rest ih =>
      have hstep : (start * X + C c).natDegree ≤ start.natDegree + 1 := by
        rw [natDegree_add_C]
        exact (natDegree_mul_le).trans (by simp)
      simpa only [List.foldl_cons, List.length_cons] using
        (ih (start * X + C c)).trans (by omega)

theorem polynomial_natDegree_lt_length (constraints : List K)
    (hne : constraints ≠ []) :
    (polynomial constraints).natDegree < constraints.length := by
  cases constraints with
  | nil => contradiction
  | cons c rest =>
      simpa [polynomial, List.foldl_cons] using
        (foldl_natDegree_le (C c) rest).trans (by simp)

/-- If at least one committed constraint residual is nonzero, a fixed
constraint list has fewer bad composition coefficients than constraints.
The STARK proof still needs commitment binding and a sound OODS test. -/
theorem bad_coeff_roots_card_lt (constraints : List K)
    (hne : constraints ≠ [])
    (hbad : ∃ c ∈ constraints, c ≠ 0) :
    (polynomial constraints).roots.card < constraints.length := by
  have hpoly : polynomial constraints ≠ 0 := by
    intro hzero
    obtain ⟨c, hc, hnonzero⟩ := hbad
    exact hnonzero ((polynomial_eq_zero_iff constraints).mp hzero c hc)
  exact (card_roots' _).trans_lt
    (polynomial_natDegree_lt_length constraints hne)

/-- A zero folded value can hide nonzero individual residuals at one
composition coefficient; the root bound above is therefore necessary. -/
theorem two_nonzero_residuals_cancel_at_one :
    fold (1 : K) [1, -1] = 0 ∧ (1 : K) ≠ 0 ∧ (-1 : K) ≠ 0 := by
  simp [fold]

end S31.Gadgets.Air.CompositionFold

namespace S31.Gadgets.Air.CompositionFold
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.NativeLogUpBatchesProof
open S31.Gadgets.Air.NativeLogUpBatches

/-- The nine source-extracted arithmetic row residuals followed by the two
source-extracted Gate interaction residuals. Base residuals are embedded in
QM31 for this row-level fold; OODS column base change remains separate. -/
def qm31RowConstraints (flags : Flags) (x y output : Quad)
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure) : List GateSecure :=
  (NativeQm31Air.residuals flags x y output).map liftBase ++
    [pairResidual a b (decode first),
      singleResidual c (decode last - decode prev - decode first +
        claimed / nInstances)]

theorem qm31_row_constraints_length (flags : Flags) (x y output : Quad)
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure) :
    (qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances).length = 11 := by
  simp [qm31RowConstraints, NativeQm31Air.residuals]

/-- The native batch finalizer appends its two constraints in exactly the
same order as the modeled eleven-residual Horner fold. -/
theorem qm31_row_fold_eq_native_tail (flags : Flags) (x y output : Quad)
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure) :
    fold rho (qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances) =
      threeTermWithPrefix
        (fold rho ((NativeQm31Air.residuals flags x y output).map liftBase))
        a b c first prev last rho claimed nInstances := by
  rw [native_three_term_with_prefix_eq]
  simp only [qm31RowConstraints, fold, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  ring

/-- At most ten composition coefficients cancel a fixed nonzero sequence
of these eleven modeled residuals. This is a fixed-value algebraic bound,
not a STARK/PCS soundness claim. -/
theorem qm31_row_bad_coeff_roots_card_le_ten
    (flags : Flags) (x y output : Quad)
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure)
    (hbad : ∃ residual ∈ qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances, residual ≠ 0) :
    (polynomial (qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances)).roots.card ≤ 10 := by
  have hlen := qm31_row_constraints_length flags x y output a b c
    first prev last claimed nInstances
  have hnonempty : qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances ≠ [] := by
    intro h
    simp [h] at hlen
  have hroot := bad_coeff_roots_card_lt
    (qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances) hnonempty hbad
  omega

/-- A forged local arithmetic operation gives a nonzero coefficient in the
source-extracted eleven-residual row sequence, regardless of its Gate terms. -/
theorem forged_qm31_row_bad_coeff_roots_card_le_ten
    (flags : Flags) (x y output : Quad)
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure)
    (hwrong : ¬ ∃ op, flags = encode op ∧ output = evaluate op x y) :
    (polynomial (qm31RowConstraints flags x y output a b c
      first prev last claimed nInstances)).roots.card ≤ 10 := by
  classical
  have hnot : ¬ ∀ residual ∈ NativeQm31Air.residuals flags x y output,
      residual = 0 := by
    intro hall
    exact hwrong ((S31.Gadgets.Air.NativeQm31AirProof.native_accepts_iff
      flags x y output).mp hall)
  push_neg at hnot
  obtain ⟨residual, hmem, hnonzero⟩ := hnot
  apply qm31_row_bad_coeff_roots_card_le_ten
  refine ⟨liftBase residual, ?_, ?_⟩
  · exact List.mem_append.mpr <| Or.inl <|
      List.mem_map.mpr ⟨residual, hmem, rfl⟩
  · exact fun h => hnonzero (liftBase_injective (by simpa using h))

end S31.Gadgets.Air.CompositionFold
