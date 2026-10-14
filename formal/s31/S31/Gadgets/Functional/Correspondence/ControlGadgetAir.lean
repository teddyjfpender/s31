import S31.Gadgets.Air.NativeQm31AirProof

/-!
Local AIR algebra for the pure-field control gadgets emitted by the native
relation compiler. The gate/address roster and constant wires are separate
source-bound premises; proof authentication remains an open PCS/FRI boundary.
-/

namespace S31.Functional.Correspondence.ControlGadgetAir

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

abbrev Wire := Nat → Quad

structure Gate where
  op : S31.Gadgets.Air.Qm31Ops.Op
  lhs : Nat
  rhs : Nat
  out : Nat
  deriving DecidableEq

def AirRows (wire : Wire) (gates : List Gate) : Prop :=
  ∀ gate ∈ gates, ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
    (encode gate.op) (wire gate.lhs) (wire gate.rhs) (wire gate.out), r = 0

theorem gate_sound (wire : Wire) (gates : List Gate)
    (hair : AirRows wire gates) (gate : Gate) (hgate : gate ∈ gates) :
    wire gate.out = evaluate gate.op (wire gate.lhs) (wire gate.rhs) := by
  have accepted : accepts (encode gate.op) (wire gate.lhs) (wire gate.rhs)
      (wire gate.out) := by
    simpa [accepts, ← S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq]
      using hair gate hgate
  exact (accepts_encoded gate.op _ _ _).mp accepted

theorem self_add_zero (anchor difference : Quad)
    (h : anchor = S31.Gadgets.Packed.add anchor difference) :
    difference = S31.Gadgets.Packed.base 0 := by
  apply Quad.ext
  · have ha := congrArg (·.a) h
    simp [S31.Gadgets.Packed.add] at ha
    simpa [S31.Gadgets.Packed.base] using ha
  · have hb := congrArg (·.b) h
    simp [S31.Gadgets.Packed.add] at hb
    simpa [S31.Gadgets.Packed.base] using hb
  · have hc := congrArg (·.c) h
    simp [S31.Gadgets.Packed.add] at hc
    simpa [S31.Gadgets.Packed.base] using hc
  · have hd := congrArg (·.d) h
    simp [S31.Gadgets.Packed.add] at hd
    simpa [S31.Gadgets.Packed.base] using hd

theorem subtract_zero_eq (left right : Quad)
    (h : subtract left right = S31.Gadgets.Packed.base 0) :
    left = right := by
  apply Quad.ext
  · have ha := congrArg (·.a) h
    simpa [subtract, S31.Gadgets.Packed.base] using sub_eq_zero.mp ha
  · have hb := congrArg (·.b) h
    simpa [subtract, S31.Gadgets.Packed.base] using sub_eq_zero.mp hb
  · have hc := congrArg (·.c) h
    simpa [subtract, S31.Gadgets.Packed.base] using sub_eq_zero.mp hc
  · have hd := congrArg (·.d) h
    simpa [subtract, S31.Gadgets.Packed.base] using sub_eq_zero.mp hd

private theorem base_mul_left (x : F) (q : Quad) (i : Fin 4) :
    coord (S31.Gadgets.Packed.mul (S31.Gadgets.Packed.base x) q) i = x * coord q i := by
  fin_cases i <;> simp [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base, coord]

private theorem base_mul_right (q : Quad) (x : F) (i : Fin 4) :
    coord (S31.Gadgets.Packed.mul q (S31.Gadgets.Packed.base x)) i = coord q i * x := by
  rw [S31.Gadgets.Packed.scalar_mul]
  fin_cases i <;> rfl

/-- x*u=1-z and x*z=0 force the *whole* QM31 zero-test output to be the
canonical base-field bit, even when the inverse hint is unrestricted QM31. -/
theorem zero_equations (x : F) (inverse z : Quad)
    (hproduct : S31.Gadgets.Packed.mul (S31.Gadgets.Packed.base x) inverse =
      subtract (S31.Gadgets.Packed.base 1) z)
    (hzero : S31.Gadgets.Packed.mul (S31.Gadgets.Packed.base x) z = S31.Gadgets.Packed.base 0) :
    z = S31.Gadgets.Packed.base (if x = 0 then 1 else 0) := by
  by_cases hx : x = 0
  · subst x
    have hp : subtract (S31.Gadgets.Packed.base 1) z = S31.Gadgets.Packed.base 0 := by
      simpa [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base] using hproduct.symm
    apply Quad.ext
    · have h := congrArg (·.a) hp
      simp [subtract, S31.Gadgets.Packed.base] at h
      simpa using (sub_eq_zero.mp h).symm
    · have h := congrArg (·.b) hp
      simpa [subtract, S31.Gadgets.Packed.base] using h.symm
    · have h := congrArg (·.c) hp
      simpa [subtract, S31.Gadgets.Packed.base] using h.symm
    · have h := congrArg (·.d) hp
      simpa [subtract, S31.Gadgets.Packed.base] using h.symm
  · apply Quad.ext
    · have h := congrArg (·.a) hzero
      simp [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base] at h
      simpa [hx, S31.Gadgets.Packed.base] using h.resolve_left hx
    · have h := congrArg (·.b) hzero
      simp [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base] at h
      simpa [hx, S31.Gadgets.Packed.base] using h.resolve_left hx
    · have h := congrArg (·.c) hzero
      simp [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base] at h
      simpa [hx, S31.Gadgets.Packed.base] using h.resolve_left hx
    · have h := congrArg (·.d) hzero
      simp [S31.Gadgets.Packed.mul, S31.Gadgets.Packed.base] at h
      simpa [hx, S31.Gadgets.Packed.base] using h.resolve_left hx

/-- Exact six arithmetic rows of the scalar zero-test gadget. The two anchor
addresses may carry arbitrary values; their self-add equations force zero. -/
structure ZeroTestRows (wire : Wire) (gates : List Gate)
    (x inverse z product complement difference xz anchor1 anchor2 : Nat) : Prop where
  x_scalar : wire x = S31.Gadgets.Packed.base (wire x).a
  one : wire 1 = S31.Gadgets.Packed.base 1
  product_gate : ⟨.mul, x, inverse, product⟩ ∈ gates
  complement_gate : ⟨.sub, 1, z, complement⟩ ∈ gates
  difference_gate : ⟨.sub, product, complement, difference⟩ ∈ gates
  difference_anchor : ⟨.add, anchor1, difference, anchor1⟩ ∈ gates
  zero_gate : ⟨.mul, x, z, xz⟩ ∈ gates
  zero_anchor : ⟨.add, anchor2, xz, anchor2⟩ ∈ gates

theorem zero_test_air_sound (wire : Wire) (gates : List Gate)
    (x inverse z product complement difference xz anchor1 anchor2 : Nat)
    (rows : ZeroTestRows wire gates x inverse z product complement difference xz anchor1 anchor2)
    (hair : AirRows wire gates) :
    wire z = S31.Gadgets.Packed.base
      (if (wire x).a = 0 then 1 else 0) := by
  have hp : wire product = S31.Gadgets.Packed.mul (wire x) (wire inverse) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.product_gate
  have hc : wire complement = subtract (wire 1) (wire z) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.complement_gate
  have hd : wire difference = subtract (wire product) (wire complement) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.difference_gate
  have ha : wire anchor1 = S31.Gadgets.Packed.add (wire anchor1) (wire difference) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.difference_anchor
  have hz : wire xz = S31.Gadgets.Packed.mul (wire x) (wire z) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.zero_gate
  have hb : wire anchor2 = S31.Gadgets.Packed.add (wire anchor2) (wire xz) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.zero_anchor
  have hdiff : wire difference = S31.Gadgets.Packed.base 0 :=
    self_add_zero _ _ ha
  have hxz : wire xz = S31.Gadgets.Packed.base 0 :=
    self_add_zero _ _ hb
  have hproduct : wire product = wire complement := by
    apply subtract_zero_eq
    rw [← hd]
    exact hdiff
  apply zero_equations (wire x).a (wire inverse) (wire z)
  · rw [← rows.x_scalar, ← hp, hproduct, hc, rows.one]
  · rw [← rows.x_scalar, ← hz]
    exact hxz

/-- The active lane equation of the emitted packed inverse. The native graph
uses pointwise multiplication, subtracts the exact active-one mask, and
forces the difference to zero with a self-add row. -/
theorem inverse_equation (x inverse mask : Quad) (i : Fin 4)
    (hproduct : pointwise x inverse = mask)
    (hmask : coord mask i = 1) :
    coord x i * coord inverse i = 1 := by
  rw [← hmask, ← hproduct, coord_pointwise]

theorem inverse_zero_rejected (x inverse mask : Quad) (i : Fin 4)
    (hproduct : pointwise x inverse = mask) (hmask : coord mask i = 1) :
    coord x i ≠ 0 := by
  intro hx
  have h := inverse_equation x inverse mask i hproduct hmask
  simp [hx] at h

structure InverseRows (wire : Wire) (gates : List Gate)
    (x inverse product difference anchor mask : Nat) : Prop where
  product_gate : ⟨.pointwiseMul, x, inverse, product⟩ ∈ gates
  difference_gate : ⟨.sub, product, mask, difference⟩ ∈ gates
  zero_anchor : ⟨.add, anchor, difference, anchor⟩ ∈ gates

theorem inverse_air_sound (wire : Wire) (gates : List Gate)
    (x inverse product difference anchor mask : Nat) (i : Fin 4)
    (rows : InverseRows wire gates x inverse product difference anchor mask)
    (hair : AirRows wire gates) (hmask : coord (wire mask) i = 1) :
    coord (wire x) i * coord (wire inverse) i = 1 := by
  have hp : wire product = pointwise (wire x) (wire inverse) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.product_gate
  have hd : wire difference = subtract (wire product) (wire mask) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.difference_gate
  have ha : wire anchor = S31.Gadgets.Packed.add (wire anchor) (wire difference) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.zero_anchor
  have hdiff := self_add_zero _ _ ha
  have hproduct : wire product = wire mask := by
    apply subtract_zero_eq
    rw [← hd]
    exact hdiff
  exact inverse_equation _ _ _ i (hp.symm.trans hproduct) hmask

theorem inverse_air_zero_rejected (wire : Wire) (gates : List Gate)
    (x inverse product difference anchor mask : Nat) (i : Fin 4)
    (rows : InverseRows wire gates x inverse product difference anchor mask)
    (hair : AirRows wire gates) (hmask : coord (wire mask) i = 1) :
    coord (wire x) i ≠ 0 := by
  intro hx
  have h := inverse_air_sound wire gates x inverse product difference anchor mask
    i rows hair hmask
  simp [hx] at h

/-- Full QM31 scalar multiplication implements selection on every packed
coordinate once the selector is an already constrained base-field bit. -/
theorem select_equation (bit : F) (falseBranch trueBranch output : Quad)
    (hbit : bit = 0 ∨ bit = 1)
    (houtput : output =
      S31.Gadgets.Packed.add (S31.Gadgets.Packed.mul falseBranch (S31.Gadgets.Packed.base (1 - bit)))
        (S31.Gadgets.Packed.mul trueBranch (S31.Gadgets.Packed.base bit))) :
    output = if bit = 0 then falseBranch else trueBranch := by
  rcases hbit with hb | hb
  · subst bit
    simp [houtput, S31.Gadgets.Packed.scalar_mul, S31.Gadgets.Packed.add]
  · subst bit
    simp [houtput, S31.Gadgets.Packed.scalar_mul, S31.Gadgets.Packed.add]

structure SelectRows (wire : Wire) (gates : List Gate)
    (bit falseBranch trueBranch complement left right output : Nat) : Prop where
  one : wire 1 = S31.Gadgets.Packed.base 1
  complement_gate : ⟨.sub, 1, bit, complement⟩ ∈ gates
  left_gate : ⟨.mul, falseBranch, complement, left⟩ ∈ gates
  right_gate : ⟨.mul, trueBranch, bit, right⟩ ∈ gates
  output_gate : ⟨.add, left, right, output⟩ ∈ gates

theorem select_air_sound (wire : Wire) (gates : List Gate)
    (bit falseBranch trueBranch complement left right output : Nat)
    (b : F)
    (rows : SelectRows wire gates bit falseBranch trueBranch complement left right output)
    (hair : AirRows wire gates)
    (hbit : wire bit = S31.Gadgets.Packed.base b)
    (hbinary : b = 0 ∨ b = 1) :
    wire output = if b = 0 then wire falseBranch else wire trueBranch := by
  have hc : wire complement = subtract (wire 1) (wire bit) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.complement_gate
  have hl : wire left = S31.Gadgets.Packed.mul (wire falseBranch) (wire complement) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.left_gate
  have hr : wire right = S31.Gadgets.Packed.mul (wire trueBranch) (wire bit) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.right_gate
  have ho : wire output = S31.Gadgets.Packed.add (wire left) (wire right) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.output_gate
  have hcomp : wire complement = S31.Gadgets.Packed.base (1 - b) := by
    rw [hc, rows.one, hbit]
    ext <;> simp [subtract, S31.Gadgets.Packed.base]
  apply select_equation b (wire falseBranch) (wire trueBranch) (wire output) hbinary
  rw [ho, hl, hr, hcomp, hbit]

/-- The source-order zero-test, selection, and packed inversion pipeline has
the intended branch and rejects zero in every active selected lane. No witness
values are fixed here; the result holds for every locally accepted AIR row
assignment with this exact gate ownership. -/
theorem control_pipeline_air_sound (wire : Wire) (gates : List Gate)
    (x hint z zp zc zd zx za zb : Nat)
    (falseBranch trueBranch selected sc sl sr : Nat)
    (inverse ip idiff ia mask : Nat)
    (zeroRows : ZeroTestRows wire gates x hint z zp zc zd zx za zb)
    (selectRows : SelectRows wire gates z falseBranch trueBranch sc sl sr selected)
    (inverseRows : InverseRows wire gates selected inverse ip idiff ia mask)
    (hair : AirRows wire gates)
    (hmask : ∀ i : Fin 4, coord (wire mask) i = 1) :
    let bit := if (wire x).a = 0 then (1 : F) else 0
    wire selected = (if bit = 0 then wire falseBranch else wire trueBranch) ∧
      (∀ i : Fin 4,
        coord (if bit = 0 then wire falseBranch else wire trueBranch) i *
          coord (wire inverse) i = 1) := by
  let bit : F := if (wire x).a = 0 then 1 else 0
  have hz : wire z = S31.Gadgets.Packed.base bit :=
    zero_test_air_sound wire gates x hint z zp zc zd zx za zb zeroRows hair
  have hbinary : bit = 0 ∨ bit = 1 := by
    unfold bit
    split_ifs <;> simp
  have hs := select_air_sound wire gates z falseBranch trueBranch sc sl sr
    selected bit selectRows hair hz hbinary
  refine ⟨hs, ?_⟩
  intro i
  have hi := inverse_air_sound wire gates selected inverse ip idiff ia mask
    i inverseRows hair (hmask i)
  simpa [bit, hs] using hi

end S31.Functional.Correspondence.ControlGadgetAir
