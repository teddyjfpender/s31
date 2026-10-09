import S31.Gadgets.Packed
import S31.Gadgets.Functional.ArithmeticNodes

/-!
The nine local polynomial constraints in the production circuit AIR's
`evaluateQm31Ops`. The four flags are preprocessed columns and the three
packed operands are trace columns. The model does not include the Gate lookup
relation, address columns, multiplicities, or the STARK proof protocol.
-/

namespace S31.Gadgets.Air.Qm31Ops

open S31.Gadgets.Packed

structure Flags where
  add : F
  sub : F
  mul : F
  pointwiseMul : F
deriving DecidableEq

inductive Op where
  | add | sub | mul | pointwiseMul
deriving DecidableEq, Repr

def encode : Op → Flags
  | .add => ⟨1, 0, 0, 0⟩
  | .sub => ⟨0, 1, 0, 0⟩
  | .mul => ⟨0, 0, 1, 0⟩
  | .pointwiseMul => ⟨0, 0, 0, 1⟩

def subtract (x y : Quad) : Quad :=
  ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩

def evaluate : Op → Quad → Quad → Quad
  | .add, x, y => Packed.add x y
  | .sub, x, y => subtract x y
  | .mul, x, y => Packed.mul x y
  | .pointwiseMul, x, y => Packed.pointwise x y

/-- The four output expressions match `linearTerms(mulTerm(k), k)` in Zig. -/
def weighted (f : Flags) (x y : Quad) : Quad :=
  let product := Packed.mul x y
  ⟨product.a * f.mul + (x.a + y.a) * f.add + (x.a - y.a) * f.sub + (x.a * y.a) * f.pointwiseMul,
   product.b * f.mul + (x.b + y.b) * f.add + (x.b - y.b) * f.sub + (x.b * y.b) * f.pointwiseMul,
   product.c * f.mul + (x.c + y.c) * f.add + (x.c - y.c) * f.sub + (x.c * y.c) * f.pointwiseMul,
   product.d * f.mul + (x.d + y.d) * f.add + (x.d - y.d) * f.sub + (x.d * y.d) * f.pointwiseMul⟩

/-- Positions 0–8 are one-hot, four bit constraints, then four output limbs. -/
def residuals (f : Flags) (x y output : Quad) : List F :=
  [f.add + f.sub + f.mul + f.pointwiseMul - 1,
   f.add * (f.add - 1),
   f.sub * (f.sub - 1),
   f.mul * (f.mul - 1),
   f.pointwiseMul * (f.pointwiseMul - 1),
   output.a - (weighted f x y).a,
   output.b - (weighted f x y).b,
   output.c - (weighted f x y).c,
   output.d - (weighted f x y).d]

def accepts (f : Flags) (x y output : Quad) : Prop :=
  ∀ r ∈ residuals f x y output, r = 0

theorem residuals_length (f : Flags) (x y output : Quad) :
    (residuals f x y output).length = 9 := rfl

private theorem flags_bit_cases (f : Flags)
    (hone : f.add + f.sub + f.mul + f.pointwiseMul - 1 = 0)
    (ha : f.add * (f.add - 1) = 0)
    (hs : f.sub * (f.sub - 1) = 0)
    (hm : f.mul * (f.mul - 1) = 0)
    (hp : f.pointwiseMul * (f.pointwiseMul - 1) = 0) :
    ∃ op, f = encode op := by
  have ha' := (bit_sound_complete f.add).mp (by unfold bit; linear_combination ha)
  have hs' := (bit_sound_complete f.sub).mp (by unfold bit; linear_combination hs)
  have hm' := (bit_sound_complete f.mul).mp (by unfold bit; linear_combination hm)
  have hp' := (bit_sound_complete f.pointwiseMul).mp (by unfold bit; linear_combination hp)
  rcases ha' with ha' | ha' <;> rcases hs' with hs' | hs' <;>
    rcases hm' with hm' | hm' <;> rcases hp' with hp' | hp' <;>
    simp_all [encode]
  all_goals
    have htwo : (1 + 1 : F) ≠ 0 := by decide
    have hthree : (1 + 1 + 1 : F) ≠ 0 := by decide
    simp_all
  case inl.inl.inl.inr =>
    exact ⟨.pointwiseMul, by cases f; simp_all⟩
  case inl.inl.inr.inl =>
    exact ⟨.mul, by cases f; simp_all⟩
  case inl.inr.inl.inl =>
    exact ⟨.sub, by cases f; simp_all⟩
  case inr.inl.inl.inl =>
    exact ⟨.add, by cases f; simp_all⟩

theorem weighted_encode (op : Op) (x y : Quad) :
    weighted (encode op) x y = evaluate op x y := by
  cases op <;> ext <;> simp [weighted, encode, evaluate, Packed.add,
    subtract, Packed.mul, Packed.pointwise]

theorem accepts_iff (f : Flags) (x y output : Quad) :
    accepts f x y output ↔
      ∃ op, f = encode op ∧ output = evaluate op x y := by
  constructor
  · intro h
    have hrows := (by simpa [accepts, residuals] using h :
      f.add + f.sub + f.mul + f.pointwiseMul - 1 = 0 ∧
      f.add * (f.add - 1) = 0 ∧
      f.sub * (f.sub - 1) = 0 ∧
      f.mul * (f.mul - 1) = 0 ∧
      f.pointwiseMul * (f.pointwiseMul - 1) = 0 ∧
      output.a - (weighted f x y).a = 0 ∧
      output.b - (weighted f x y).b = 0 ∧
      output.c - (weighted f x y).c = 0 ∧
      output.d - (weighted f x y).d = 0)
    obtain ⟨op, rfl⟩ := flags_bit_cases f hrows.1 hrows.2.1 hrows.2.2.1
      hrows.2.2.2.1 hrows.2.2.2.2.1
    refine ⟨op, rfl, ?_⟩
    rw [← weighted_encode]
    exact Quad.ext (sub_eq_zero.mp hrows.2.2.2.2.2.1)
      (sub_eq_zero.mp hrows.2.2.2.2.2.2.1)
      (sub_eq_zero.mp hrows.2.2.2.2.2.2.2.1)
      (sub_eq_zero.mp hrows.2.2.2.2.2.2.2.2)
  · rintro ⟨op, rfl, rfl⟩
    cases op <;> simp [accepts, residuals, weighted, encode, evaluate,
      Packed.add, Packed.mul, Packed.pointwise, subtract]

theorem accepts_encoded (op : Op) (x y output : Quad) :
    accepts (encode op) x y output ↔ output = evaluate op x y := by
  rw [accepts_iff]
  constructor
  · rintro ⟨other, heq, hout⟩
    have : other = op := by cases other <;> cases op <;> simp_all [encode]
    simpa [this] using hout
  · intro h; exact ⟨op, rfl, h⟩

theorem honest_row (op : Op) (x y : Quad) :
    accepts (encode op) x y (evaluate op x y) :=
  (accepts_encoded op x y _).mpr rfl

theorem output_unique (f : Flags) (x y left right : Quad)
    (hl : accepts f x y left) (hr : accepts f x y right) :
    left = right := by
  obtain ⟨op, hf, hout⟩ := (accepts_iff f x y left).mp hl
  subst f
  rw [(accepts_encoded op x y right).mp hr, hout]

theorem all_flags_zero_rejected (x y output : Quad) :
    ¬ accepts ⟨0, 0, 0, 0⟩ x y output := by
  intro h
  obtain ⟨op, hop, _⟩ := (accepts_iff _ _ _ _).mp h
  cases op <;> simp [encode] at hop

theorem two_flags_rejected (x y output : Quad) :
    ¬ accepts ⟨1, 1, 0, 0⟩ x y output := by
  intro h
  obtain ⟨op, hop, _⟩ := (accepts_iff _ _ _ _).mp h
  cases op <;> simp [encode] at hop

/-- Pack exactly the four M31 lanes in one S31 SIMD wire. -/
def packM31 (lanes : Fin 4 → S31.M31) : Quad :=
  ⟨S31.Field.toZMod (lanes ⟨0, by decide⟩),
   S31.Field.toZMod (lanes ⟨1, by decide⟩),
   S31.Field.toZMod (lanes ⟨2, by decide⟩),
   S31.Field.toZMod (lanes ⟨3, by decide⟩)⟩

theorem coord_packM31 (lanes : Fin 4 → S31.M31) (i : Fin 4) :
    coord (packM31 lanes) i = S31.Field.toZMod (lanes i) := by
  fin_cases i <;> rfl

/-- `simd.mul` selects the pointwise opcode; it never invokes QM31 extension
multiplication for S31 array multiplication. -/
def s31Op (multiply : Bool) : Op :=
  if multiply then .pointwiseMul else .add

theorem s31Op_coord (multiply : Bool) (a b : Fin 4 → S31.M31)
    (i : Fin 4) :
    coord (evaluate (s31Op multiply) (packM31 a) (packM31 b)) i =
      S31.Field.toZMod
        (if multiply then a i * b i else a i + b i) := by
  cases multiply <;> fin_cases i <;>
    simp [s31Op, evaluate, packM31, coord, Packed.add,
      Packed.pointwise, S31.Field.toZMod_add, S31.Field.toZMod_mul]

/-- Local AIR row acceptance is equivalent to the four S31 source M31 lane
results, for every possible output witness. -/
theorem s31_row_iff (multiply : Bool) (a b : Fin 4 → S31.M31)
    (output : Quad) :
    accepts (encode (s31Op multiply)) (packM31 a) (packM31 b) output ↔
      ∀ i : Fin 4, coord output i = S31.Field.toZMod
        (if multiply then a i * b i else a i + b i) := by
  rw [accepts_encoded]
  constructor
  · intro h i
    rw [h]
    exact s31Op_coord multiply a b i
  · intro h
    apply Quad.ext
    · simpa [coord] using (h ⟨0, by decide⟩).trans
        (s31Op_coord multiply a b ⟨0, by decide⟩).symm
    · simpa [coord] using (h ⟨1, by decide⟩).trans
        (s31Op_coord multiply a b ⟨1, by decide⟩).symm
    · simpa [coord] using (h ⟨2, by decide⟩).trans
        (s31Op_coord multiply a b ⟨2, by decide⟩).symm
    · simpa [coord] using (h ⟨3, by decide⟩).trans
        (s31Op_coord multiply a b ⟨3, by decide⟩).symm

/-- For one full four-lane S31 array chunk, the actual normalized relation
evaluator accepts exactly the M31 outputs accepted by this AIR row model. -/
theorem row_iff_normalized_node (multiply : Bool)
    (a b output : Fin 4 → S31.M31) :
    accepts (encode (s31Op multiply)) (packM31 a) (packM31 b)
      (packM31 output) ↔
    S31.evaluateNode (S31.Functional.arithmeticEnv a b)
      (S31.Functional.arithmeticNode multiply) =
        .ok ⟨.m31, List.ofFn output⟩ := by
  rw [s31_row_iff, S31.Functional.arithmeticNode_eval]
  constructor
  · intro h
    have heq : (fun i : Fin 4 => if multiply then a i * b i else a i + b i) =
        output := by
      funext i
      apply S31.Field.toZMod_injective
      exact (by simpa [coord_packM31] using (h i).symm)
    rw [heq]
  · intro h
    have hlist : List.ofFn
        (fun i : Fin 4 => if multiply then a i * b i else a i + b i) =
        List.ofFn output := by
      injection h with hvalue
      exact congrArg S31.Value.words hvalue
    have heq := List.ofFn_injective hlist
    intro i
    rw [coord_packM31, ← congrFun heq i]

end S31.Gadgets.Air.Qm31Ops
