import S31.Gadgets.Air.BitRows

namespace S31.Gadgets.Air.ZeroRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

theorem toQM_sub (x y : Quad) :
    QuadField.toQM (subtract x y) =
      QuadField.toQM x - QuadField.toQM y := by
  ext <;> rfl

/-- The exact arithmetic row schedule of `isZeroWord`, with the two
`assertZeroArithmetic` self-loops modeled by `BitRows.acceptsZero`. -/
def acceptsZeroTest (input indicator : Quad) : Prop :=
  ∃ inverse product complement difference productZ : Quad,
    accepts (encode .mul) input inverse product ∧
    accepts (encode .sub) (base 1) indicator complement ∧
    accepts (encode .sub) product complement difference ∧
    BitRows.acceptsZero difference ∧
    accepts (encode .mul) input indicator productZ ∧
    BitRows.acceptsZero productZ

theorem acceptsZeroTest_sound (input indicator : Quad)
    (h : acceptsZeroTest input indicator) :
    indicator = if input = base 0 then base 1 else base 0 := by
  obtain ⟨inverse, product, complement, difference, productZ,
    hmul, hcomp, hdiff, hzeroDiff, hmulZ, hzeroZ⟩ := h
  have hmul' := (accepts_encoded .mul input inverse product).mp hmul
  have hcomp' := (accepts_encoded .sub (base 1) indicator complement).mp hcomp
  have hdiff' := (accepts_encoded .sub product complement difference).mp hdiff
  have hzeroDiff' := (BitRows.acceptsZero_iff difference).mp hzeroDiff
  have hmulZ' := (accepts_encoded .mul input indicator productZ).mp hmulZ
  have hzeroZ' := (BitRows.acceptsZero_iff productZ).mp hzeroZ
  have hproduct : product = complement := by
    apply QuadField.toQM_injective
    have h := congrArg QuadField.toQM hzeroDiff'
    rw [hdiff'] at h
    simp only [evaluate, toQM_sub, QuadField.toQM_base_zero] at h
    exact sub_eq_zero.mp h
  have hz : QuadField.toQM input * QuadField.toQM indicator = 0 := by
    have h := congrArg QuadField.toQM hzeroZ'
    rw [hmulZ'] at h
    simp only [evaluate, QuadField.toQM_mul,
      QuadField.toQM_base_zero] at h
    exact h
  have hp : QuadField.toQM input * QuadField.toQM inverse =
      1 - QuadField.toQM indicator := by
    have h := congrArg QuadField.toQM hproduct
    rw [hmul', hcomp'] at h
    simp only [evaluate, QuadField.toQM_mul,
      toQM_sub, QuadField.toQM_base_one] at h
    exact h
  have hresult := S31.Gadgets.is_zero_sound
    (QuadField.toQM input) (QuadField.toQM indicator)
    (QuadField.toQM inverse) ⟨hz, hp⟩
  by_cases hinput : input = base 0
  · have heq : QuadField.toQM input = 0 := by
      simp [hinput, QuadField.toQM_base_zero]
    rw [if_pos heq] at hresult
    simp only [if_pos hinput]
    apply QuadField.toQM_injective
    simpa [QuadField.toQM_base_one] using hresult
  · have hne : QuadField.toQM input ≠ 0 := by
      intro hinput'
      exact hinput (QuadField.toQM_injective
        (by simpa [QuadField.toQM_base_zero] using hinput'))
    rw [if_neg hne] at hresult
    simp only [if_neg hinput]
    apply QuadField.toQM_injective
    simpa [QuadField.toQM_base_zero] using hresult

def fromQM (x : QuadField.QM) : Quad :=
  ⟨x.re.re, x.re.im, x.im.re, x.im.im⟩

theorem toQM_fromQM (x : QuadField.QM) :
    QuadField.toQM (fromQM x) = x := by
  ext <;> rfl

/-- Honest inverse and indicator witnesses exist for every four-coordinate
input, including zero. -/
theorem acceptsZeroTest_complete (input indicator : Quad)
    (hindicator : indicator = if input = base 0 then base 1 else base 0) :
    acceptsZeroTest input indicator := by
  let inverse := fromQM
    (if QuadField.toQM input = 0 then 0 else (QuadField.toQM input)⁻¹)
  have hindicatorQM : QuadField.toQM indicator =
      if QuadField.toQM input = 0 then 1 else 0 := by
    rw [hindicator]
    by_cases hzero : input = base 0
    · simp [hzero, QuadField.toQM_base_zero,
        QuadField.toQM_base_one]
    · have hnonzero : QuadField.toQM input ≠ 0 := by
        intro hz
        exact hzero (QuadField.toQM_injective
          (by simpa [QuadField.toQM_base_zero] using hz))
      simp [hzero, hnonzero, QuadField.toQM_base_zero]
  have hinverseQM : QuadField.toQM inverse =
      if QuadField.toQM input = 0 then 0 else
        (QuadField.toQM input)⁻¹ := toQM_fromQM _
  have hconstraint : S31.Gadgets.zeroConstraint
      (QuadField.toQM input) (QuadField.toQM indicator)
      (QuadField.toQM inverse) := by
    rw [hindicatorQM, hinverseQM]
    exact S31.Gadgets.is_zero_complete (QuadField.toQM input)
  let product := evaluate .mul input inverse
  let complement := evaluate .sub (base 1) indicator
  let difference := evaluate .sub product complement
  let productZ := evaluate .mul input indicator
  have hzeroDifference : difference = base 0 := by
    apply QuadField.toQM_injective
    have hp : QuadField.toQM product =
        QuadField.toQM input * QuadField.toQM inverse := by
      simp [product, evaluate, QuadField.toQM_mul]
    have hc : QuadField.toQM complement =
        1 - QuadField.toQM indicator := by
      simp [complement, evaluate, toQM_sub,
        QuadField.toQM_base_one]
    simp only [difference, evaluate, toQM_sub,
      hp, hc, QuadField.toQM_base_zero]
    exact sub_eq_zero.mpr hconstraint.2
  have hzeroProductZ : productZ = base 0 := by
    apply QuadField.toQM_injective
    simpa [productZ, evaluate, QuadField.toQM_mul,
      QuadField.toQM_base_zero] using hconstraint.1
  exact ⟨inverse, product, complement, difference, productZ,
    honest_row _ _ _, honest_row _ _ _, honest_row _ _ _,
    (BitRows.acceptsZero_iff _).mpr hzeroDifference,
    honest_row _ _ _, (BitRows.acceptsZero_iff _).mpr hzeroProductZ⟩

theorem acceptsZeroTest_iff (input indicator : Quad) :
    acceptsZeroTest input indicator ↔
      indicator = if input = base 0 then base 1 else base 0 :=
  ⟨acceptsZeroTest_sound input indicator,
   acceptsZeroTest_complete input indicator⟩

/-- The source-visible M31 zero test is the restriction of the universal
QM31 row theorem to canonical scalar input/output bindings. -/
theorem base_zero_test_iff (value claimed : S31.M31) :
    acceptsZeroTest (base (S31.Field.toZMod value))
      (base (S31.Field.toZMod claimed)) ↔
      claimed = if value = 0 then 1 else 0 := by
  rw [acceptsZeroTest_iff]
  have hbase (x y : F) : base x = base y ↔ x = y := by
    constructor
    · intro h
      exact congrArg Quad.a h
    · rintro rfl
      rfl
  have hzero : base (S31.Field.toZMod value) = base 0 ↔ value = 0 := by
    rw [hbase]
    constructor
    · intro h
      exact S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_zero] using h)
    · rintro rfl
      exact S31.Field.toZMod_zero
  simp only [hzero]
  by_cases hv : value = 0
  · simp only [if_pos hv, hbase]
    constructor
    · intro h
      exact S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_one] using h)
    · rintro rfl
      exact S31.Field.toZMod_one
  · simp only [if_neg hv, hbase]
    constructor
    · intro h
      exact S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_zero] using h)
    · rintro rfl
      exact S31.Field.toZMod_zero

def normalizedZeroNode : S31.Node :=
  { name := "out", op := .is_zero, lhs := some "input" }

def normalizedZeroEnv (value : S31.M31) : S31.Env :=
  [("input", ⟨.m31, [value]⟩)]

theorem normalizedZeroNode_shape (value : S31.M31) :
    S31.inferNode ((normalizedZeroEnv value).map
      (fun (name, input) => (name, input.shape))) normalizedZeroNode =
      .ok ⟨.m31, 1⟩ := by
  have hkind : (S31.Kind.m31 == S31.Kind.m31) = true := rfl
  simp [normalizedZeroNode, normalizedZeroEnv, S31.inferNode,
    S31.Node.metadataValid, S31.Node.fields, S31.shapeOperand,
    S31.expectShape, S31.lookup, S31.Value.shape, S31.need,
    S31.require, Bind.bind, Except.bind, Except.map, hkind]
  rfl

theorem normalizedZeroNode_eval (value : S31.M31) :
    S31.evaluateNode (normalizedZeroEnv value) normalizedZeroNode =
      .ok ⟨.m31, [if value = 0 then 1 else 0]⟩ := by
  unfold S31.evaluateNode
  rw [normalizedZeroNode_shape]
  simp [normalizedZeroNode, normalizedZeroEnv, S31.valueOperand,
    S31.lookup, S31.Value.shape, S31.Value.valid,
    S31.require, Bind.bind, Except.bind]
  by_cases hz : value = 0
  · subst value
    decide
  · have hval : value.val ≠ 0 := by
      intro hv
      exact hz (RiscvRefinement.M31.ext (by simpa using hv))
    simp [hz, hval, S31.bitValue]
    decide

theorem base_zero_test_iff_evaluateNode
    (value claimed : S31.M31) :
    acceptsZeroTest (base (S31.Field.toZMod value))
      (base (S31.Field.toZMod claimed)) ↔
      S31.evaluateNode (normalizedZeroEnv value) normalizedZeroNode =
        .ok ⟨.m31, [claimed]⟩ := by
  rw [base_zero_test_iff, normalizedZeroNode_eval]
  constructor
  · intro h
    simp [h]
  · intro h
    have hw : [if value = 0 then 1 else 0] = [claimed] :=
      congrArg S31.Value.words (Except.ok.inj h)
    exact (List.cons.inj hw).1.symm

theorem zero_input_forged_indicator_rejected :
    ¬ acceptsZeroTest (base 0) (base 0) := by
  intro h
  have hresult := acceptsZeroTest_sound (base 0) (base 0) h
  exact (by decide : (base 0 : Quad) ≠ base 1)
    (by simpa using hresult)

theorem seven_input_honest_indicator :
    acceptsZeroTest (base 7) (base 0) := by
  apply acceptsZeroTest_complete
  have hnonzero : (base 7 : Quad) ≠ base 0 := by decide
  simp [hnonzero]

end S31.Gadgets.Air.ZeroRows
