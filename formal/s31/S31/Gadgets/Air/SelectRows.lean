import S31.Gadgets.Air.SimdChunks
import S31.Gadgets.Air.QuadField
import S31.Gadgets.Functional.ArrayConditional

/-!
The direct S31 compiler's `selectByBit` computes `1 - bit`, multiplies the
false and true packed words by those M31 scalars, then adds the results.
These are local QM31 operation rows. The bit premise must be discharged by
the selector producer or its Boolean constraint; Gate lookup and compiler
emission are separate obligations.
-/

namespace S31.Gadgets.Air.SelectRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- Four operation rows in `selectByBit`, with all intermediate trace values
existentially quantified rather than assumed honest. -/
def acceptsSelect (selector : S31.M31)
    (onFalse onTrue output : Quad) : Prop :=
  ∃ complement falsePart truePart : Quad,
    accepts (encode .sub) (base 1)
      (base (S31.Field.toZMod selector)) complement ∧
    accepts (encode .mul) onFalse complement falsePart ∧
    accepts (encode .mul) onTrue
      (base (S31.Field.toZMod selector)) truePart ∧
    accepts (encode .add) falsePart truePart output

/-- The direct selector self-product row forces any four-coordinate QM31
witness to be canonical zero or one. The tower-field argument uses the
nonsquareness of minus one and five in M31. -/
theorem untrusted_selector_self_product_iff (selector : Quad) :
    accepts (encode .mul) selector selector selector ↔
      selector = base 0 ∨ selector = base 1 := by
  rw [accepts_encoded]
  constructor
  · exact fun h => (QuadField.self_product_iff selector).mp h.symm
  · exact fun h => ((QuadField.self_product_iff selector).mpr h).symm

/-- Binding the base coordinate of an arbitrary selector witness to a source
M31 value, then imposing the self-product row, gives the canonical QM31
encoding of that source bit. No representation premise is assumed. -/
theorem untrusted_selector_bound_iff (selector : S31.M31)
    (wire : Quad) (hcoord : wire.a = S31.Field.toZMod selector) :
    accepts (encode .mul) wire wire wire ↔
      wire = base (S31.Field.toZMod selector) ∧
        (selector = 0 ∨ selector = 1) := by
  rw [untrusted_selector_self_product_iff]
  constructor
  · rintro (hzero | hone)
    · have hz : selector = 0 :=
        S31.Field.toZMod_injective
          (by simpa [hzero, base, S31.Field.toZMod_zero] using hcoord.symm)
      subst selector
      exact ⟨by simpa [S31.Field.toZMod_zero] using hzero,
        Or.inl rfl⟩
    · have ho : selector = 1 :=
        S31.Field.toZMod_injective
          (by simpa [hone, base, S31.Field.toZMod_one] using hcoord.symm)
      subst selector
      exact ⟨by simpa [S31.Field.toZMod_one] using hone,
        Or.inr rfl⟩
  · rintro ⟨hwire, hbit⟩
    rw [hwire]
    rcases hbit with hzero | hone
    · subst selector
      simp [S31.Field.toZMod_zero]
    · subst selector
      simp [S31.Field.toZMod_one]

/-- For a base-field encoded source selector, the same row is equivalent to
Booleanity of the source M31 value. -/
theorem base_selector_self_product_iff (selector : S31.M31) :
    accepts (encode .mul)
      (base (S31.Field.toZMod selector))
      (base (S31.Field.toZMod selector))
      (base (S31.Field.toZMod selector)) ↔
    selector = 0 ∨ selector = 1 := by
  rw [accepts_encoded]
  constructor
  · intro h
    have ha := congrArg Quad.a h
    have hbit : S31.Gadgets.bit (S31.Field.toZMod selector) := by
      unfold S31.Gadgets.bit
      simpa [evaluate, base, Packed.mul] using ha.symm
    rcases (S31.Gadgets.bit_sound_complete _).mp hbit with hz | ho
    · left
      exact S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_zero] using hz)
    · right
      exact S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_one] using ho)
  · rintro (rfl | rfl) <;>
      simp [evaluate, base, Packed.mul,
        S31.Field.toZMod_zero, S31.Field.toZMod_one]

/-- If the selector is a constrained bit, every satisfying assignment of
the four row outputs gives exactly the chosen packed word. Both bit cases
also have honest row witnesses. -/
theorem acceptsSelect_iff (selector : S31.M31)
    (onFalse onTrue output : Quad)
    (hbit : selector = 0 ∨ selector = 1) :
    acceptsSelect selector onFalse onTrue output ↔
      output = if selector = 0 then onFalse else onTrue := by
  constructor
  · rintro ⟨complement, falsePart, truePart, hc, hf, ht, ho⟩
    have hc' := (accepts_encoded .sub (base 1)
      (base (S31.Field.toZMod selector)) complement).mp hc
    have hf' := (accepts_encoded .mul onFalse complement falsePart).mp hf
    have ht' := (accepts_encoded .mul onTrue
      (base (S31.Field.toZMod selector)) truePart).mp ht
    have ho' := (accepts_encoded .add falsePart truePart output).mp ho
    rcases hbit with hzero | hone
    · subst selector
      simp [S31.Field.toZMod_zero, evaluate, subtract, base,
        Packed.mul, Packed.add] at hc' hf' ht' ho' ⊢
      simpa [hc', hf', ht'] using ho'
    · subst selector
      simp [S31.Field.toZMod_one, evaluate, subtract, base,
        Packed.mul, Packed.add] at hc' hf' ht' ho' ⊢
      simpa [hc', hf', ht'] using ho'
  · intro hout
    let complement := evaluate .sub (base 1)
      (base (S31.Field.toZMod selector))
    let falsePart := evaluate .mul onFalse complement
    let truePart := evaluate .mul onTrue
      (base (S31.Field.toZMod selector))
    refine ⟨complement, falsePart, truePart,
      honest_row _ _ _, honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (accepts_encoded .add falsePart truePart output).mpr
    rw [hout]
    rcases hbit with hzero | hone
    · subst selector
      simp [complement, falsePart, truePart, S31.Field.toZMod_zero,
        evaluate, subtract, base, Packed.mul, Packed.add]
    · subst selector
      have hone : (1 : S31.M31) ≠ 0 := by decide
      simp [complement, falsePart, truePart, S31.Field.toZMod_one,
        evaluate, subtract, base, Packed.mul, Packed.add, hone]

/-- The four-row selection model agrees with all four native M31 lanes,
for arbitrary intermediate row witnesses and either Boolean selector. -/
theorem acceptsSelect_lanes_iff (selector : S31.M31)
    (onFalse onTrue claimed : Fin 4 → S31.M31)
    (hbit : selector = 0 ∨ selector = 1) :
    acceptsSelect selector (packM31 onFalse) (packM31 onTrue)
      (packM31 claimed) ↔
    ∀ i : Fin 4,
      claimed i = if selector = 0 then onFalse i else onTrue i := by
  rw [acceptsSelect_iff selector _ _ _ hbit]
  constructor
  · intro h i
    have hi := congrArg (fun q => coord q i) h
    by_cases hz : selector = 0
    · simpa [hz, coord_packM31] using
        S31.Field.toZMod_injective (by simpa [hz, coord_packM31] using hi)
    · simpa [hz, coord_packM31] using
        S31.Field.toZMod_injective (by simpa [hz, coord_packM31] using hi)
  · intro h
    by_cases hz : selector = 0
    · simp only [if_pos hz]
      congr 1
      funext i
      simpa [hz] using h i
    · simp only [if_neg hz]
      congr 1
      funext i
      simpa [hz] using h i

/-- All packed rows for a source array selection. A short final row has
arbitrary input padding and existential intermediate/output trace values. -/
def packedSelectRows {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) : Prop :=
  ∀ block : Fin ((n + 3) / 4), ∃ output : Quad,
    acceptsSelect selector
      (packM31 (SimdChunks.chunk4 onFalse block.val (tailFalse block.val)))
      (packM31 (SimdChunks.chunk4 onTrue block.val (tailTrue block.val))) output ∧
    ∀ (i : Fin 4) (hi : block.val * 4 + i.val < n),
      coord output i =
        S31.Field.toZMod (claimed ⟨block.val * 4 + i.val, hi⟩)

/-- Match the compiler's topology: one shared complement row, then two
scalar product rows and one addition row per packed word. -/
def packedSelectRowsShared {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) : Prop :=
  ∃ complement : Quad,
    accepts (encode .sub) (base 1)
      (base (S31.Field.toZMod selector)) complement ∧
    ∀ block : Fin ((n + 3) / 4),
      ∃ falsePart truePart output : Quad,
        accepts (encode .mul)
          (packM31 (SimdChunks.chunk4 onFalse block.val
            (tailFalse block.val))) complement falsePart ∧
        accepts (encode .mul)
          (packM31 (SimdChunks.chunk4 onTrue block.val
            (tailTrue block.val)))
          (base (S31.Field.toZMod selector)) truePart ∧
        accepts (encode .add) falsePart truePart output ∧
        ∀ (i : Fin 4) (hi : block.val * 4 + i.val < n),
          coord output i =
            S31.Field.toZMod (claimed ⟨block.val * 4 + i.val, hi⟩)

/-- The per-word local relation has exactly the same accepted claims as the
shared-complement topology. Output uniqueness of the subtraction row makes
all local complement witnesses equal to the one shared producer. -/
theorem packedSelectRowsShared_iff {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    packedSelectRowsShared selector onFalse onTrue claimed
      tailFalse tailTrue ↔
    packedSelectRows selector onFalse onTrue claimed
      tailFalse tailTrue := by
  constructor
  · rintro ⟨complement, hcomp, rows⟩ block
    obtain ⟨falsePart, truePart, output, hf, ht, ho, hclaim⟩ := rows block
    exact ⟨output, ⟨complement, falsePart, truePart,
      hcomp, hf, ht, ho⟩, hclaim⟩
  · intro rows
    let complement := evaluate .sub (base 1)
      (base (S31.Field.toZMod selector))
    have hcomp : accepts (encode .sub) (base 1)
        (base (S31.Field.toZMod selector)) complement := honest_row _ _ _
    refine ⟨complement, hcomp, ?_⟩
    intro block
    obtain ⟨output, ⟨other, falsePart, truePart, hother,
      hf, ht, ho⟩, hclaim⟩ := rows block
    have hsame := output_unique (encode .sub) (base 1)
      (base (S31.Field.toZMod selector)) other complement hother hcomp
    subst other
    exact ⟨falsePart, truePart, output, hf, ht, ho, hclaim⟩

/-- One Boolean selector constrains every active output lane across every
four-lane wire, regardless of final-row padding. -/
theorem packedSelectRows_iff {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31)
    (hbit : selector = 0 ∨ selector = 1) :
    packedSelectRows selector onFalse onTrue claimed tailFalse tailTrue ↔
      ∀ j : Fin n,
        claimed j = if selector = 0 then onFalse j else onTrue j := by
  constructor
  · intro rows j
    have hblock : j.val / 4 < (n + 3) / 4 := by omega
    let block : Fin ((n + 3) / 4) := ⟨j.val / 4, hblock⟩
    have hlimb : j.val % 4 < 4 := by omega
    let limb : Fin 4 := ⟨j.val % 4, hlimb⟩
    have hindex : block.val * 4 + limb.val < n := by
      dsimp [block, limb]
      omega
    obtain ⟨output, hrows, hclaim⟩ := rows block
    have houtput := (acceptsSelect_iff selector _ _ output hbit).mp hrows
    have hvalue : S31.Field.toZMod
        (claimed ⟨block.val * 4 + limb.val, hindex⟩) =
        S31.Field.toZMod
          (if selector = 0 then
            onFalse ⟨block.val * 4 + limb.val, hindex⟩ else
            onTrue ⟨block.val * 4 + limb.val, hindex⟩) := by
      rw [← hclaim limb hindex, houtput]
      by_cases hz : selector = 0
      · simpa [hz, coord_packM31] using
          congrArg S31.Field.toZMod
            (SimdChunks.chunk4_active onFalse block.val
              (tailFalse block.val) limb hindex)
      · simpa [hz, coord_packM31] using
          congrArg S31.Field.toZMod
            (SimdChunks.chunk4_active onTrue block.val
              (tailTrue block.val) limb hindex)
    have hsource := S31.Field.toZMod_injective hvalue
    have hsame : (⟨block.val * 4 + limb.val, hindex⟩ : Fin n) = j := by
      apply Fin.ext
      dsimp [block, limb]
      omega
    simpa [hsame] using hsource
  · intro h block
    let falseWord := packM31
      (SimdChunks.chunk4 onFalse block.val (tailFalse block.val))
    let trueWord := packM31
      (SimdChunks.chunk4 onTrue block.val (tailTrue block.val))
    refine ⟨if selector = 0 then falseWord else trueWord, ?_, ?_⟩
    · exact (acceptsSelect_iff selector falseWord trueWord _ hbit).mpr rfl
    · intro i hi
      by_cases hz : selector = 0
      · simpa [hz, falseWord, coord_packM31,
          SimdChunks.chunk4_active onFalse block.val
            (tailFalse block.val) i hi] using
          congrArg S31.Field.toZMod (h ⟨block.val * 4 + i.val, hi⟩).symm
      · simpa [hz, trueWord, coord_packM31,
          SimdChunks.chunk4_active onTrue block.val
            (tailTrue block.val) i hi] using
          congrArg S31.Field.toZMod (h ⟨block.val * 4 + i.val, hi⟩).symm

/-- A Boolean selector and all of its packed operation rows accept exactly
the source-level array conditional relation, for any array length. The
selector's Boolean constraint is stated separately because its producer may
already have proved it; this theorem does not model Gate lookup wiring. -/
theorem packedSelectRows_iff_arraySelect {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    ((selector = 0 ∨ selector = 1) ∧
      packedSelectRows selector onFalse onTrue claimed tailFalse tailTrue) ↔
      S31.Functional.arraySelect selector onFalse onTrue claimed := by
  constructor
  · rintro ⟨hbit, hrows⟩
    have h := (packedSelectRows_iff selector onFalse onTrue claimed
      tailFalse tailTrue hbit).mp hrows
    apply (S31.Functional.array_select_iff selector onFalse onTrue claimed).mpr
    rcases hbit with hz | ho
    · left
      refine ⟨hz, funext fun i => ?_⟩
      simpa [hz] using h i
    · right
      refine ⟨ho, funext fun i => ?_⟩
      have hz : selector ≠ 0 := by simpa [ho] using
        (show (1 : S31.M31) ≠ 0 by decide)
      simpa [hz] using h i
  · intro h
    rcases (S31.Functional.array_select_iff selector onFalse onTrue claimed).mp h with
      ⟨hz, hout⟩ | ⟨ho, hout⟩
    · refine ⟨Or.inl hz, (packedSelectRows_iff selector onFalse onTrue
        claimed tailFalse tailTrue (Or.inl hz)).mpr ?_⟩
      intro i
      simp [hz, hout]
    · refine ⟨Or.inr ho, (packedSelectRows_iff selector onFalse onTrue
        claimed tailFalse tailTrue (Or.inr ho)).mpr ?_⟩
      intro i
      have hz : selector ≠ 0 := by simpa [ho] using
        (show (1 : S31.M31) ≠ 0 by decide)
      simp [hz, hout]

/-- The same rows agree with the concrete normalized array selection rule. -/
theorem packedSelectRows_iff_normalized {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    ((selector = 0 ∨ selector = 1) ∧
      packedSelectRows selector onFalse onTrue claimed tailFalse tailTrue) ↔
      S31.Functional.normalizedArraySelect selector onFalse onTrue claimed := by
  rw [packedSelectRows_iff_arraySelect,
    S31.Functional.array_select_iff_normalized]

/-- The complete packed selection relation agrees with the executable
normalized `select` node, including rejection of non-Boolean selectors. -/
theorem packedSelectRows_iff_evaluateNode {n : Nat} (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    ((selector = 0 ∨ selector = 1) ∧
      packedSelectRows selector onFalse onTrue claimed tailFalse tailTrue) ↔
      S31.evaluateNode
        (S31.Functional.normalizedSelectEnv selector onFalse onTrue)
        S31.Functional.normalizedSelectNode =
          .ok ⟨.m31, List.ofFn claimed⟩ :=
  (packedSelectRows_iff_arraySelect selector onFalse onTrue claimed
    tailFalse tailTrue).trans
    (S31.Functional.array_select_iff_evaluateNode selector onFalse onTrue claimed)

/-- Source-level eager array conditionals, strict graph acceptance and all
local packed selection rows agree on the final result for every source array
length. The rows for branch subexpressions and Gate lookup remain separate. -/
theorem source_array_if_iff_packed_rows {n m : Nat}
    (selector : S31.Functional.Expr [.array n] .field)
    (onTrue onFalse : S31.Functional.Expr [.array n] (.array m))
    (inputs : List S31.M31) (claimed : Fin m → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31)
    (hinputs : inputs.length = n) :
    S31.Functional.ArrayIfAccepts selector onTrue onFalse inputs claimed ↔
    ((S31.Functional.denote selector
        (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)) = 0 ∨
      S31.Functional.denote selector
        (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)) = 1) ∧
      packedSelectRows
        (S31.Functional.denote selector
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        (S31.Functional.denote onFalse
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        (S31.Functional.denote onTrue
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        claimed tailFalse tailTrue) := by
  rw [S31.Functional.array_if_accepts_iff_normalized selector onTrue
    onFalse inputs claimed hinputs]
  exact (packedSelectRows_iff_normalized _ _ _ _ tailFalse tailTrue).symm

/-- Exact shared-complement row topology also agrees with the executable
normalized `select` node, including non-Boolean selector rejection. -/
theorem packedSelectRowsShared_iff_evaluateNode {n : Nat}
    (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    ((selector = 0 ∨ selector = 1) ∧
      packedSelectRowsShared selector onFalse onTrue claimed
        tailFalse tailTrue) ↔
      S31.evaluateNode
        (S31.Functional.normalizedSelectEnv selector onFalse onTrue)
        S31.Functional.normalizedSelectNode =
          .ok ⟨.m31, List.ofFn claimed⟩ := by
  rw [packedSelectRowsShared_iff]
  exact packedSelectRows_iff_evaluateNode selector onFalse onTrue claimed
    tailFalse tailTrue

/-- The direct selector's self-product row discharges the Boolean premise
for a base-field encoded input, then the shared-complement rows bind every
selected output lane to the executable normalized relation. -/
theorem base_self_product_select_iff_evaluateNode {n : Nat}
    (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    (accepts (encode .mul)
      (base (S31.Field.toZMod selector))
      (base (S31.Field.toZMod selector))
      (base (S31.Field.toZMod selector)) ∧
      packedSelectRowsShared selector onFalse onTrue claimed
        tailFalse tailTrue) ↔
      S31.evaluateNode
        (S31.Functional.normalizedSelectEnv selector onFalse onTrue)
        S31.Functional.normalizedSelectNode =
          .ok ⟨.m31, List.ofFn claimed⟩ := by
  rw [base_selector_self_product_iff]
  exact packedSelectRowsShared_iff_evaluateNode selector onFalse onTrue
    claimed tailFalse tailTrue

/-- The source-to-row selection bridge also holds with an arbitrary QM31
selector witness. Its base coordinate is bound to the source M31 value; the
self-product row proves the remaining coordinates vanish and the value is a
bit. Gate address wiring is a separate global obligation. -/
theorem untrusted_self_product_select_iff_evaluateNode {n : Nat}
    (selector : S31.M31)
    (onFalse onTrue claimed : Fin n → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31) :
    (∃ wire : Quad,
      wire.a = S31.Field.toZMod selector ∧
      accepts (encode .mul) wire wire wire ∧
      packedSelectRowsShared selector onFalse onTrue claimed
        tailFalse tailTrue) ↔
      S31.evaluateNode
        (S31.Functional.normalizedSelectEnv selector onFalse onTrue)
        S31.Functional.normalizedSelectNode =
          .ok ⟨.m31, List.ofFn claimed⟩ := by
  constructor
  · rintro ⟨wire, hcoord, hself, hrows⟩
    have hbit := (untrusted_selector_bound_iff selector wire hcoord).mp hself
    exact (base_self_product_select_iff_evaluateNode selector onFalse
      onTrue claimed tailFalse tailTrue).mp
        ⟨(base_selector_self_product_iff selector).mpr hbit.2, hrows⟩
  · intro hsource
    have hrows := (base_self_product_select_iff_evaluateNode selector onFalse
      onTrue claimed tailFalse tailTrue).mpr hsource
    refine ⟨base (S31.Field.toZMod selector), rfl, hrows.1, hrows.2⟩

/-- The typed source conditional, its strict graph and the compiler-shaped
shared-complement AIR row relation admit precisely the same array outputs. -/
theorem source_array_if_iff_shared_rows {n m : Nat}
    (selector : S31.Functional.Expr [.array n] .field)
    (onTrue onFalse : S31.Functional.Expr [.array n] (.array m))
    (inputs : List S31.M31) (claimed : Fin m → S31.M31)
    (tailFalse tailTrue : Nat → Fin 4 → S31.M31)
    (hinputs : inputs.length = n) :
    S31.Functional.ArrayIfAccepts selector onTrue onFalse inputs claimed ↔
    ((S31.Functional.denote selector
        (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)) = 0 ∨
      S31.Functional.denote selector
        (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)) = 1) ∧
      packedSelectRowsShared
        (S31.Functional.denote selector
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        (S31.Functional.denote onFalse
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        (S31.Functional.denote onTrue
          (S31.Functional.arrayInputSource (fun i => inputs.getD i.val 0)))
        claimed tailFalse tailTrue) := by
  rw [packedSelectRowsShared_iff]
  exact source_array_if_iff_packed_rows selector onTrue onFalse inputs
    claimed tailFalse tailTrue hinputs

/-- Concrete control: without a Boolean producer, four locally valid rows
accept the interpolation `3*(1-2) + 5*2 = 7`. Thus the bit premise above is
essential, even though all four arithmetic row equations are sound. -/
theorem nonbit_interpolation_rows :
    acceptsSelect (RiscvRefinement.M31.reduce 2)
      (base 3) (base 5) (base 7) := by
  let complement := evaluate .sub (base 1)
    (base (S31.Field.toZMod (RiscvRefinement.M31.reduce 2)))
  let falsePart := evaluate .mul (base 3) complement
  let truePart := evaluate .mul (base 5)
    (base (S31.Field.toZMod (RiscvRefinement.M31.reduce 2)))
  refine ⟨complement, falsePart, truePart,
    honest_row _ _ _, honest_row _ _ _, honest_row _ _ _, ?_⟩
  apply (accepts_encoded .add falsePart truePart (base 7)).mpr
  decide

theorem nonbit_interpolation_not_choice :
    (RiscvRefinement.M31.reduce 2) ≠ 0 ∧
      (RiscvRefinement.M31.reduce 2) ≠ 1 ∧
      (base 7 : Quad) ≠ base 3 ∧ (base 7 : Quad) ≠ base 5 := by
  decide

end S31.Gadgets.Air.SelectRows
