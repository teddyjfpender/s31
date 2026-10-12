import S31.Gadgets.Air.Qm31Ops

/-!
The operation-row schedules emitted by `relation_compiler.booleanNode` after
`checkedBitWord` has produced Boolean, base-field scalar operands. All
intermediate row values are arbitrary witnesses. A direct self-product input
still needs the QM31 field/idempotent argument described in `SelectRows`.
-/

namespace S31.Gadgets.Air.BooleanRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

def word (value : Bool) : Quad :=
  base (S31.Gadgets.encodeBool value)

def acceptsNot (a output : Quad) : Prop :=
  accepts (encode .sub) (base 1) a output

def acceptsAnd (a b output : Quad) : Prop :=
  accepts (encode .mul) a b output

def acceptsOr (a b output : Quad) : Prop :=
  ∃ sum product : Quad,
    accepts (encode .add) a b sum ∧
    accepts (encode .mul) a b product ∧
    accepts (encode .sub) sum product output

def acceptsXor (a b output : Quad) : Prop :=
  ∃ sum product twice : Quad,
    accepts (encode .add) a b sum ∧
    accepts (encode .mul) a b product ∧
    accepts (encode .mul) (base 2) product twice ∧
    accepts (encode .sub) sum twice output

def acceptsSelect (selector a b output : Quad) : Prop :=
  ∃ complement falsePart truePart : Quad,
    accepts (encode .sub) (base 1) selector complement ∧
    accepts (encode .mul) complement a falsePart ∧
    accepts (encode .mul) selector b truePart ∧
    accepts (encode .add) falsePart truePart output

theorem not_iff (a : Bool) (output : Quad) :
    acceptsNot (word a) output ↔ output = word (!a) := by
  rw [acceptsNot, accepts_encoded]
  cases a <;> simp [word, S31.Gadgets.encodeBool, evaluate,
    subtract, base]

theorem and_iff (a b : Bool) (output : Quad) :
    acceptsAnd (word a) (word b) output ↔ output = word (a && b) := by
  rw [acceptsAnd, accepts_encoded]
  cases a <;> cases b <;>
    simp [word, S31.Gadgets.encodeBool, evaluate, Packed.mul, base]

theorem or_iff (a b : Bool) (output : Quad) :
    acceptsOr (word a) (word b) output ↔ output = word (a || b) := by
  constructor
  · rintro ⟨sum, product, hs, hp, ho⟩
    rw [(accepts_encoded .add _ _ _).mp hs] at ho
    rw [(accepts_encoded .mul _ _ _).mp hp] at ho
    rw [(accepts_encoded .sub _ _ _).mp ho]
    cases a <;> cases b <;>
      simp [word, S31.Gadgets.encodeBool, evaluate,
        Packed.add, Packed.mul, subtract, base]
  · intro hout
    let sum := evaluate .add (word a) (word b)
    let product := evaluate .mul (word a) (word b)
    refine ⟨sum, product, honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (accepts_encoded .sub sum product output).mpr
    rw [hout]
    cases a <;> cases b <;>
      simp [sum, product, word, S31.Gadgets.encodeBool,
        evaluate, Packed.add, Packed.mul, subtract, base]

theorem xor_iff (a b : Bool) (output : Quad) :
    acceptsXor (word a) (word b) output ↔ output = word (a != b) := by
  constructor
  · rintro ⟨sum, product, twice, hs, hp, ht, ho⟩
    rw [(accepts_encoded .add _ _ _).mp hs] at ho
    rw [(accepts_encoded .mul _ _ _).mp hp] at ht
    rw [(accepts_encoded .mul _ _ _).mp ht] at ho
    rw [(accepts_encoded .sub _ _ _).mp ho]
    cases a <;> cases b <;>
      simp [word, S31.Gadgets.encodeBool, evaluate,
        Packed.add, Packed.mul, subtract, base]; ring
  · intro hout
    let sum := evaluate .add (word a) (word b)
    let product := evaluate .mul (word a) (word b)
    let twice := evaluate .mul (base 2) product
    refine ⟨sum, product, twice,
      honest_row _ _ _, honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (accepts_encoded .sub sum twice output).mpr
    rw [hout]
    cases a <;> cases b <;>
      simp [sum, product, twice, word, S31.Gadgets.encodeBool,
        evaluate, Packed.add, Packed.mul, subtract, base]; ring

theorem select_iff (selector a b : Bool) (output : Quad) :
    acceptsSelect (word selector) (word a) (word b) output ↔
      output = word (if selector then b else a) := by
  constructor
  · rintro ⟨complement, falsePart, truePart, hc, hf, ht, ho⟩
    rw [(accepts_encoded .sub _ _ _).mp hc] at hf
    rw [(accepts_encoded .mul _ _ _).mp hf] at ho
    rw [(accepts_encoded .mul _ _ _).mp ht] at ho
    rw [(accepts_encoded .add _ _ _).mp ho]
    cases selector <;> cases a <;> cases b <;>
      simp [word, S31.Gadgets.encodeBool, evaluate,
        Packed.add, Packed.mul, subtract, base]
  · intro hout
    let complement := evaluate .sub (base 1) (word selector)
    let falsePart := evaluate .mul complement (word a)
    let truePart := evaluate .mul (word selector) (word b)
    refine ⟨complement, falsePart, truePart,
      honest_row _ _ _, honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (accepts_encoded .add falsePart truePart output).mpr
    rw [hout]
    cases selector <;> cases a <;> cases b <;>
      simp [complement, falsePart, truePart, word,
        S31.Gadgets.encodeBool, evaluate, Packed.add,
        Packed.mul, subtract, base]

end S31.Gadgets.Air.BooleanRows
