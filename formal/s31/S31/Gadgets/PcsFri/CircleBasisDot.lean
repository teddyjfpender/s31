import S31.Gadgets.PcsFri.CircleRecursiveBasisDegree

/-!
# Circle coefficient basis dot product

The native sampled-value fast paths evaluate coefficient arrays using the
subset-product basis, rather than the recursive reference evaluator. This
module proves the mathematical equality between that dot product and the
half-split recursive recurrence for every power-of-two coefficient count.
It does not yet refine the native loops or packed arithmetic.
-/

namespace S31.Gadgets.PcsFri.CircleBasisDot

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The factor product indexed by the low `k` bits of a coefficient slot. -/
def basisWeight (factors : Nat → E) : Nat → Nat → E
  | 0, _ => 1
  | k + 1, j =>
      basisWeight factors k (j % 2 ^ k) *
        if j < 2 ^ k then 1 else factors k

/-- One dot product over the entire `2^k` coefficient word. -/
def basisDot (factors : Nat → E) (k : Nat) (coefficients : Nat → F) : E :=
  ∑ j ∈ Finset.range (2 ^ k),
    (algebraMap F E) (coefficients j) * basisWeight factors k j

/-- A low/high factored dot product, matching the mathematical shape of the
native split-basis kernel. -/
def splitDot (factors : Nat → E) (low high : Nat)
    (coefficients : Nat → F) : E :=
  ∑ block ∈ Finset.range (2 ^ high),
    basisDot factors low
      (fun j => coefficients (j + block * 2 ^ low)) *
      basisWeight (fun r => factors (low + r)) high block

/-- Half-split semantic recurrence, independent of a list representation. -/
def recursiveFunction (factors : Nat → E) : Nat → (Nat → F) → E
  | 0, coefficients => (algebraMap F E) (coefficients 0)
  | k + 1, coefficients =>
      recursiveFunction factors k coefficients +
        recursiveFunction factors k (fun j => coefficients (j + 2 ^ k)) *
          factors k

private theorem basisWeight_low (factors : Nat → E) (k j : Nat)
    (hj : j < 2 ^ k) :
    basisWeight factors (k + 1) j = basisWeight factors k j := by
  simp [basisWeight, Nat.mod_eq_of_lt hj, hj]

private theorem basisWeight_high (factors : Nat → E) (k j : Nat)
    (hj : j < 2 ^ k) :
    basisWeight factors (k + 1) (j + 2 ^ k) =
      basisWeight factors k j * factors k := by
  have hnlt : ¬ j + 2 ^ k < 2 ^ k := by omega
  simp [basisWeight, Nat.add_mod_right, Nat.mod_eq_of_lt hj, hnlt]

theorem basisDot_succ
    (factors : Nat → E) (k : Nat) (coefficients : Nat → F) :
    basisDot factors (k + 1) coefficients =
      basisDot factors k coefficients +
        basisDot factors k (fun j => coefficients (j + 2 ^ k)) * factors k := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    simp [pow_succ]; omega
  have hlow :
      (∑ j ∈ Finset.range (2 ^ k),
        (algebraMap F E) (coefficients j) * basisWeight factors (k + 1) j) =
      basisDot factors k coefficients := by
    unfold basisDot
    apply Finset.sum_congr rfl
    intro j hj
    rw [basisWeight_low factors k j (Finset.mem_range.mp hj)]
  have hhigh :
      (∑ j ∈ Finset.range (2 ^ k),
        (algebraMap F E) (coefficients (2 ^ k + j)) *
          basisWeight factors (k + 1) (2 ^ k + j)) =
      basisDot factors k (fun j => coefficients (j + 2 ^ k)) * factors k := by
    rw [basisDot, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 2 ^ k + j = j + 2 ^ k by omega,
      basisWeight_high factors k j (Finset.mem_range.mp hj)]
    ring
  rw [basisDot, hpow, Finset.sum_range_add, hlow, hhigh]

theorem basisDot_eq_recursiveFunction
    (factors : Nat → E) (k : Nat) (coefficients : Nat → F) :
    basisDot factors k coefficients = recursiveFunction factors k coefficients := by
  induction k generalizing coefficients with
  | zero =>
      simp [basisDot, recursiveFunction, basisWeight]
  | succ k ih =>
      rw [basisDot_succ, recursiveFunction, ih, ih]

private theorem basisDot_congr
    (factors : Nat → E) (k : Nat) (a b : Nat → F)
    (hab : ∀ j < 2 ^ k, a j = b j) :
    basisDot factors k a = basisDot factors k b := by
  unfold basisDot
  apply Finset.sum_congr rfl
  intro j hj
  rw [hab j (Finset.mem_range.mp hj)]

/-- Algebraic low/high factorization used by the native split-basis path.
This concerns mathematical products and sums; the native packed loops and
array slices require separate implementation refinement. -/
theorem basisDot_split
    (factors : Nat → E) (low high : Nat) (coefficients : Nat → F) :
    basisDot factors (low + high) coefficients =
      ∑ block ∈ Finset.range (2 ^ high),
        basisDot factors low
          (fun j => coefficients (j + block * 2 ^ low)) *
          basisWeight (fun r => factors (low + r)) high block := by
  induction high generalizing coefficients with
  | zero =>
      simp [basisWeight]
  | succ high ih =>
      let shifted : Nat → E := fun r => factors (low + r)
      have hpow : 2 ^ (high + 1) = 2 ^ high + 2 ^ high := by
        simp [pow_succ]; omega
      have hshift : 2 ^ (low + high) = 2 ^ high * 2 ^ low := by
        rw [pow_add]; ring
      have hlow :
          (∑ block ∈ Finset.range (2 ^ high),
            basisDot factors low
              (fun j => coefficients (j + block * 2 ^ low)) *
              basisWeight shifted (high + 1) block) =
          basisDot factors (low + high) coefficients := by
        rw [ih]
        apply Finset.sum_congr rfl
        intro block hb
        rw [basisWeight_low shifted high block (Finset.mem_range.mp hb)]
      have hhigh :
          (∑ block ∈ Finset.range (2 ^ high),
            basisDot factors low
              (fun j => coefficients (j + (2 ^ high + block) * 2 ^ low)) *
              basisWeight shifted (high + 1) (2 ^ high + block)) =
          basisDot factors (low + high)
            (fun j => coefficients (j + 2 ^ (low + high))) *
            factors (low + high) := by
        rw [ih, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro block hb
        rw [show 2 ^ high + block = block + 2 ^ high by omega,
          basisWeight_high shifted high block (Finset.mem_range.mp hb)]
        dsimp [shifted]
        have hindex :
            basisDot factors low
              (fun j => coefficients (j + (block + 2 ^ high) * 2 ^ low)) =
            basisDot factors low
              (fun j => coefficients (j + block * 2 ^ low + 2 ^ (low + high))) := by
          apply basisDot_congr
          intro j _
          congr 1
          rw [hshift]
          ring
        rw [hindex]
        ring
      rw [show low + (high + 1) = (low + high) + 1 by omega,
        basisDot_succ, hpow, Finset.sum_range_add, hlow, hhigh]

theorem splitDot_eq_basisDot
    (factors : Nat → E) (low high : Nat) (coefficients : Nat → F) :
    splitDot factors low high coefficients =
      basisDot factors (low + high) coefficients := by
  exact (basisDot_split factors low high coefficients).symm

/-- The source-transcribed list recurrence is exactly the subset-product
dot product for every list (out-of-range coefficient slots read as zero).
This supplies the mathematical target for native subset and split basis
kernels; the split factorization is proved separately, while array
indexing and packed loops still require refinement. -/
theorem recursiveValue_eq_basisDot
    (x y : E) (k : Nat) (coefficients : List F) :
    CircleRecursiveBasisDegree.recursiveValue x y k coefficients =
      basisDot (CircleRecursiveBasisDegree.nativeFactorValue x y) k
        (fun j => coefficients.getD j 0) := by
  induction k generalizing coefficients with
  | zero =>
      simp [CircleRecursiveBasisDegree.recursiveValue, basisDot,
        basisWeight, List.getD, List.head?_eq_getElem?]
  | succ k ih =>
      let factors := CircleRecursiveBasisDegree.nativeFactorValue x y
      have htake : basisDot factors k
          (fun j => (coefficients.take (2 ^ k)).getD j 0) =
          basisDot factors k (fun j => coefficients.getD j 0) := by
        apply basisDot_congr
        intro j hj
        simp [List.getD, hj]
      have hdrop : basisDot factors k
          (fun j => (coefficients.drop (2 ^ k)).getD j 0) =
          basisDot factors k (fun j => coefficients.getD (j + 2 ^ k) 0) := by
        apply basisDot_congr
        intro j _
        simp [List.getD, List.getElem?_drop, Nat.add_comm]
      rw [CircleRecursiveBasisDegree.recursiveValue,
        ih (coefficients.take (2 ^ k)),
        ih (coefficients.drop (2 ^ k)), htake, hdrop]
      exact (basisDot_succ factors k (fun j => coefficients.getD j 0)).symm

/-- The mathematical subset-product dot evaluates the exact bounded circle
Laurent word, including at a secure-field OOD point. -/
theorem basisDot_eq_coefficientWord_eval
    [NeZero (2 : F)]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ)
    (k : Nat) (coefficients : List F) :
    basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX z.val z⁻¹.val)
        (CircleLaurentDegree.fourierY ((algebraMap F E) i)
          z.val z⁻¹.val))
      k (fun j => coefficients.getD j 0) =
        LaurentPolynomial.eval₂ (algebraMap F E) z
          (CircleRecursiveBasisDegree.coefficientWord i k coefficients) := by
  rw [← recursiveValue_eq_basisDot]
  exact (CircleRecursiveBasisDegree.coefficientWord_eval_algebra
    i hi z k coefficients).symm

theorem accepted_height17_split_equals_recursiveValue
    (x y : E) (coefficients : List F) :
    splitDot (CircleRecursiveBasisDegree.nativeFactorValue x y) 10 6
        (fun j => coefficients.getD j 0) =
      CircleRecursiveBasisDegree.recursiveValue x y 16 coefficients := by
  calc
    _ = basisDot (CircleRecursiveBasisDegree.nativeFactorValue x y)
        (10 + 6) (fun j => coefficients.getD j 0) :=
          splitDot_eq_basisDot _ 10 6 _
    _ = CircleRecursiveBasisDegree.recursiveValue x y 16 coefficients := by
      simpa only [show 10 + 6 = 16 by norm_num] using
        (recursiveValue_eq_basisDot x y 16 coefficients).symm

/-- A source word whose two projected sampled values equal the full
subset-product dot products has an own quotient at each point. This theorem
bridges the mathematical fast-path operation to the two-Q degree theorem,
with explicit source-height and imaginary-unit equalities for both claims;
the native materialization and packed dot-product loops still need refinement. -/
theorem accepted_basis_dot_two_q_own_quotients
    [NeZero (2 : F)]
    (h : Nat) (hh : h ∈ SparseP05TwoQDegree.acceptedHeights)
    (i : F) (hi : i ^ 2 = -1) (coefficients : List F)
    (c₀ c₁ : SparseP05TwoQDegree.ProjectedConjugateClaim F E)
    (hheight₀ : c₀.sourceHeight = h)
    (hheight₁ : c₁.sourceHeight = h)
    (himag₀ : c₀.i = i)
    (himag₁ : c₁.i = i)
    (hdistinct : c₀.z ≠ c₁.z)
    (hvalue₀ : basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX c₀.z.val c₀.z⁻¹.val)
        (CircleLaurentDegree.fourierY ((algebraMap F E) i)
          c₀.z.val c₀.z⁻¹.val))
      (h - 1) (fun j => coefficients.getD j 0) =
        LaurentPolynomial.eval₂ (algebraMap F E) c₀.z c₀.interpolation)
    (hvalue₁ : basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX c₁.z.val c₁.z⁻¹.val)
        (CircleLaurentDegree.fourierY ((algebraMap F E) i)
          c₁.z.val c₁.z⁻¹.val))
      (h - 1) (fun j => coefficients.getD j 0) =
        LaurentPolynomial.eval₂ (algebraMap F E) c₁.z c₁.interpolation) :
    ∃ q₀ q₁ : CircleLaurentDegree.CirclePoly F,
      CircleLaurentDegree.InCircleBand
        (SparseP05TwoQDegree.sourceRadius h - 1) q₀ ∧
      CircleLaurentDegree.InCircleBand
        (SparseP05TwoQDegree.sourceRadius h - 1) q₁ ∧
      CircleRecursiveBasisDegree.coefficientWord i (h - 1) coefficients =
        c₀.interpolation +
          CircleLaurentDegree.nativeLineLaurent
            c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁ * q₀ ∧
      CircleRecursiveBasisDegree.coefficientWord i (h - 1) coefficients =
        c₁.interpolation +
          CircleLaurentDegree.nativeLineLaurent
            c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁ * q₁ := by
  apply CircleRecursiveBasisDegree.accepted_recursive_word_two_q_own_quotients
    h hh i hi coefficients c₀ c₁ hheight₀ hheight₁ himag₀ himag₁ hdistinct
  · rw [recursiveValue_eq_basisDot]
    exact hvalue₀
  · rw [recursiveValue_eq_basisDot]
    exact hvalue₁

end S31.Gadgets.PcsFri.CircleBasisDot
