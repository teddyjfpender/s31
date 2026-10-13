import Mathlib.Tactic

/-!
The bit-reversed query path used by the experimental adjacent-height paired
FRI cascade. `r` is a raw row in the largest circle domain. At source height
`i`, the verifier opens the adjacent pair whose even row is `pairBase r i`.
The circle projection preserves the low bit of `r` while deleting the next
`i` bits. The line fold output selects one member of the next line pair.

These are index identities, not a proximity theorem. In particular, the
older full-fiber bundle counting lemma must not be used for this sparse path
without proving the sparse verifier's exact inspected-row relation.
-/

namespace S31.Gadgets.PcsFri.SparseCascadeQueries

def pairBase (r i : Nat) : Nat := 2 * (r / 2 ^ (i + 1))

def projectedCircleRow (r i : Nat) : Nat := pairBase r i + r % 2

def lineFoldRow (r i : Nat) : Nat := r / 2 ^ (i + 1)

theorem projected_in_opened_pair (r i : Nat) :
    projectedCircleRow r i = pairBase r i ∨
      projectedCircleRow r i = pairBase r i + 1 := by
  unfold projectedCircleRow
  have hbit : r % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

theorem projected_circle_row_zero (r : Nat) :
    projectedCircleRow r 0 = r := by
  simpa [projectedCircleRow, pairBase, Nat.add_comm, Nat.mul_comm]
    using (Nat.mod_add_div r 2)

theorem opened_pair_folds_to_line_row (r i : Nat) :
    pairBase r i / 2 = lineFoldRow r i := by
  simp [pairBase, lineFoldRow]

theorem line_row_in_next_opened_pair (r i : Nat) :
    lineFoldRow r i = pairBase r (i + 1) ∨
      lineFoldRow r i = pairBase r (i + 1) + 1 := by
  have h : lineFoldRow r i = 2 * (lineFoldRow r i / 2) + lineFoldRow r i % 2 := by
    omega
  have hdiv : lineFoldRow r i / 2 = r / 2 ^ (i + 2) := by
    simp [lineFoldRow, Nat.div_div_eq_div_mul, pow_succ,
      show i + 2 = i + 1 + 1 by omega]
  have hbit : lineFoldRow r i % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [hdiv] at h
  simp only [pairBase, show i + 1 + 1 = i + 2 by omega]
  omega

theorem pair_base_even (r i : Nat) : pairBase r i % 2 = 0 := by
  simp [pairBase]

theorem projected_circle_row_parity (r i : Nat) :
    projectedCircleRow r i % 2 = r % 2 := by
  simp [projectedCircleRow, pairBase, Nat.add_mod]

theorem projected_circle_row_div_two (r i : Nat) :
    projectedCircleRow r i / 2 = lineFoldRow r i := by
  unfold projectedCircleRow pairBase lineFoldRow
  have hbit : r % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

theorem sparse_query_bounds (k i r : Nat) (hi : i < k)
    (hr : r < 2 ^ k) :
    projectedCircleRow r i < 2 ^ (k - i) ∧
      pairBase r i + 1 < 2 ^ (k - i) := by
  have hfactor : 2 ^ k = 2 ^ (k - (i + 1)) * 2 ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hquot : r / 2 ^ (i + 1) < 2 ^ (k - (i + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    rw [← hfactor]
    exact hr
  have hnext : 2 ^ (k - i) = 2 * 2 ^ (k - (i + 1)) := by
    have h : k - i = k - (i + 1) + 1 := by omega
    rw [h, pow_succ]
    omega
  have hbit : r % 2 < 2 := Nat.mod_lt _ (by omega)
  unfold projectedCircleRow pairBase
  constructor <;> omega

private def swapMiddle (A B C : Type*) : (A × B) × C ≃ (A × C) × B where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := by intro ⟨⟨_, _⟩, _⟩; rfl
  right_inv := by intro ⟨⟨_, _⟩, _⟩; rfl

/-- Separate the `i` omitted middle bits from the retained high and low
bits. This equivalence gives an exact `2^i`-to-one counting interface for a
uniform raw query. The native transcript still needs its own independence
and source-binding proof. -/
def sparseSplit (k i : Nat) (hi : i < k) :
    Fin (2 ^ k) ≃ Fin (2 ^ (k - i)) × Fin (2 ^ i) := by
  let A := 2 ^ (k - i - 1)
  let B := 2 ^ i
  have h₁ : 2 ^ k = (A * B) * 2 := by
    dsimp [A, B]
    calc
      2 ^ k = 2 ^ ((k - i - 1) + i + 1) := by congr 1; omega
      _ = (2 ^ (k - i - 1) * 2 ^ i) * 2 := by rw [pow_add, pow_succ, pow_add]; norm_num
  have h₂ : A * 2 = 2 ^ (k - i) := by
    dsimp [A]
    rw [← pow_succ]
    congr 1
    omega
  let e₀ : Fin (2 ^ k) ≃ Fin ((A * B) * 2) := finCongr h₁
  let e₁ : Fin ((A * B) * 2) ≃ Fin (A * B) × Fin 2 :=
    (finProdFinEquiv (m := A * B) (n := 2)).symm
  let e₂ : Fin (A * B) × Fin 2 ≃ (Fin A × Fin B) × Fin 2 :=
    ((finProdFinEquiv (m := A) (n := B)).symm).prodCongr (Equiv.refl _)
  let e₃ : (Fin A × Fin B) × Fin 2 ≃ (Fin A × Fin 2) × Fin B :=
    swapMiddle (Fin A) (Fin B) (Fin 2)
  let e₄ : (Fin A × Fin 2) × Fin B ≃ Fin (2 ^ (k - i)) × Fin B :=
    ((finProdFinEquiv (m := A) (n := 2)).trans (finCongr h₂)).prodCongr (Equiv.refl _)
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans e₄)))

theorem sparseSplit_projected (k i : Nat) (hi : i < k)
    (raw : Fin (2 ^ k)) :
    (sparseSplit k i hi raw).1.val = projectedCircleRow raw.val i := by
  simp [sparseSplit, finProdFinEquiv, swapMiddle, projectedCircleRow,
    pairBase, finCongr, Nat.div_div_eq_div_mul, pow_succ]
  rw [mul_comm (2 : Nat) (2 ^ i), add_comm]

/-- For a uniform raw row in a `2^k`-row domain, every projected source row
at height `i` has exactly `2^i` raw preimages. This is an exact combinatorial
statement about the path schedule, conditional on uniform raw sampling. -/
theorem projected_fiber_card (k i : Nat) (hi : i < k)
    (projected : Fin (2 ^ (k - i))) :
    (Finset.univ.filter (fun raw : Fin (2 ^ k) =>
      projectedCircleRow raw.val i = projected.val)).card = 2 ^ i := by
  classical
  let e := sparseSplit k i hi
  have hset :
      (Finset.univ.filter (fun raw : Fin (2 ^ k) =>
        projectedCircleRow raw.val i = projected.val)) =
      Finset.univ.filter (fun raw => (e raw).1 = projected) := by
    ext raw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.ext_iff, sparseSplit_projected]
  rw [hset]
  have hcard : (Finset.univ.filter (fun raw : Fin (2 ^ k) =>
      (e raw).1 = projected)).card = (Finset.univ : Finset (Fin (2 ^ i))).card := by
    apply Finset.card_bij (fun raw _ => (e raw).2)
    · intro raw hraw
      simp
    · intro raw hraw other hother heq
      apply e.injective
      apply Prod.ext
      · exact (Finset.mem_filter.mp hraw).2.trans (Finset.mem_filter.mp hother).2.symm
      · exact heq
    · intro middle _
      refine ⟨e.symm (projected, middle), ?_, ?_⟩ <;> simp
  simpa using hcard

end S31.Gadgets.PcsFri.SparseCascadeQueries
