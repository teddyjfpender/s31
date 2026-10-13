import S31.Gadgets.PcsFri.QuerySampling
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

/-- Raw rows whose sparse projected circle row belongs to a fixed bad set. -/
def projectedBadRaw (k i : Nat) (hi : i < k)
    (bad : Finset (Fin (2 ^ (k - i)))) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun raw => (sparseSplit k i hi raw).1 ∈ bad)

/-- The exact count of raw rows that project into a fixed bad source-row set.
This is the finite counting premise behind sparse-path query analysis. -/
theorem projected_bad_raw_card (k i : Nat) (hi : i < k)
    (bad : Finset (Fin (2 ^ (k - i)))) :
    (projectedBadRaw k i hi bad).card = bad.card * 2 ^ i := by
  classical
  have hfiber (row : Fin (2 ^ (k - i))) :
      (Finset.univ.filter (fun raw : Fin (2 ^ k) =>
        (sparseSplit k i hi raw).1 = row)).card = 2 ^ i := by
    convert projected_fiber_card k i hi row using 1
    apply congrArg Finset.card
    ext raw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.ext_iff, sparseSplit_projected]
  calc
    (projectedBadRaw k i hi bad).card =
        ∑ row ∈ bad, (Finset.univ.filter (fun raw : Fin (2 ^ k) =>
          (sparseSplit k i hi raw).1 = row)).card := by
            simpa [projectedBadRaw] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (Finset.univ : Finset (Fin (2 ^ k))) bad
                (fun raw => (sparseSplit k i hi raw).1)).symm
    _ = bad.card * 2 ^ i := by simp [hfiber]

/-- A sparse pair misses a bad set only if neither of its two opened rows is
bad. This is the event the native CAS05 verifier must refine. -/
def goodSparsePair (k i : Nat) (bad : Finset (Fin (2 ^ (k - i)))) :
    Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun raw => ∀ row ∈ bad,
    row.val ≠ pairBase raw.val i ∧ row.val ≠ pairBase raw.val i + 1)

theorem good_sparse_disjoint_projected_bad (k i : Nat) (hi : i < k)
    (bad : Finset (Fin (2 ^ (k - i)))) :
    Disjoint (goodSparsePair k i bad) (projectedBadRaw k i hi bad) := by
  apply Finset.disjoint_left.mpr
  intro raw hgood hbad
  have hmiss := (Finset.mem_filter.mp hgood).2
  have hselected := (Finset.mem_filter.mp hbad).2
  have hrow := hmiss (sparseSplit k i hi raw).1 hselected
  have hvalue := sparseSplit_projected k i hi raw
  rcases projected_in_opened_pair raw.val i with heven | hodd
  · exact hrow.1 (hvalue.trans heven)
  · exact hrow.2 (hvalue.trans hodd)

/-- Under independent *uniform* raw queries, missing a fixed bad source-row
set in every opened pair is bounded by ordinary row-distance sampling on
that source height. This says nothing about native BCS or Merkle binding. -/
theorem good_sparse_sequences_card_le (k i draws : Nat) (hi : i < k)
    (bad : Finset (Fin (2 ^ (k - i)))) :
    (S31.Gadgets.PcsFri.QuerySampling.goodSequences draws
      (goodSparsePair k i bad)).card ≤
      ((2 ^ (k - i) - bad.card) * 2 ^ i) ^ draws := by
  have hsubset : goodSparsePair k i bad ⊆
      Finset.univ \ projectedBadRaw k i hi bad := by
    intro raw hgood
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun hbad => Finset.disjoint_left.mp
      (good_sparse_disjoint_projected_bad k i hi bad) hgood hbad
  have hcount := Finset.card_le_card hsubset
  have htotal : Fintype.card (Fin (2 ^ k)) =
      2 ^ (k - i) * 2 ^ i := by
    rw [Fintype.card_fin, ← pow_add]
    congr 1
    omega
  have hgood : (goodSparsePair k i bad).card ≤
      (2 ^ (k - i) - bad.card) * 2 ^ i := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, htotal,
      projected_bad_raw_card] at hcount
    simpa [Nat.sub_mul] using hcount
  rw [S31.Gadgets.PcsFri.QuerySampling.good_sequences_card]
  exact Nat.pow_le_pow_left hgood _

end S31.Gadgets.PcsFri.SparseCascadeQueries
