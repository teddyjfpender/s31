import S31.Gadgets.PcsFri.QuerySampling
import S31.Gadgets.PcsFri.M31MaskedQuery

/-!
An ideal raw FRI query selects a complete local fiber bundle. If every row
in that bundle is checked, sampling a uniformly random raw row cannot make a
fixed bad-row set harder to detect: the set of raw positions whose bundles
intersect the bad set contains the bad set itself. This elementary counting
step connects a row-distance premise to the bundled-query event.

The theorem does not establish that native checks inspect every required
row, that the bad set is fixed before Fiat–Shamir draws, or that the native
masked sampler is uniform. Those are separate PCS/FRI obligations.
-/

namespace S31.Gadgets.PcsFri.BundleQueryBound

open S31.Gadgets.PcsFri.QuerySampling
open S31.Gadgets.PcsFri.M31MaskedQuery

variable {D K : Type*} [Fintype D] [DecidableEq D] [DecidableEq K]

/-- Raw positions whose bundle contains no row from a fixed bad set. The
`bundle` map may be any partition label, including native `row >> h`. -/
def goodBundle (bad : Finset D) (bundle : D → K) : Finset D :=
  Finset.univ.filter fun raw => ∀ row ∈ bad, bundle raw ≠ bundle row

/-- A bad row always lies in a bundle that contains a bad row: itself. -/
theorem goodBundle_disjoint_bad (bad : Finset D) (bundle : D → K) :
    Disjoint (goodBundle bad bundle) bad := by
  apply Finset.disjoint_left.mpr
  intro raw hgood hbad
  have hreject := (Finset.mem_filter.mp hgood).2 raw hbad
  exact hreject rfl

/-- The raw positions that miss all bad bundles form a subset of the
ordinary good-row positions, regardless of bundle size or repeated queries. -/
theorem goodBundle_subset_goodRows (bad : Finset D) (bundle : D → K) :
    goodBundle bad bundle ⊆ Finset.univ \ bad := by
  intro raw hgood
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hbad
  exact Finset.disjoint_left.mp (goodBundle_disjoint_bad bad bundle) hgood hbad

theorem goodBundle_card_le_goodRows (bad : Finset D) (bundle : D → K) :
    (goodBundle bad bundle).card ≤ Fintype.card D - bad.card := by
  have hcard := Finset.card_le_card (goodBundle_subset_goodRows bad bundle)
  simpa [Finset.card_sdiff] using hcard

/-- For independent ideal raw draws with replacement, the number of
all-undetected query vectors is at most the ordinary good-row count to `s`.
The separate native-to-bundle refinement remains a premise. -/
theorem goodBundle_sequences_card_le (s : Nat) (bad : Finset D)
    (bundle : D → K) :
    (goodSequences s (goodBundle bad bundle)).card ≤
      (Fintype.card D - bad.card) ^ s := by
  rw [good_sequences_card]
  gcongr
  exact goodBundle_card_le_goodRows bad bundle

/-- Join the bundle-counting step with the exact native M31-reduce-and-mask
preimage count. Under *independent ideal uniform raw words*, the all-missed
fraction is bounded by good-row density plus the native two-word bias. This
does not establish Fiat–Shamir independence or the verifier-to-bundle link. -/
theorem masked_bundle_miss_fraction_le {K : Type*} [DecidableEq K]
    (k draws : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31)
    (bad : Finset (Fin (size k))) (bundle : Fin (size k) → K) :
    ((goodSequences draws (goodRawFin k (goodBundle bad bundle))).card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤
        (((size k - bad.card : Nat) : ℚ) / (size k : ℚ) +
          2 / (rawSize : ℚ)) ^ draws := by
  have hcount : (goodBundle bad bundle).card ≤ size k - bad.card := by
    simpa using goodBundle_card_le_goodRows bad bundle
  have hdensity : uniformMass k (goodBundle bad bundle) ≤
      ((size k - bad.card : Nat) : ℚ) / (size k : ℚ) := by
    unfold uniformMass
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
  exact exact_raw_product_ge_two_vs_alpha k hk hk31
    (goodBundle bad bundle) draws
    (((size k - bad.card : Nat) : ℚ) / (size k : ℚ)) hdensity

end S31.Gadgets.PcsFri.BundleQueryBound
