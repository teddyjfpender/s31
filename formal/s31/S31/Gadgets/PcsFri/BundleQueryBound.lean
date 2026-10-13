import S31.Gadgets.PcsFri.QuerySampling

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

end S31.Gadgets.PcsFri.BundleQueryBound
