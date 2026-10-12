import S31.Gadgets.Air.PermutationScratch

namespace S31.Gadgets.Air.PermutationRows
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.LogUpCount
open S31.Gadgets.Air.GateLookup

theorem zero_add_word (word : Quad) :
    evaluate .add (base 0) word = word := by
  cases word
  simp [evaluate, Packed.add, base]

/-- Each permutation pair has two ordinary add rows. The first yields the
input value at the shared scratch address; the second reads one scratch
value and yields the output value. -/
theorem permutation_rows_sound {n : Nat}
    (scratchAddress : Nat)
    (inputs outputs producedScratch readScratch : Fin n → Quad)
    (hfirst : ∀ i,
      accepts (encode .add) (base 0) (inputs i) (producedScratch i))
    (hsecond : ∀ i,
      accepts (encode .add) (base 0) (readScratch i) (outputs i))
    (hscratch :
      (List.ofFn fun i => (scratchAddress, readScratch i)).Perm
        (List.ofFn fun i => (scratchAddress, producedScratch i))) :
    (List.ofFn outputs).Perm (List.ofFn inputs) := by
  have hproduced : ∀ i, producedScratch i = inputs i := by
    intro i
    have h := (accepts_encoded .add (base 0)
      (inputs i) (producedScratch i)).mp (hfirst i)
    simpa [zero_add_word] using h
  have hread : ∀ i, outputs i = readScratch i := by
    intro i
    have h := (accepts_encoded .add (base 0)
      (readScratch i) (outputs i)).mp (hsecond i)
    simpa [zero_add_word] using h
  have hmap :
      ((List.ofFn readScratch).map fun word =>
          (scratchAddress, word)).Perm
        ((List.ofFn producedScratch).map fun word =>
          (scratchAddress, word)) := by
    simpa only [List.map_ofFn] using hscratch
  have hwords : (List.ofFn readScratch).Perm
      (List.ofFn producedScratch) := by
    classical
    apply mapped_perm_reflects _ _
      (fun word => (scratchAddress, word))
      (fun a _ b _ heq => congrArg Prod.snd heq)
      hmap
  have hout : List.ofFn outputs = List.ofFn readScratch := by
    congr 1
    funext i
    exact hread i
  have hin : List.ofFn producedScratch = List.ofFn inputs := by
    congr 1
    funext i
    exact hproduced i
  simpa [hout, hin] using hwords

theorem permutation_rows_complete {n : Nat}
    (scratchAddress : Nat) (inputs outputs : Fin n → Quad)
    (hperm : (List.ofFn outputs).Perm (List.ofFn inputs)) :
    ∃ producedScratch readScratch : Fin n → Quad,
      (∀ i, accepts (encode .add) (base 0)
        (inputs i) (producedScratch i)) ∧
      (∀ i, accepts (encode .add) (base 0)
        (readScratch i) (outputs i)) ∧
      (List.ofFn fun i => (scratchAddress, readScratch i)).Perm
        (List.ofFn fun i => (scratchAddress, producedScratch i)) := by
  refine ⟨inputs, outputs, ?_, ?_, ?_⟩
  · intro i
    exact (accepts_encoded .add (base 0) (inputs i) (inputs i)).mpr
      (zero_add_word (inputs i)).symm
  · intro i
    exact (accepts_encoded .add (base 0) (outputs i) (outputs i)).mpr
      (zero_add_word (outputs i)).symm
  · simpa only [List.map_ofFn] using
      hperm.map (fun word => (scratchAddress, word))

/-- The ideal two-row schedule plus scratch multiset check accepts exactly
the permutations of its input words. -/
theorem permutation_rows_iff {n : Nat}
    (scratchAddress : Nat) (inputs outputs : Fin n → Quad) :
    (∃ producedScratch readScratch : Fin n → Quad,
      (∀ i, accepts (encode .add) (base 0)
        (inputs i) (producedScratch i)) ∧
      (∀ i, accepts (encode .add) (base 0)
        (readScratch i) (outputs i)) ∧
      (List.ofFn fun i => (scratchAddress, readScratch i)).Perm
        (List.ofFn fun i => (scratchAddress, producedScratch i))) ↔
      (List.ofFn outputs).Perm (List.ofFn inputs) := by
  constructor
  · rintro ⟨producedScratch, readScratch, hfirst, hsecond, hscratch⟩
    exact permutation_rows_sound scratchAddress inputs outputs
      producedScratch readScratch hfirst hsecond hscratch
  · exact permutation_rows_complete scratchAddress inputs outputs

def swapInputs : Fin 2 → Quad
  | ⟨0, _⟩ => base 5
  | _ => base 7

def swapOutputs : Fin 2 → Quad
  | ⟨0, _⟩ => base 7
  | _ => base 5

def forgedOutputs : Fin 2 → Quad
  | ⟨0, _⟩ => base 5
  | _ => base 8

theorem two_word_swap_accepted :
    ∃ producedScratch readScratch : Fin 2 → Quad,
      (∀ i, accepts (encode .add) (base 0)
        (swapInputs i) (producedScratch i)) ∧
      (∀ i, accepts (encode .add) (base 0)
        (readScratch i) (swapOutputs i)) ∧
      (List.ofFn fun i => (100, readScratch i)).Perm
        (List.ofFn fun i => (100, producedScratch i)) := by
  apply (permutation_rows_iff 100 swapInputs swapOutputs).mpr
  decide

theorem two_word_forgery_rejected :
    ¬ (∃ producedScratch readScratch : Fin 2 → Quad,
      (∀ i, accepts (encode .add) (base 0)
        (swapInputs i) (producedScratch i)) ∧
      (∀ i, accepts (encode .add) (base 0)
        (readScratch i) (forgedOutputs i)) ∧
      (List.ofFn fun i => (100, readScratch i)).Perm
        (List.ofFn fun i => (100, producedScratch i))) := by
  rw [permutation_rows_iff]
  decide

def isAtAddress (address : Nat) (event : GateLookup.Event) : Bool :=
  event.1 == address

theorem filter_other_addresses_nil (address : Nat)
    (events : List GateLookup.Event)
    (hother : ∀ event ∈ events, event.1 ≠ address) :
    events.filter (isAtAddress address) = [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have hhead : event.1 ≠ address := hother event (by simp)
      have htail : ∀ item ∈ rest, item.1 ≠ address := by
        intro item hmem
        exact hother item (by simp [hmem])
      simp [isAtAddress, hhead, ih htail]

theorem filter_address_self (address : Nat)
    (events : List GateLookup.Event)
    (hat : ∀ event ∈ events, event.1 = address) :
    events.filter (isAtAddress address) = events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have hhead : event.1 = address := hat event (by simp)
      have htail : ∀ item ∈ rest, item.1 = address := by
        intro item hmem
        exact hat item (by simp [hmem])
      simp [isAtAddress, hhead, ih htail]

/-- Exact global Gate balance isolates the shared scratch multiset by
filtering on one scratch address. Other permutation gates may use different
scratch addresses. -/
theorem scratch_balance_at_address
    (scratchAddress : Nat)
    (reads produced otherUses scratchUses otherYields scratchYields :
      List GateLookup.Event)
    (hbalance : reads.Perm produced)
    (huses : reads.Perm (otherUses ++ scratchUses))
    (hyields : produced.Perm (otherYields ++ scratchYields))
    (hotherUses : ∀ event ∈ otherUses, event.1 ≠ scratchAddress)
    (hotherYields : ∀ event ∈ otherYields, event.1 ≠ scratchAddress)
    (hscratchUses : ∀ event ∈ scratchUses,
      event.1 = scratchAddress)
    (hscratchYields : ∀ event ∈ scratchYields,
      event.1 = scratchAddress) :
    scratchUses.Perm scratchYields := by
  have hpartition : (otherUses ++ scratchUses).Perm
      (otherYields ++ scratchYields) :=
    huses.symm.trans (hbalance.trans hyields)
  have hfiltered := hpartition.filter (isAtAddress scratchAddress)
  simpa [List.filter_append,
    filter_other_addresses_nil scratchAddress otherUses hotherUses,
    filter_other_addresses_nil scratchAddress otherYields hotherYields,
    filter_address_self scratchAddress scratchUses hscratchUses,
    filter_address_self scratchAddress scratchYields hscratchYields]
    using hfiltered

theorem scratch_event_address {n : Nat}
    (scratchAddress : Nat)
    (values : Fin n → Quad) :
    ∀ event ∈ (List.ofFn fun i => (scratchAddress, values i)),
      event.1 = scratchAddress := by
  intro event hmem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
  rfl

/-- A global closed Gate relation forces the permutation's scratch
multiset to balance; the two add rows then force output-value permutation. -/
theorem permutation_sound_of_global_gate {n : Nat}
    (scratchAddress : Nat)
    (reads produced otherUses otherYields : List GateLookup.Event)
    (inputs outputs producedScratch readScratch : Fin n → Quad)
    (hbalance : reads.Perm produced)
    (huses : reads.Perm
      (otherUses ++
        List.ofFn fun i => (scratchAddress, readScratch i)))
    (hyields : produced.Perm
      (otherYields ++
        List.ofFn fun i => (scratchAddress, producedScratch i)))
    (hotherUses : ∀ event ∈ otherUses,
      event.1 ≠ scratchAddress)
    (hotherYields : ∀ event ∈ otherYields,
      event.1 ≠ scratchAddress)
    (hfirst : ∀ i,
      accepts (encode .add) (base 0) (inputs i) (producedScratch i))
    (hsecond : ∀ i,
      accepts (encode .add) (base 0) (readScratch i) (outputs i)) :
    (List.ofFn outputs).Perm (List.ofFn inputs) := by
  have hscratch := scratch_balance_at_address
    scratchAddress reads produced otherUses
    (List.ofFn fun i => (scratchAddress, readScratch i))
    otherYields
    (List.ofFn fun i => (scratchAddress, producedScratch i))
    hbalance huses hyields hotherUses hotherYields
    (scratch_event_address scratchAddress readScratch)
    (scratch_event_address scratchAddress producedScratch)
  exact permutation_rows_sound scratchAddress inputs outputs
    producedScratch readScratch hfirst hsecond hscratch

end S31.Gadgets.Air.PermutationRows
