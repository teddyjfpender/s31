import S31.Gadgets.Air.GateLookup

namespace S31.Gadgets.Air.GateProducerCheck
open S31.Gadgets.Air.GateLookup

/-- Model of the preprocessed builder's declared-variable address scan. It
rejects an out-of-range output or a second producer at an already seen
address. Permutation scratch addresses are handled separately. -/
def scan (bound : Nat) (seen : Finset Nat) :
    List Nat → Option (Finset Nat)
  | [] => some seen
  | address :: rest =>
      if address < bound then
        if address ∈ seen then none
        else scan bound (insert address seen) rest
      else none

theorem scan_sound {bound : Nat} {seen : Finset Nat}
    {addresses : List Nat} {result : Finset Nat}
    (hscan : scan bound seen addresses = some result) :
    addresses.Nodup ∧
      ∀ address ∈ addresses, address < bound ∧ address ∉ seen := by
  induction addresses generalizing seen with
  | nil =>
      constructor
      · simp
      · intro address hmem
        simp at hmem
  | cons head tail ih =>
      by_cases hbound : head < bound
      · by_cases hseen : head ∈ seen
        · simp [scan, hbound, hseen] at hscan
        · have htail : scan bound (insert head seen) tail = some result := by
            simpa [scan, hbound, hseen] using hscan
          obtain ⟨hnodup, hrest⟩ := ih htail
          have hhead : head ∉ tail := by
            intro hmem
            exact (hrest head hmem).2 (Finset.mem_insert_self _ _)
          constructor
          · exact List.nodup_cons.mpr ⟨hhead, hnodup⟩
          · intro address hmem
            rcases List.mem_cons.mp hmem with heq | htailmem
            · subst address
              exact ⟨hbound, hseen⟩
            · obtain ⟨haddress, hnotInsert⟩ := hrest address htailmem
              exact ⟨haddress, fun hin =>
                hnotInsert (Finset.mem_insert_of_mem hin)⟩
      · simp [scan, hbound] at hscan

/-- Successful checking of one produced-event list discharges uniqueness
and range premises for that list. -/
theorem checked_produced_unique (bound : Nat)
    (produced : List Event) (result : Finset Nat)
    (hscan : scan bound ∅ (produced.map Prod.fst) = some result) :
    uniqueProduced produced ∧
      ∀ event ∈ produced, event.1 < bound := by
  obtain ⟨hnodup, hbound⟩ := scan_sound hscan
  constructor
  · intro address left right hleft hright
    have heq : (address, left) = (address, right) :=
      (List.inj_on_of_nodup_map hnodup) hleft hright rfl
    exact congrArg Prod.snd heq
  · intro event hmem
    exact (hbound event.1 (List.mem_map_of_mem hmem)).1

theorem duplicate_addresses_rejected (bound address : Nat)
    (hbound : address < bound) :
    scan bound ∅ [address, address] = none := by
  simp [scan, hbound]

/-- Scratch producers can share addresses, but they cannot shadow a declared
variable because their addresses start at or above the declared bound. -/
theorem checked_declared_unique_with_scratch
    (bound : Nat) (declared scratch : List Event)
    (result : Finset Nat)
    (hscan : scan bound ∅ (declared.map Prod.fst) = some result)
    (hscratch : ∀ event ∈ scratch, bound ≤ event.1)
    (address : Nat) (haddress : address < bound)
    (left right : S31.Gadgets.Packed.Quad)
    (hleft : (address, left) ∈ declared ++ scratch)
    (hright : (address, right) ∈ declared ++ scratch) :
    left = right := by
  have hunique := (checked_produced_unique bound declared result hscan).1
  have hdeclaredLeft : (address, left) ∈ declared := by
    rcases List.mem_append.mp hleft with h | h
    · exact h
    · exact False.elim (Nat.not_le_of_gt haddress (hscratch _ h))
  have hdeclaredRight : (address, right) ∈ declared := by
    rcases List.mem_append.mp hright with h | h
    · exact h
    · exact False.elim (Nat.not_le_of_gt haddress (hscratch _ h))
  exact hunique address left right hdeclaredLeft hdeclaredRight

/-- An ordinary row reading declared addresses remains sound even when
permutation scratch addresses have several producer rows. -/
theorem addressed_declared_row_sound
    (bound : Nat) (rows : List Row)
    (externalUses externalYields declared scratch : List Event)
    (result : Finset Nat)
    (hproduced : (allYields rows externalYields).Perm
      (declared ++ scratch))
    (hscan : scan bound ∅ (declared.map Prod.fst) = some result)
    (hscratch : ∀ event ∈ scratch, bound ≤ event.1)
    (hbalance : balanced rows externalUses externalYields)
    (row : Row) (hrow : row ∈ rows)
    (haddress0 : row.in0Address < bound)
    (haddress1 : row.in1Address < bound)
    (left right : S31.Gadgets.Packed.Quad)
    (hleft : (row.in0Address, left) ∈ allYields rows externalYields)
    (hright : (row.in1Address, right) ∈ allYields rows externalYields)
    (hair : Qm31Ops.accepts row.flags row.in0 row.in1 row.output) :
    ∃ op, row.flags = Qm31Ops.encode op ∧
      row.output = Qm31Ops.evaluate op left right := by
  obtain ⟨huse0, huse1⟩ := row_input_use rows externalUses row hrow
  have hread0 : (row.in0Address, row.in0) ∈
      allYields rows externalYields := hbalance.mem_iff.mp huse0
  have hread1 : (row.in1Address, row.in1) ∈
      allYields rows externalYields := hbalance.mem_iff.mp huse1
  have hread0' := hproduced.mem_iff.mp hread0
  have hread1' := hproduced.mem_iff.mp hread1
  have hleft' := hproduced.mem_iff.mp hleft
  have hright' := hproduced.mem_iff.mp hright
  have h0 := checked_declared_unique_with_scratch bound declared scratch
    result hscan hscratch row.in0Address haddress0 row.in0 left
    hread0' hleft'
  have h1 := checked_declared_unique_with_scratch bound declared scratch
    result hscan hscratch row.in1Address haddress1 row.in1 right
    hread1' hright'
  obtain ⟨op, hflags, hout⟩ :=
    (Qm31Ops.accepts_iff _ _ _ _).mp hair
  exact ⟨op, hflags, by simpa [h0, h1] using hout⟩

end S31.Gadgets.Air.GateProducerCheck
