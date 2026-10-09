import S31.Gadgets.Air.GateLookup

namespace S31.Gadgets.Air.GateProducerCheck
open S31.Gadgets.Air.GateLookup

/-- Model of the preprocessed builder's address bitmap scan. The scan rejects
an out-of-range output or a second producer at an already seen address. -/
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

/-- Successful checking of produced addresses discharges both uniqueness
and canonical-range premises for the exact Gate address join. -/
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

theorem addressed_row_sound_of_scan
    (bound : Nat) (rows : List Row)
    (externalUses externalYields : List Event)
    (result : Finset Nat)
    (hscan : scan bound ∅
      ((allYields rows externalYields).map Prod.fst) = some result)
    (hbalance : balanced rows externalUses externalYields)
    (row : Row) (hrow : row ∈ rows)
    (left right : S31.Gadgets.Packed.Quad)
    (hleft : (row.in0Address, left) ∈
      allYields rows externalYields)
    (hright : (row.in1Address, right) ∈
      allYields rows externalYields)
    (hair : Qm31Ops.accepts row.flags row.in0 row.in1 row.output) :
    ∃ op, row.flags = Qm31Ops.encode op ∧
      row.output = Qm31Ops.evaluate op left right := by
  exact addressed_row_sound rows externalUses externalYields row hrow
    hbalance
    (checked_produced_unique bound _ result hscan).1
    left right hleft hright hair

end S31.Gadgets.Air.GateProducerCheck
