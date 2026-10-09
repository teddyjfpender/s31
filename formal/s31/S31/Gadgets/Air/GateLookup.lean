import S31.Gadgets.Air.Qm31Ops

/-!
An ideal, exact-multiset model of the circuit Gate relation. In production,
the row contributes two positive input tuples and a negative output tuple
weighted by its preprocessed multiplicity. The public statement and other
components contribute further events. This model assumes exact multiset
balance; proving the probabilistic LogUp argument and the compiler's producer
uniqueness are separate obligations.
-/

namespace S31.Gadgets.Air.GateLookup

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- The relation id is fixed for this component; the remaining tuple is the
preprocessed address and four committed M31 limbs. -/
abbrev Event := Nat × Quad

structure Row where
  in0Address : Nat
  in1Address : Nat
  outAddress : Nat
  flags : Flags
  in0 : Quad
  in1 : Quad
  output : Quad
  multiplicity : Nat

def Row.uses (r : Row) : List Event :=
  [(r.in0Address, r.in0), (r.in1Address, r.in1)]

def Row.yields (r : Row) : List Event :=
  List.replicate r.multiplicity (r.outAddress, r.output)

def allUses (rows : List Row) (external : List Event) : List Event :=
  rows.flatMap Row.uses ++ external

def allYields (rows : List Row) (external : List Event) : List Event :=
  rows.flatMap Row.yields ++ external

/-- The ideal meaning of a closed Gate relation, before lookup compression. -/
def balanced (rows : List Row) (externalUses externalYields : List Event) : Prop :=
  (allUses rows externalUses).Perm (allYields rows externalYields)

/-- A circuit address has one produced packed value, even if its event appears
several times to account for multiplicity. -/
def uniqueProduced (produced : List Event) : Prop :=
  ∀ address left right,
    (address, left) ∈ produced →
    (address, right) ∈ produced → left = right

theorem balanced_read_matches (reads produced : List Event)
    (hbalance : reads.Perm produced)
    (hunique : uniqueProduced produced)
    (address : Nat) (read value : Quad)
    (hread : (address, read) ∈ reads)
    (hvalue : (address, value) ∈ produced) :
    read = value := by
  exact hunique address read value (hbalance.mem_iff.mp hread) hvalue

theorem row_input_use (rows : List Row) (external : List Event)
    (r : Row) (hr : r ∈ rows) :
    (r.in0Address, r.in0) ∈ allUses rows external ∧
    (r.in1Address, r.in1) ∈ allUses rows external := by
  constructor
  · apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [Row.uses]⟩
  · apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [Row.uses]⟩

/-- A zero-multiplicity output is not yielded to Gate. A positive
multiplicity makes the row's output available to later input lookups. -/
theorem row_output_yield (rows : List Row) (external : List Event)
    (r : Row) (hr : r ∈ rows) (hm : 0 < r.multiplicity) :
    (r.outAddress, r.output) ∈ allYields rows external := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  simp [Row.yields, Nat.ne_of_gt hm]

/-- An input trace value different from the unique producer value prevents
exact Gate multiset closure, even if the row's arithmetic equation holds. -/
theorem forged_input_rejected (rows : List Row)
    (externalUses externalYields : List Event)
    (r : Row) (hr : r ∈ rows)
    (hunique : uniqueProduced (allYields rows externalYields))
    (expected : Quad)
    (hexpected : (r.in0Address, expected) ∈
      allYields rows externalYields)
    (hforged : r.in0 ≠ expected) :
    ¬ balanced rows externalUses externalYields := by
  intro hbalance
  exact hforged (balanced_read_matches _ _ hbalance hunique
    r.in0Address r.in0 expected
    (row_input_use rows externalUses r hr).1 hexpected)

/-- Under exact Gate balance and a unique produced value at each address,
both local row operands are forced to the circuit's produced values. The
nine AIR constraints then force the row output to their selected operation. -/
theorem addressed_row_sound (rows : List Row)
    (externalUses externalYields : List Event)
    (r : Row) (hr : r ∈ rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (left right : Quad)
    (hleft : (r.in0Address, left) ∈ allYields rows externalYields)
    (hright : (r.in1Address, right) ∈ allYields rows externalYields)
    (hair : accepts r.flags r.in0 r.in1 r.output) :
    ∃ op, r.flags = encode op ∧ r.output = evaluate op left right := by
  obtain ⟨huse0, huse1⟩ := row_input_use rows externalUses r hr
  have h0 := balanced_read_matches _ _ hbalance hunique
    r.in0Address r.in0 left huse0 hleft
  have h1 := balanced_read_matches _ _ hbalance hunique
    r.in1Address r.in1 right huse1 hright
  obtain ⟨op, hflags, hout⟩ := (accepts_iff _ _ _ _).mp hair
  exact ⟨op, hflags, by simpa [h0, h1] using hout⟩

end S31.Gadgets.Air.GateLookup
