import S31.Gadgets.Air.GateChallengeClosure
import S31.Gadgets.Air.GenericChipBoundary

/-!
One addressed endpoint of the current 16-row private bridge contributes
`1/16` of a Gate reciprocal in every row. Multiplying its rational closure
equation by 16 compares the sixteen committed bridge events with sixteen
copies of the circuit event. This module applies the existing Gate challenge
bound to that one-address slice. It does not yet prove the production paired
fraction AIR implies this symbolic equation or compose all eight addresses
and the chip relation into one concrete soundness bound.
-/

namespace S31.Gadgets.Air.PrivateBridgeChallenge

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallengeClosure
open S31.Gadgets.Packed

abbrev GateEvent := S31.Gadgets.Air.GateLookup.Event

def event (address : Nat) (value : S31.M31) : GateEvent :=
  (address, base (S31.Field.toZMod value))

def bridgeEvents (address : Nat) (rows : Fin 16 → S31.M31) : List GateEvent :=
  List.ofFn (fun row => event address (rows row))

def circuitEvents (address : Nat) (expected : S31.M31) : List GateEvent :=
  List.replicate 16 (event address expected)

/-- If all sixteen bridge values are the same, the weighted bridge event
multiset is exactly the circuit event repeated sixteen times. -/
theorem constant_rows_balance (address : Nat) (expected : S31.M31) :
    bridgeEvents address (fun _ => expected) =
      circuitEvents address expected := by
  simp [bridgeEvents, circuitEvents, event]

/-- Exact event balance forces every bridge row to equal the addressed
circuit value. The actual protocol obtains balance only probabilistically. -/
theorem balanced_rows_constant (address : Nat) (rows : Fin 16 → S31.M31)
    (expected : S31.M31)
    (hbalance : (bridgeEvents address rows).Perm
      (circuitEvents address expected)) :
    ∀ row, rows row = expected := by
  have h := GenericChipBoundary.averaged_bridge_rows_constant
    (fun row => event address (rows row))
    (event address expected) hbalance
  intro row
  apply S31.Field.toZMod_injective
  have heq := congrArg (fun pair : GateEvent => pair.2.a) (h row)
  simpa [event, base] using heq

private theorem canonical_events (address : Nat)
    (rows : Fin 16 → S31.M31) (expected : S31.M31)
    (haddress : address < 2147483647) :
    ∀ entry ∈ bridgeEvents address rows ++ circuitEvents address expected,
      entry.1 < 2147483647 := by
  intro entry hentry
  rcases List.mem_append.mp hentry with hbridge | hcircuit
  · obtain ⟨row, rfl⟩ := List.mem_ofFn.mp hbridge
    exact haddress
  · have heq := List.eq_of_mem_replicate hcircuit
    rw [heq]
    exact haddress

private theorem bounded_bridge_counts (address : Nat)
    (rows : Fin 16 → S31.M31) (expected : S31.M31) :
    ∀ entry ∈ bridgeEvents address rows ++ circuitEvents address expected,
      (bridgeEvents address rows).count entry < 2147483647 := by
  intro entry _
  have hcount : (bridgeEvents address rows).count entry ≤
      (bridgeEvents address rows).length := List.count_le_length
  have hlen : (bridgeEvents address rows).length = 16 := by
    simp [bridgeEvents]
  omega

private theorem bounded_circuit_counts (address : Nat)
    (rows : Fin 16 → S31.M31) (expected : S31.M31) :
    ∀ entry ∈ bridgeEvents address rows ++ circuitEvents address expected,
      (circuitEvents address expected).count entry < 2147483647 := by
  intro entry _
  have hcount : (circuitEvents address expected).count entry ≤
      (circuitEvents address expected).length := List.count_le_length
  have hlen : (circuitEvents address expected).length = 16 := by
    simp [circuitEvents]
  omega

/-- For one fixed Gate address, any row-varying bridge endpoint can satisfy
the ideal random-challenge reciprocal closure only on the established small
exceptional set. The bound's support size counts distinct *canonical* Gate
events among the sixteen bridge rows and the circuit event. -/
theorem varying_rows_false_closure_bound
    (address : Nat) (rows : Fin 16 → S31.M31)
    (expected : S31.M31)
    (haddress : address < 2147483647)
    (hvaries : ∃ row, rows row ≠ expected) :
    (closingPairs [] (bridgeEvents address rows)
      (circuitEvents address expected)).card ≤
      (5 * (bridgeEvents address rows ++
        circuitEvents address expected).toFinset.card ^ 2 +
        2 * (bridgeEvents address rows ++
          circuitEvents address expected).toFinset.card) *
        Fintype.card S31.Gadgets.Air.GateChallenge.GateSecure := by
  have hwrong : ¬ (bridgeEvents address rows).Perm
      (circuitEvents address expected) := by
    intro hbalance
    obtain ⟨row, hne⟩ := hvaries
    exact hne (balanced_rows_constant address rows expected hbalance row)
  simpa [allUses, allYields] using
    (false_closing_pairs_card_le []
      (bridgeEvents address rows) (circuitEvents address expected)
      (by simpa [allUses, allYields] using
        canonical_events address rows expected haddress)
      (by simpa [allUses, allYields] using
        bounded_bridge_counts address rows expected)
      (by simpa [allUses, allYields] using
        bounded_circuit_counts address rows expected)
      (by simpa [allUses, allYields] using hwrong))

/-- All eight Gate endpoints of the current private bridge, with one
sixteen-row slice per compiler-selected address. This represents the ideal
unweighted event equation obtained by clearing the common `1/16` factor. -/
def allBridgeEvents (addresses : Fin 8 → Nat)
    (rows : Fin 8 → Fin 16 → S31.M31) : List GateEvent :=
  (List.ofFn (fun lane : Fin 8 => lane)).flatMap
    (fun lane => bridgeEvents (addresses lane) (rows lane))

def allCircuitEvents (addresses : Fin 8 → Nat)
    (expected : Fin 8 → S31.M31) : List GateEvent :=
  (List.ofFn (fun lane : Fin 8 => lane)).flatMap
    (fun lane => circuitEvents (addresses lane) (expected lane))

/-- With unique compiler-selected addresses, one wrong bridge row makes the
entire eight-address event multiset wrong. This excludes cancellation across
different endpoint addresses at the ideal multiset level. -/
theorem wrong_row_breaks_joint_balance
    (addresses : Fin 8 → Nat) (rows : Fin 8 → Fin 16 → S31.M31)
    (expected : Fin 8 → S31.M31)
    (haddresses : Function.Injective addresses)
    (lane : Fin 8) (row : Fin 16)
    (hwrong : rows lane row ≠ expected lane) :
    ¬ (allBridgeEvents addresses rows).Perm
      (allCircuitEvents addresses expected) := by
  intro hbalance
  have hmember : event (addresses lane) (rows lane row) ∈
      allBridgeEvents addresses rows := by
    apply List.mem_flatMap.mpr
    exact ⟨lane, List.mem_ofFn.mpr ⟨lane, rfl⟩,
      List.mem_ofFn.mpr ⟨row, rfl⟩⟩
  have hcircuit := hbalance.mem_iff.mp hmember
  obtain ⟨other, _, hother⟩ := List.mem_flatMap.mp hcircuit
  have hevent : event (addresses lane) (rows lane row) =
      event (addresses other) (expected other) := by
    simpa [circuitEvents] using
      (List.eq_of_mem_replicate hother)
  have haddress : lane = other := haddresses
    (congrArg Prod.fst hevent)
  subst other
  have hvalue := congrArg (fun pair : GateEvent => pair.2.a) hevent
  exact hwrong (S31.Field.toZMod_injective (by
    simpa [event, base] using hvalue))

private theorem all_bridge_length
    (addresses : Fin 8 → Nat) (rows : Fin 8 → Fin 16 → S31.M31) :
    (allBridgeEvents addresses rows).length = 128 := by
  simp [allBridgeEvents, bridgeEvents]

private theorem all_circuit_length
    (addresses : Fin 8 → Nat) (expected : Fin 8 → S31.M31) :
    (allCircuitEvents addresses expected).length = 128 := by
  simp [allCircuitEvents, circuitEvents]

private theorem all_events_canonical
    (addresses : Fin 8 → Nat) (rows : Fin 8 → Fin 16 → S31.M31)
    (expected : Fin 8 → S31.M31)
    (haddresses : ∀ lane, addresses lane < 2147483647) :
    ∀ entry ∈ allBridgeEvents addresses rows ++
      allCircuitEvents addresses expected,
      entry.1 < 2147483647 := by
  intro entry hentry
  rcases List.mem_append.mp hentry with hbridge | hcircuit
  · obtain ⟨lane, _, hrow⟩ := List.mem_flatMap.mp hbridge
    obtain ⟨row, rfl⟩ := List.mem_ofFn.mp hrow
    exact haddresses lane
  · obtain ⟨lane, _, hrow⟩ := List.mem_flatMap.mp hcircuit
    have heq := List.eq_of_mem_replicate hrow
    rw [heq]
    exact haddresses lane

/-- Under distinct canonical addresses, one incorrect row in any of the
eight bridge endpoints makes the **joint Gate** reciprocal closure a false
identity except for the same explicit finite-field challenge exceptional
set as the generic Gate theorem. The production AIR-to-rational and chip
closure links remain separate obligations. -/
theorem joint_eight_address_false_closure_bound
    (addresses : Fin 8 → Nat) (rows : Fin 8 → Fin 16 → S31.M31)
    (expected : Fin 8 → S31.M31)
    (haddresses : Function.Injective addresses)
    (hcanonical : ∀ lane, addresses lane < 2147483647)
    (lane : Fin 8) (row : Fin 16)
    (hwrong : rows lane row ≠ expected lane) :
    (closingPairs [] (allBridgeEvents addresses rows)
      (allCircuitEvents addresses expected)).card ≤
      (5 * (allBridgeEvents addresses rows ++
        allCircuitEvents addresses expected).toFinset.card ^ 2 +
       2 * (allBridgeEvents addresses rows ++
        allCircuitEvents addresses expected).toFinset.card) *
      Fintype.card S31.Gadgets.Air.GateChallenge.GateSecure := by
  have hwrongBalance := wrong_row_breaks_joint_balance addresses rows
    expected haddresses lane row hwrong
  have hbridgeCount :
      ∀ entry ∈ allBridgeEvents addresses rows ++
        allCircuitEvents addresses expected,
        (allBridgeEvents addresses rows).count entry < 2147483647 := by
    intro entry _
    have hcount : (allBridgeEvents addresses rows).count entry ≤
        (allBridgeEvents addresses rows).length := List.count_le_length
    rw [all_bridge_length] at hcount
    omega
  have hcircuitCount :
      ∀ entry ∈ allBridgeEvents addresses rows ++
        allCircuitEvents addresses expected,
        (allCircuitEvents addresses expected).count entry < 2147483647 := by
    intro entry _
    have hcount : (allCircuitEvents addresses expected).count entry ≤
        (allCircuitEvents addresses expected).length := List.count_le_length
    rw [all_circuit_length] at hcount
    omega
  simpa [allUses, allYields] using
    (false_closing_pairs_card_le []
      (allBridgeEvents addresses rows)
      (allCircuitEvents addresses expected)
      (by simpa [allUses, allYields] using
        all_events_canonical addresses rows expected hcanonical)
      (by simpa [allUses, allYields] using hbridgeCount)
      (by simpa [allUses, allYields] using hcircuitCount)
      (by simpa [allUses, allYields] using hwrongBalance))

end S31.Gadgets.Air.PrivateBridgeChallenge
