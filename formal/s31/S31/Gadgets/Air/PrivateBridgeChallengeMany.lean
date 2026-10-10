import S31.Gadgets.Air.PrivateBridgeChallenge

/-!
Finite families of sixteen-row private bridge endpoints. The theorem counts
the exceptional challenge pairs for an incorrect committed endpoint under
coherent expected producer values at repeated addresses. It is a theorem
about the ideal rational Gate closure model, not a proof that the production
paired-fraction AIR implies it or that PCS enforces the committed rows.
-/

namespace S31.Gadgets.Air.PrivateBridgeChallengeMany

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallengeClosure
open S31.Gadgets.Air.PrivateBridgeChallenge

def bridgeEventsN {n : Nat} (addresses : Fin n → Nat)
    (rows : Fin n → Fin 16 → S31.M31) : List GateEvent :=
  (List.ofFn (fun lane : Fin n => lane)).flatMap
    (fun lane => bridgeEvents (addresses lane) (rows lane))

def circuitEventsN {n : Nat} (addresses : Fin n → Nat)
    (expected : Fin n → S31.M31) : List GateEvent :=
  (List.ofFn (fun lane : Fin n => lane)).flatMap
    (fun lane => circuitEvents (addresses lane) (expected lane))

/-- Repeated endpoint addresses are safe when the expected producer value is
coherent: a wrong bridge value cannot occur in the circuit event multiset. -/
theorem wrong_row_breaks_joint_balance {n : Nat}
    (addresses : Fin n → Nat) (rows : Fin n → Fin 16 → S31.M31)
    (expected : Fin n → S31.M31)
    (hcoherent : ∀ left right,
      addresses left = addresses right → expected left = expected right)
    (lane : Fin n) (row : Fin 16)
    (hwrong : rows lane row ≠ expected lane) :
    ¬ (bridgeEventsN addresses rows).Perm
      (circuitEventsN addresses expected) := by
  intro hbalance
  have hmember : event (addresses lane) (rows lane row) ∈
      bridgeEventsN addresses rows := by
    apply List.mem_flatMap.mpr
    exact ⟨lane, List.mem_ofFn.mpr ⟨lane, rfl⟩,
      List.mem_ofFn.mpr ⟨row, rfl⟩⟩
  have hcircuit := hbalance.mem_iff.mp hmember
  obtain ⟨other, _, hother⟩ := List.mem_flatMap.mp hcircuit
  have hevent : event (addresses lane) (rows lane row) =
      event (addresses other) (expected other) := by
    simpa [circuitEventsN] using
      (List.eq_of_mem_replicate hother)
  have haddress : addresses lane = addresses other :=
    congrArg Prod.fst hevent
  have hexpected : expected lane = expected other :=
    hcoherent lane other haddress
  have hvalue := congrArg (fun pair : GateEvent => pair.2.a) hevent
  exact hwrong ((S31.Field.toZMod_injective (by
    simpa [event, S31.Gadgets.Packed.base] using hvalue)).trans
    hexpected.symm)

private theorem bridge_length {n : Nat}
    (addresses : Fin n → Nat) (rows : Fin n → Fin 16 → S31.M31) :
    (bridgeEventsN addresses rows).length = n * 16 := by
  simp [bridgeEventsN, bridgeEvents]
  change (List.ofFn (fun _ : Fin n => (16 : Nat))).sum = n * 16
  rw [List.ofFn_const, List.sum_replicate_nat]

private theorem circuit_length {n : Nat}
    (addresses : Fin n → Nat) (expected : Fin n → S31.M31) :
    (circuitEventsN addresses expected).length = n * 16 := by
  simp [circuitEventsN, circuitEvents]
  change (List.ofFn (fun _ : Fin n => (16 : Nat))).sum = n * 16
  rw [List.ofFn_const, List.sum_replicate_nat]

private theorem events_canonical {n : Nat}
    (addresses : Fin n → Nat) (rows : Fin n → Fin 16 → S31.M31)
    (expected : Fin n → S31.M31)
    (haddresses : ∀ lane, addresses lane < 2147483647) :
    ∀ entry ∈ bridgeEventsN addresses rows ++
      circuitEventsN addresses expected,
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

/-- For any finite number of bridge endpoints with fewer than the M31
characteristic many total rows, one wrong row can close only on the explicit
exceptional set. The support size counts distinct canonical Gate events. -/
theorem false_closure_bound {n : Nat}
    (addresses : Fin n → Nat) (rows : Fin n → Fin 16 → S31.M31)
    (expected : Fin n → S31.M31)
    (hcoherent : ∀ left right,
      addresses left = addresses right → expected left = expected right)
    (hcanonical : ∀ lane, addresses lane < 2147483647)
    (hrows : n * 16 < 2147483647)
    (lane : Fin n) (row : Fin 16)
    (hwrong : rows lane row ≠ expected lane) :
    (closingPairs [] (bridgeEventsN addresses rows)
      (circuitEventsN addresses expected)).card ≤
      (5 * (bridgeEventsN addresses rows ++
        circuitEventsN addresses expected).toFinset.card ^ 2 +
       2 * (bridgeEventsN addresses rows ++
        circuitEventsN addresses expected).toFinset.card) *
      Fintype.card S31.Gadgets.Air.GateChallenge.GateSecure := by
  have hwrongBalance := wrong_row_breaks_joint_balance addresses rows
    expected hcoherent lane row hwrong
  have hbridgeCount :
      ∀ entry ∈ bridgeEventsN addresses rows ++
        circuitEventsN addresses expected,
        (bridgeEventsN addresses rows).count entry < 2147483647 := by
    intro entry _
    have hcount : (bridgeEventsN addresses rows).count entry ≤
        (bridgeEventsN addresses rows).length := List.count_le_length
    rw [bridge_length] at hcount
    omega
  have hcircuitCount :
      ∀ entry ∈ bridgeEventsN addresses rows ++
        circuitEventsN addresses expected,
        (circuitEventsN addresses expected).count entry < 2147483647 := by
    intro entry _
    have hcount : (circuitEventsN addresses expected).count entry ≤
        (circuitEventsN addresses expected).length := List.count_le_length
    rw [circuit_length] at hcount
    omega
  simpa [allUses, allYields] using
    (false_closing_pairs_card_le []
      (bridgeEventsN addresses rows)
      (circuitEventsN addresses expected)
      (by simpa [allUses, allYields] using
        events_canonical addresses rows expected hcanonical)
      (by simpa [allUses, allYields] using hbridgeCount)
      (by simpa [allUses, allYields] using hcircuitCount)
      (by simpa [allUses, allYields] using hwrongBalance))

/-- Sixteen endpoints model two eight-endpoint bridge calls, including any
reused address whose producer value is coherent across both calls. There are
at most 512 distinct events, hence the numerical exceptional-pair factor
`5·512² + 2·512 = 1,311,744`. -/
theorem sixteen_endpoint_false_closure_bound
    (addresses : Fin 16 → Nat)
    (rows : Fin 16 → Fin 16 → S31.M31)
    (expected : Fin 16 → S31.M31)
    (hcoherent : ∀ left right,
      addresses left = addresses right → expected left = expected right)
    (hcanonical : ∀ lane, addresses lane < 2147483647)
    (lane : Fin 16) (row : Fin 16)
    (hwrong : rows lane row ≠ expected lane) :
    (closingPairs [] (bridgeEventsN addresses rows)
      (circuitEventsN addresses expected)).card ≤
      1311744 *
      Fintype.card S31.Gadgets.Air.GateChallenge.GateSecure := by
  let support :=
    (bridgeEventsN addresses rows ++
      circuitEventsN addresses expected).toFinset.card
  have hlen :
      (bridgeEventsN addresses rows ++
        circuitEventsN addresses expected).length = 512 := by
    simp [bridge_length, circuit_length]
  have hsupport : support ≤ 512 := by
    exact (List.toFinset_card_le _).trans (by rw [hlen])
  have hsquare : support ^ 2 ≤ 512 ^ 2 :=
    Nat.pow_le_pow_left hsupport 2
  have hpoly : 5 * support ^ 2 + 2 * support ≤ 1311744 := by
    omega
  have hmain := false_closure_bound addresses rows expected
    hcoherent hcanonical (by decide) lane row hwrong
  exact hmain.trans
    (Nat.mul_le_mul_right
      (Fintype.card S31.Gadgets.Air.GateChallenge.GateSecure)
      hpoly)

end S31.Gadgets.Air.PrivateBridgeChallengeMany
