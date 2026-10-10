import S31.Gadgets.Air.TaggedPairChallenge
import Mathlib.Tactic

/-!
Source-shaped algebra for the tagged pair chip and bridge interaction AIR.
A verifier-accepted AIR premise here means the row residuals vanish on every
logical trace row with the specified cyclic predecessor permutation. It is
not derived from PCS/FRI openings or Fiat–Shamir in this module.
-/

namespace S31.Gadgets.Air.TaggedPairAirClosure

open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.GateChallenge

variable {K : Type*} [Field K]

/-- Exactly the two secure running-sum residuals in
`tagged_pair_chip.zig::rowConstraints`, after unpacking the secure column.
The first interaction column is row-local. The final one has a cyclic
predecessor mask and the verifier-supplied `claimed_sum / R` shift. -/
def ChipAccepted {R : Nat} (previous : Fin R ≃ Fin R)
    (qin qout first current : Fin R → K) (claim : K) : Prop :=
  ∀ row : Fin R,
    first row * qin row = 1 ∧
    ((current row - current (previous row) - first row +
      claim / (R : K)) * qout row + 1 = 0)

private theorem eq_inv_of_mul_eq_one (a b : K)
    (hb : b ≠ 0) (hab : a * b = 1) : a = b⁻¹ := by
  calc
    a = a * (b * b⁻¹) := by simp [hb]
    _ = (a * b) * b⁻¹ := by ring
    _ = b⁻¹ := by rw [hab]; ring

private theorem eq_neg_inv_of_mul_eq_neg_one (a b : K)
    (hb : b ≠ 0) (hab : a * b = -1) : a = -b⁻¹ := by
  calc
    a = a * (b * b⁻¹) := by simp [hb]
    _ = (a * b) * b⁻¹ := by ring
    _ = -b⁻¹ := by rw [hab]; ring

/-- Each chip AIR row contributes precisely its signed input/output event
fractions when both denominators are nonzero. -/
theorem chip_air_row_fraction {R : Nat} (previous : Fin R ≃ Fin R)
    (qin qout first current : Fin R → K) (claim : K)
    (haccepted : ChipAccepted previous qin qout first current claim)
    (hqin : ∀ row, qin row ≠ 0)
    (hqout : ∀ row, qout row ≠ 0)
    (row : Fin R) :
    current row - current (previous row) + claim / (R : K) =
      (qin row)⁻¹ - (qout row)⁻¹ := by
  obtain ⟨hfirst, hlast⟩ := haccepted row
  have hfirstEq : first row = (qin row)⁻¹ :=
    eq_inv_of_mul_eq_one _ _ (hqin row) hfirst
  let delta := current row - current (previous row) - first row +
    claim / (R : K)
  have hdeltaMul : delta * qout row = -1 := by
    dsimp [delta]
    linear_combination hlast
  have hdeltaEq : delta = -(qout row)⁻¹ :=
    eq_neg_inv_of_mul_eq_neg_one _ _ (hqout row) hdeltaMul
  calc
    current row - current (previous row) + claim / (R : K) =
      first row + delta := by dsimp [delta]; ring
    _ = (qin row)⁻¹ - (qout row)⁻¹ := by rw [hfirstEq, hdeltaEq]; ring

/-- Cyclic telescoping recovers the chip's claimed sum from its AIR row
residuals. Row order need not be canonical; only the predecessor mask must
permute all logical rows exactly once. -/
theorem chip_air_claim_eq_reciprocal_sum {R : Nat}
    (previous : Fin R ≃ Fin R)
    (qin qout first current : Fin R → K) (claim : K)
    (hR : (R : K) ≠ 0)
    (haccepted : ChipAccepted previous qin qout first current claim)
    (hqin : ∀ row, qin row ≠ 0)
    (hqout : ∀ row, qout row ≠ 0) :
    claim = ∑ row : Fin R, ((qin row)⁻¹ - (qout row)⁻¹) := by
  have hrows :
      (∑ row : Fin R,
        (current row - current (previous row) + claim / (R : K))) =
      ∑ row : Fin R, ((qin row)⁻¹ - (qout row)⁻¹) := by
    apply Finset.sum_congr rfl
    intro row _
    exact chip_air_row_fraction previous qin qout first current
      claim haccepted hqin hqout row
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hrows
  rw [Equiv.sum_comp previous current] at hrows
  have hshift : (R : K) * (claim / (R : K)) = claim := by
    field_simp
  simpa [hshift] using hrows

/-- The predecessor permutation premise is necessary. With both rows
reading row zero as their predecessor, all source-shaped chip residuals can
vanish with nonzero denominators while the claimed sum differs from the
sum of row fractions. The actual native mask is intended to be cyclic; its
correspondence to the logical rows remains an external obligation. -/
theorem nonbijective_previous_counterexample :
    (∀ row : Fin 2,
      (1 : ℚ) * 1 = 1 ∧
      (((if row = 0 then (0 : ℚ) else 1) - 0 - 1 + 4 / 2) *
        (if row = 0 then (-1 : ℚ) else -(1 / 2)) + 1 = 0)) ∧
    (4 : ℚ) ≠ ∑ row : Fin 2,
      ((1 : ℚ)⁻¹ -
        (if row = 0 then (-1 : ℚ) else -(1 / 2))⁻¹) := by
  constructor
  · intro row
    fin_cases row <;> norm_num
  · simp [Fin.sum_univ_succ]
    norm_num

/-- Bind a chip's two AIR denominators to the native seven-word event
tuples for arbitrary witness step order. -/
theorem chip_air_claim_eq_event_sums {R : Nat}
    (previous : Fin R ≃ Fin R)
    (input output : Fin R → JointTuple)
    (qin qout first current : Fin R → GateSecure)
    (claim alpha z : GateSecure)
    (hR : (R : GateSecure) ≠ 0)
    (haccepted : ChipAccepted previous qin qout first current claim)
    (hqin : ∀ row, qin row = combine7 (input row) alpha z)
    (hqout : ∀ row, qout row = combine7 (output row) alpha z)
    (hnonzeroIn : ∀ row, qin row ≠ 0)
    (hnonzeroOut : ∀ row, qout row ≠ 0) :
    claim =
      productionReciprocalSum7 (List.ofFn input) alpha z -
      productionReciprocalSum7 (List.ofFn output) alpha z := by
  rw [chip_air_claim_eq_reciprocal_sum previous qin qout first current
    claim hR haccepted hnonzeroIn hnonzeroOut]
  simp only [productionReciprocalSum7, List.map_ofFn, List.sum_ofFn,
    Finset.sum_sub_distrib]
  have hin : (∑ row : Fin R, (qin row)⁻¹) =
      ∑ row : Fin R, 1 / combine7 (input row) alpha z := by
    apply Finset.sum_congr rfl
    intro row _
    simp [hqin row, div_eq_mul_inv]
  have hout : (∑ row : Fin R, (qout row)⁻¹) =
      ∑ row : Fin R, 1 / combine7 (output row) alpha z := by
    apply Finset.sum_congr rfl
    intro row _
    simp [hqout row, div_eq_mul_inv]
  exact congrArg₂ Sub.sub hin hout

private theorem eq_div_of_mul_sub_eq_zero (a denominator numerator : K)
    (hden : denominator ≠ 0)
    (hresidual : a * denominator - numerator = 0) :
    a = numerator / denominator := by
  apply (eq_div_iff hden).2
  exact sub_eq_zero.mp hresidual

/-- Native paired Gate fraction for one of four bridge slots in one row. -/
def bridgeGateTerm (d0 d1 : Fin 4 → Fin 16 → K)
    (slot : Fin 4) (row : Fin 16) : K :=
  ((d0 slot row + d1 slot row) / 16) /
    (d0 slot row * d1 slot row)

/-- Native paired chip start/end fraction in one bridge row. -/
def bridgeChipTerm (first last : Fin 16 → K)
    (row : Fin 16) : K :=
  ((first row - last row) / 16) / (first row * last row)

def bridgeRowTerm (d0 d1 : Fin 4 → Fin 16 → K)
    (first last : Fin 16 → K) (row : Fin 16) : K :=
  bridgeGateTerm d0 d1 0 row +
  bridgeGateTerm d0 d1 1 row +
  bridgeGateTerm d0 d1 2 row +
  bridgeGateTerm d0 d1 3 row +
  bridgeChipTerm first last row

/-- The five interaction residuals in
`tagged_pair_bridge.zig::rowConstraints` after unpacking secure columns.
The eight main-column `current-next=0` equations are handled separately by
`TaggedPairBridgeRows`; they make the denominators constant across rows. -/
def BridgeAccepted (previous : Fin 16 ≃ Fin 16)
    (d0 d1 : Fin 4 → Fin 16 → K) (first last : Fin 16 → K)
    (current : Fin 5 → Fin 16 → K) (claim : K) : Prop :=
  ∀ row : Fin 16,
    current 0 row * (d0 0 row * d1 0 row) -
      (d0 0 row + d1 0 row) / 16 = 0 ∧
    (current 1 row - current 0 row) * (d0 1 row * d1 1 row) -
      (d0 1 row + d1 1 row) / 16 = 0 ∧
    (current 2 row - current 1 row) * (d0 2 row * d1 2 row) -
      (d0 2 row + d1 2 row) / 16 = 0 ∧
    (current 3 row - current 2 row) * (d0 3 row * d1 3 row) -
      (d0 3 row + d1 3 row) / 16 = 0 ∧
    (current 4 row - current 4 (previous row) - current 3 row +
      claim / 16) * (first row * last row) -
      (first row - last row) / 16 = 0

/-- The five bridge residuals recover that row's four Gate pairs and one
chip start/end pair as rational fractions. -/
theorem bridge_air_row_fraction (previous : Fin 16 ≃ Fin 16)
    (d0 d1 : Fin 4 → Fin 16 → K) (first last : Fin 16 → K)
    (current : Fin 5 → Fin 16 → K) (claim : K)
    (haccepted : BridgeAccepted previous d0 d1 first last current claim)
    (hd0 : ∀ slot row, d0 slot row ≠ 0)
    (hd1 : ∀ slot row, d1 slot row ≠ 0)
    (hfirst : ∀ row, first row ≠ 0)
    (hlast : ∀ row, last row ≠ 0)
    (row : Fin 16) :
    current 4 row - current 4 (previous row) + claim / 16 =
      bridgeRowTerm d0 d1 first last row := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := haccepted row
  have hprod (slot : Fin 4) : d0 slot row * d1 slot row ≠ 0 :=
    mul_ne_zero (hd0 slot row) (hd1 slot row)
  have hend : first row * last row ≠ 0 :=
    mul_ne_zero (hfirst row) (hlast row)
  have e0 : current 0 row = bridgeGateTerm d0 d1 0 row :=
    eq_div_of_mul_sub_eq_zero _ _ _ (hprod 0) h0
  have e1 : current 1 row - current 0 row =
      bridgeGateTerm d0 d1 1 row :=
    eq_div_of_mul_sub_eq_zero _ _ _ (hprod 1) h1
  have e2 : current 2 row - current 1 row =
      bridgeGateTerm d0 d1 2 row :=
    eq_div_of_mul_sub_eq_zero _ _ _ (hprod 2) h2
  have e3 : current 3 row - current 2 row =
      bridgeGateTerm d0 d1 3 row :=
    eq_div_of_mul_sub_eq_zero _ _ _ (hprod 3) h3
  have e4 : current 4 row - current 4 (previous row) -
      current 3 row + claim / 16 = bridgeChipTerm first last row :=
    eq_div_of_mul_sub_eq_zero _ _ _ hend h4
  unfold bridgeRowTerm
  linear_combination e0 + e1 + e2 + e3 + e4

/-- Cyclic telescoping recovers each bridge's claimed sum. No assumption
about honest interaction-writer execution is used. -/
theorem bridge_air_claim_eq_fraction_sum (previous : Fin 16 ≃ Fin 16)
    (d0 d1 : Fin 4 → Fin 16 → K) (first last : Fin 16 → K)
    (current : Fin 5 → Fin 16 → K) (claim : K)
    (h16 : (16 : K) ≠ 0)
    (haccepted : BridgeAccepted previous d0 d1 first last current claim)
    (hd0 : ∀ slot row, d0 slot row ≠ 0)
    (hd1 : ∀ slot row, d1 slot row ≠ 0)
    (hfirst : ∀ row, first row ≠ 0)
    (hlast : ∀ row, last row ≠ 0) :
    claim = ∑ row : Fin 16, bridgeRowTerm d0 d1 first last row := by
  have hrows :
      (∑ row : Fin 16,
        (current 4 row - current 4 (previous row) + claim / 16)) =
      ∑ row : Fin 16, bridgeRowTerm d0 d1 first last row := by
    apply Finset.sum_congr rfl
    intro row _
    exact bridge_air_row_fraction previous d0 d1 first last current
      claim haccepted hd0 hd1 hfirst hlast row
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hrows
  rw [Equiv.sum_comp previous (current 4)] at hrows
  have hshift : (16 : K) * (claim / 16) = claim := by
    field_simp
  simpa [hshift] using hrows

/-- If the bridge's eight main words are constant, all five fractions have
row-independent denominators. This is the consequence of the eight
`current-next` residuals proved separately by `TaggedPairBridgeRows`. -/
theorem bridge_air_claim_eq_endpoint_reciprocals
    (previous : Fin 16 ≃ Fin 16)
    (d0 d1 : Fin 4 → K) (first last : K)
    (current : Fin 5 → Fin 16 → K) (claim : K)
    (h16 : (16 : K) ≠ 0)
    (haccepted : BridgeAccepted previous
      (fun slot _ => d0 slot) (fun slot _ => d1 slot)
      (fun _ => first) (fun _ => last) current claim)
    (hd0 : ∀ slot, d0 slot ≠ 0)
    (hd1 : ∀ slot, d1 slot ≠ 0)
    (hfirst : first ≠ 0) (hlast : last ≠ 0) :
    claim =
      (d0 0)⁻¹ + (d1 0)⁻¹ +
      (d0 1)⁻¹ + (d1 1)⁻¹ +
      (d0 2)⁻¹ + (d1 2)⁻¹ +
      (d0 3)⁻¹ + (d1 3)⁻¹ -
      first⁻¹ + last⁻¹ := by
  have hclaim := bridge_air_claim_eq_fraction_sum previous
    (fun slot _ => d0 slot) (fun slot _ => d1 slot)
    (fun _ => first) (fun _ => last) current claim
    h16 haccepted (fun slot _ => hd0 slot) (fun slot _ => hd1 slot)
    (fun _ => hfirst) (fun _ => hlast)
  have hrow :
      ∀ row : Fin 16,
        bridgeRowTerm (fun slot _ => d0 slot) (fun slot _ => d1 slot)
          (fun _ => first) (fun _ => last) row =
        bridgeRowTerm (fun slot _ => d0 slot) (fun slot _ => d1 slot)
          (fun _ => first) (fun _ => last) 0 := by
    intro row
    rfl
  rw [Finset.sum_congr rfl (fun row _ => hrow row)] at hclaim
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hclaim
  rw [hclaim]
  dsimp [bridgeRowTerm, bridgeGateTerm, bridgeChipTerm]
  field_simp [h16, hd0 0, hd1 0, hd0 1, hd1 1,
    hd0 2, hd1 2, hd0 3, hd1 3, hfirst, hlast]
  ring

/-- Bind a constant-word bridge's four Gate pairs and one chip endpoint
pair to their native six-word-padded and seven-word tuples. -/
theorem bridge_air_claim_eq_event_sums
    (previous : Fin 16 ≃ Fin 16)
    (gate0 gate1 : Fin 4 → JointTuple)
    (start finish : JointTuple)
    (d0 d1 : Fin 4 → GateSecure) (first last : GateSecure)
    (current : Fin 5 → Fin 16 → GateSecure) (claim alpha z : GateSecure)
    (h16 : (16 : GateSecure) ≠ 0)
    (haccepted : BridgeAccepted previous
      (fun slot _ => d0 slot) (fun slot _ => d1 slot)
      (fun _ => first) (fun _ => last) current claim)
    (hgate0 : ∀ slot, d0 slot = combine7 (gate0 slot) alpha z)
    (hgate1 : ∀ slot, d1 slot = combine7 (gate1 slot) alpha z)
    (hstart : first = combine7 start alpha z)
    (hfinish : last = combine7 finish alpha z)
    (hd0 : ∀ slot, d0 slot ≠ 0)
    (hd1 : ∀ slot, d1 slot ≠ 0)
    (hfirst : first ≠ 0) (hlast : last ≠ 0) :
    claim = productionReciprocalSum7
      [gate0 0, gate1 0, gate0 1, gate1 1,
       gate0 2, gate1 2, gate0 3, gate1 3] alpha z -
      productionReciprocalSum7 [start] alpha z +
      productionReciprocalSum7 [finish] alpha z := by
  rw [bridge_air_claim_eq_endpoint_reciprocals previous d0 d1
    first last current claim h16 haccepted hd0 hd1 hfirst hlast]
  simp only [productionReciprocalSum7, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  simp only [hgate0, hgate1, hstart, hfinish, div_eq_mul_inv]
  ring

private theorem reciprocalSum_append (left right : List JointTuple)
    (alpha z : GateSecure) :
    productionReciprocalSum7 (left ++ right) alpha z =
      productionReciprocalSum7 left alpha z +
      productionReciprocalSum7 right alpha z := by
  simp [productionReciprocalSum7]

/-- The native verifier checks that its five committed component claimed
sums add to zero. The four component equalities below are supplied by the
chip and bridge AIR lemmas above, and the circuit equality is a separate
Gate AIR correspondence premise. Their sum is exactly the signed event
closure consumed by `TaggedPairChallenge`. -/
theorem five_claimed_sums_imply_signed_closure
    (circuitYields circuitUses : List JointTuple)
    (bridgeGates₀ bridgeGates₁ chipInputs₀ chipInputs₁
      chipOutputs₀ chipOutputs₁ chipStarts₀ chipStarts₁
      chipEnds₀ chipEnds₁ : List JointTuple)
    (alpha z circuitClaim chipClaim₀ chipClaim₁
      bridgeClaim₀ bridgeClaim₁ : GateSecure)
    (hcircuit : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
    (hchip₀ : chipClaim₀ =
      productionReciprocalSum7 chipInputs₀ alpha z -
      productionReciprocalSum7 chipOutputs₀ alpha z)
    (hchip₁ : chipClaim₁ =
      productionReciprocalSum7 chipInputs₁ alpha z -
      productionReciprocalSum7 chipOutputs₁ alpha z)
    (hbridge₀ : bridgeClaim₀ =
      productionReciprocalSum7 bridgeGates₀ alpha z -
      productionReciprocalSum7 chipStarts₀ alpha z +
      productionReciprocalSum7 chipEnds₀ alpha z)
    (hbridge₁ : bridgeClaim₁ =
      productionReciprocalSum7 bridgeGates₁ alpha z -
      productionReciprocalSum7 chipStarts₁ alpha z +
      productionReciprocalSum7 chipEnds₁ alpha z)
    (hfive : circuitClaim + chipClaim₀ + chipClaim₁ +
      bridgeClaim₀ + bridgeClaim₁ = 0) :
    jointSignedClosure circuitYields circuitUses
      (bridgeGates₀ ++ bridgeGates₁)
      (chipInputs₀ ++ chipInputs₁)
      (chipOutputs₀ ++ chipOutputs₁)
      (chipStarts₀ ++ chipStarts₁)
      (chipEnds₀ ++ chipEnds₁) alpha z = 0 := by
  rw [hcircuit, hchip₀, hchip₁, hbridge₀, hbridge₁] at hfive
  simp only [jointSignedClosure, reciprocalSum_append]
  linear_combination hfive

/-- Compose the source-shaped five-claim closure with the explicit ideal
challenge exception set. This is exact joint event balance under the stated
component AIR and circuit correspondence premises; it does not establish
those premises from an accepted PCS/FRI proof. -/
theorem five_claimed_sums_imply_exact_joint_events
    (circuitYields circuitUses : List JointTuple)
    (bridgeGates₀ bridgeGates₁ chipInputs₀ chipInputs₁
      chipOutputs₀ chipOutputs₁ chipStarts₀ chipStarts₁
      chipEnds₀ chipEnds₁ : List JointTuple)
    (alpha z circuitClaim chipClaim₀ chipClaim₁
      bridgeClaim₀ bridgeClaim₁ : GateSecure)
    (hcircuit : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
    (hchip₀ : chipClaim₀ =
      productionReciprocalSum7 chipInputs₀ alpha z -
      productionReciprocalSum7 chipOutputs₀ alpha z)
    (hchip₁ : chipClaim₁ =
      productionReciprocalSum7 chipInputs₁ alpha z -
      productionReciprocalSum7 chipOutputs₁ alpha z)
    (hbridge₀ : bridgeClaim₀ =
      productionReciprocalSum7 bridgeGates₀ alpha z -
      productionReciprocalSum7 chipStarts₀ alpha z +
      productionReciprocalSum7 chipEnds₀ alpha z)
    (hbridge₁ : bridgeClaim₁ =
      productionReciprocalSum7 bridgeGates₁ alpha z -
      productionReciprocalSum7 chipStarts₁ alpha z +
      productionReciprocalSum7 chipEnds₁ alpha z)
    (hfive : circuitClaim + chipClaim₀ + chipClaim₁ +
      bridgeClaim₀ + bridgeClaim₁ = 0)
    (hgood : (alpha,z) ∉ badPairs7
      (circuitYields ++ (bridgeGates₀ ++ bridgeGates₁) ++
        (chipInputs₀ ++ chipInputs₁) ++ (chipEnds₀ ++ chipEnds₁))
      (circuitUses ++ (chipOutputs₀ ++ chipOutputs₁) ++
        (chipStarts₀ ++ chipStarts₁))) :
    (circuitYields ++ (bridgeGates₀ ++ bridgeGates₁) ++
      (chipInputs₀ ++ chipInputs₁) ++ (chipEnds₀ ++ chipEnds₁)).Perm
    (circuitUses ++ (chipOutputs₀ ++ chipOutputs₁) ++
      (chipStarts₀ ++ chipStarts₁)) := by
  apply exact_joint_events_of_signed_closure _ _ _ _ _ _ _ alpha z
    hgood
  exact five_claimed_sums_imply_signed_closure
    circuitYields circuitUses bridgeGates₀ bridgeGates₁
    chipInputs₀ chipInputs₁ chipOutputs₀ chipOutputs₁
    chipStarts₀ chipStarts₁ chipEnds₀ chipEnds₁
    alpha z circuitClaim chipClaim₀ chipClaim₁ bridgeClaim₀ bridgeClaim₁
    hcircuit hchip₀ hchip₁ hbridge₀ hbridge₁ hfive

/-- The two native chip components each have `R` committed logical rows.
The tuple fields represent the verifier-fixed relation and call IDs plus
witness step/state columns; the other fields are the secure interaction
columns and denominators sampled from those tuples. -/
structure ChipProfile (R : Nat) where
  previous : Fin R ≃ Fin R
  input : Fin R → JointTuple
  output : Fin R → JointTuple
  qin : Fin R → GateSecure
  qout : Fin R → GateSecure
  first : Fin R → GateSecure
  current : Fin R → GateSecure
  claim : GateSecure

/-- One 16-row bridge after its eight main columns have been proved constant.
The four Gate pairs and one chip endpoint pair are verifier-selected from
those constant columns. -/
structure BridgeProfile where
  previous : Fin 16 ≃ Fin 16
  gate0 : Fin 4 → JointTuple
  gate1 : Fin 4 → JointTuple
  start : JointTuple
  finish : JointTuple
  d0 : Fin 4 → GateSecure
  d1 : Fin 4 → GateSecure
  first : GateSecure
  last : GateSecure
  current : Fin 5 → Fin 16 → GateSecure
  claim : GateSecure

def BridgeProfile.gates (bridge : BridgeProfile) : List JointTuple :=
  [bridge.gate0 0, bridge.gate1 0, bridge.gate0 1, bridge.gate1 1,
   bridge.gate0 2, bridge.gate1 2, bridge.gate0 3, bridge.gate1 3]

/-- Source-shaped composition of the verifier-accepted logical AIR rows.
The premises explicitly say: all chip and bridge row residuals vanish on
their cyclic predecessor masks; the bridge's eight main words are constant
(so its denominator fields are row-independent); every event denominator is
nonzero; the circuit Gate claim has its separate event interpretation; and
the verifier checked the five claimed sums total zero. No PCS, Fiat–Shamir,
or source-manifest correspondence is inferred from these premises. -/
theorem accepted_pair_air_implies_signed_closure
    {R₀ R₁ : Nat}
    (chip₀ : ChipProfile R₀) (chip₁ : ChipProfile R₁)
    (bridge₀ bridge₁ : BridgeProfile)
    (circuitYields circuitUses : List JointTuple)
    (circuitClaim alpha z : GateSecure)
    (hR₀ : (R₀ : GateSecure) ≠ 0)
    (hR₁ : (R₁ : GateSecure) ≠ 0)
    (h16 : (16 : GateSecure) ≠ 0)
    (hchip₀ : ChipAccepted chip₀.previous chip₀.qin chip₀.qout
      chip₀.first chip₀.current chip₀.claim)
    (hchip₁ : ChipAccepted chip₁.previous chip₁.qin chip₁.qout
      chip₁.first chip₁.current chip₁.claim)
    (hbridge₀ : BridgeAccepted bridge₀.previous
      (fun slot _ => bridge₀.d0 slot) (fun slot _ => bridge₀.d1 slot)
      (fun _ => bridge₀.first) (fun _ => bridge₀.last)
      bridge₀.current bridge₀.claim)
    (hbridge₁ : BridgeAccepted bridge₁.previous
      (fun slot _ => bridge₁.d0 slot) (fun slot _ => bridge₁.d1 slot)
      (fun _ => bridge₁.first) (fun _ => bridge₁.last)
      bridge₁.current bridge₁.claim)
    (hchipTuples₀ : ∀ row,
      chip₀.qin row = combine7 (chip₀.input row) alpha z ∧
      chip₀.qout row = combine7 (chip₀.output row) alpha z)
    (hchipTuples₁ : ∀ row,
      chip₁.qin row = combine7 (chip₁.input row) alpha z ∧
      chip₁.qout row = combine7 (chip₁.output row) alpha z)
    (hbridgeTuples₀ :
      (∀ slot, bridge₀.d0 slot = combine7 (bridge₀.gate0 slot) alpha z ∧
        bridge₀.d1 slot = combine7 (bridge₀.gate1 slot) alpha z) ∧
      bridge₀.first = combine7 bridge₀.start alpha z ∧
      bridge₀.last = combine7 bridge₀.finish alpha z)
    (hbridgeTuples₁ :
      (∀ slot, bridge₁.d0 slot = combine7 (bridge₁.gate0 slot) alpha z ∧
        bridge₁.d1 slot = combine7 (bridge₁.gate1 slot) alpha z) ∧
      bridge₁.first = combine7 bridge₁.start alpha z ∧
      bridge₁.last = combine7 bridge₁.finish alpha z)
    (hnonzeroChip₀ : ∀ row, chip₀.qin row ≠ 0 ∧ chip₀.qout row ≠ 0)
    (hnonzeroChip₁ : ∀ row, chip₁.qin row ≠ 0 ∧ chip₁.qout row ≠ 0)
    (hnonzeroBridge₀ :
      (∀ slot, bridge₀.d0 slot ≠ 0 ∧ bridge₀.d1 slot ≠ 0) ∧
      bridge₀.first ≠ 0 ∧ bridge₀.last ≠ 0)
    (hnonzeroBridge₁ :
      (∀ slot, bridge₁.d0 slot ≠ 0 ∧ bridge₁.d1 slot ≠ 0) ∧
      bridge₁.first ≠ 0 ∧ bridge₁.last ≠ 0)
    (hcircuit : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
    (hfive : circuitClaim + chip₀.claim + chip₁.claim +
      bridge₀.claim + bridge₁.claim = 0) :
    jointSignedClosure circuitYields circuitUses
      ([bridge₀.gate0 0, bridge₀.gate1 0, bridge₀.gate0 1, bridge₀.gate1 1,
        bridge₀.gate0 2, bridge₀.gate1 2, bridge₀.gate0 3, bridge₀.gate1 3] ++
       [bridge₁.gate0 0, bridge₁.gate1 0, bridge₁.gate0 1, bridge₁.gate1 1,
        bridge₁.gate0 2, bridge₁.gate1 2, bridge₁.gate0 3, bridge₁.gate1 3])
      (List.ofFn chip₀.input ++ List.ofFn chip₁.input)
      (List.ofFn chip₀.output ++ List.ofFn chip₁.output)
      ([bridge₀.start] ++ [bridge₁.start])
      ([bridge₀.finish] ++ [bridge₁.finish]) alpha z = 0 := by
  have hc₀ := chip_air_claim_eq_event_sums chip₀.previous
    chip₀.input chip₀.output chip₀.qin chip₀.qout chip₀.first
    chip₀.current chip₀.claim alpha z hR₀ hchip₀
    (fun row => (hchipTuples₀ row).1)
    (fun row => (hchipTuples₀ row).2)
    (fun row => (hnonzeroChip₀ row).1)
    (fun row => (hnonzeroChip₀ row).2)
  have hc₁ := chip_air_claim_eq_event_sums chip₁.previous
    chip₁.input chip₁.output chip₁.qin chip₁.qout chip₁.first
    chip₁.current chip₁.claim alpha z hR₁ hchip₁
    (fun row => (hchipTuples₁ row).1)
    (fun row => (hchipTuples₁ row).2)
    (fun row => (hnonzeroChip₁ row).1)
    (fun row => (hnonzeroChip₁ row).2)
  have hb₀ := bridge_air_claim_eq_event_sums bridge₀.previous
    bridge₀.gate0 bridge₀.gate1 bridge₀.start bridge₀.finish
    bridge₀.d0 bridge₀.d1 bridge₀.first bridge₀.last
    bridge₀.current bridge₀.claim alpha z h16 hbridge₀
    (fun slot => (hbridgeTuples₀.1 slot).1)
    (fun slot => (hbridgeTuples₀.1 slot).2)
    hbridgeTuples₀.2.1 hbridgeTuples₀.2.2
    (fun slot => (hnonzeroBridge₀.1 slot).1)
    (fun slot => (hnonzeroBridge₀.1 slot).2)
    hnonzeroBridge₀.2.1 hnonzeroBridge₀.2.2
  have hb₁ := bridge_air_claim_eq_event_sums bridge₁.previous
    bridge₁.gate0 bridge₁.gate1 bridge₁.start bridge₁.finish
    bridge₁.d0 bridge₁.d1 bridge₁.first bridge₁.last
    bridge₁.current bridge₁.claim alpha z h16 hbridge₁
    (fun slot => (hbridgeTuples₁.1 slot).1)
    (fun slot => (hbridgeTuples₁.1 slot).2)
    hbridgeTuples₁.2.1 hbridgeTuples₁.2.2
    (fun slot => (hnonzeroBridge₁.1 slot).1)
    (fun slot => (hnonzeroBridge₁.1 slot).2)
    hnonzeroBridge₁.2.1 hnonzeroBridge₁.2.2
  exact five_claimed_sums_imply_signed_closure
    circuitYields circuitUses
    [bridge₀.gate0 0, bridge₀.gate1 0, bridge₀.gate0 1, bridge₀.gate1 1,
      bridge₀.gate0 2, bridge₀.gate1 2, bridge₀.gate0 3, bridge₀.gate1 3]
    [bridge₁.gate0 0, bridge₁.gate1 0, bridge₁.gate0 1, bridge₁.gate1 1,
      bridge₁.gate0 2, bridge₁.gate1 2, bridge₁.gate0 3, bridge₁.gate1 3]
    (List.ofFn chip₀.input) (List.ofFn chip₁.input)
    (List.ofFn chip₀.output) (List.ofFn chip₁.output)
    [bridge₀.start] [bridge₁.start]
    [bridge₀.finish] [bridge₁.finish]
    alpha z circuitClaim chip₀.claim chip₁.claim
    bridge₀.claim bridge₁.claim hcircuit hc₀ hc₁ hb₀ hb₁ hfive

end S31.Gadgets.Air.TaggedPairAirClosure
