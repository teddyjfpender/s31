import S31.Gadgets.Functional.TextSquare4GateJoin
import S31.Gadgets.Air.GateUseTraversal

/-!
The concrete source-generated circuit claim, composed with the modeled
checked Gate counters and bounded-error LogUp closure. This remains a
conditional algebraic theorem: source-to-trace event correspondence,
commitment openings, Fiat-Shamir sampling, and the native verifier protocol
are not asserted here.
-/

namespace S31.Functional.TextSquare4ChallengeJoin

open S31
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateCounter
open S31.Gadgets.Air.GateCounterCircuit
open S31.Gadgets.Air.GateUseTraversal
open S31.Functional.TextSquare4GateJoin

/-- For a nonexceptional challenge pair, successful compressed counter
walks and zero Gate reciprocal contribution force the four public output
words of the exported circuit path to be the fourth powers of its public
inputs. Declared-event coverage and local AIR acceptance stay explicit. -/
theorem public_claim_of_checked_logup_closure
    (rows : List Row)
    (externalUses externalYields declared :
      List S31.Gadgets.Air.GateLookup.Event)
    (baseUses shaBoundary : List S31.Gadgets.Air.GateLookup.Event)
    (bound permutationRows : Nat) (result : Finset Nat)
    (useCounts yieldCounts : Nat → Nat)
    (input claimed : Fin 4 → M31)
    (hbound : 35 ≤ bound)
    (huses : allUses rows externalUses =
      expandedUses baseUses permutationRows shaBoundary)
    (huseRun : checkedCounts
      (compressedUses baseUses permutationRows shaBoundary) =
        some useCounts)
    (hyieldRun : checkedCounts
      (rowYieldSteps rows externalYields) = some yieldCounts)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < modulus)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan bound ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value, address < 35 →
      (address, value) ∈ allYields rows externalYields →
      (address, value) ∈ declared)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  have hbalanced := closed_gate_of_compressed_counters
    rows externalUses externalYields baseUses shaBoundary
    permutationRows useCounts yieldCounts huses huseRun hyieldRun
    alpha z hcanonical halpha hz hclosed
  exact native_public_claim_of_checked_declared rows
    externalUses externalYields declared bound result input claimed
    hbound hbalanced hscan hcovered hpath hpins

/-- A forged public result cannot have zero Gate reciprocal contribution at
a good challenge pair while all checked counter, producer, path-row and
public-event premises hold. -/
theorem forged_claim_rejected_at_good_challenges
    (rows : List Row)
    (externalUses externalYields declared :
      List S31.Gadgets.Air.GateLookup.Event)
    (baseUses shaBoundary : List S31.Gadgets.Air.GateLookup.Event)
    (bound permutationRows : Nat) (result : Finset Nat)
    (useCounts yieldCounts : Nat → Nat)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ TextSquare4Air.fourth input)
    (hbound : 35 ≤ bound)
    (huses : allUses rows externalUses =
      expandedUses baseUses permutationRows shaBoundary)
    (huseRun : checkedCounts
      (compressedUses baseUses permutationRows shaBoundary) =
        some useCounts)
    (hyieldRun : checkedCounts
      (rowYieldSteps rows externalYields) = some yieldCounts)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < modulus)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan bound ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value, address < 35 →
      (address, value) ∈ allYields rows externalYields →
      (address, value) ∈ declared)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z ≠ 0 := by
  intro hclosed
  exact hforged (public_claim_of_checked_logup_closure rows
    externalUses externalYields declared baseUses shaBoundary
    bound permutationRows result useCounts yieldCounts input claimed
    hbound huses huseRun hyieldRun alpha z hcanonical halpha hz hclosed
    hscan hcovered hpath hpins)

end S31.Functional.TextSquare4ChallengeJoin
