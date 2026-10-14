import Mathlib.Tactic

/-!
Conditional mass accounting for two sequential raw Gate PoW searches. This is
not a ROM/BCS theorem for BLAKE2s. A list entry is the conditional probability
that one *fresh, distinct* oracle trial passes, after all previous failures.
The entries may vary with the preceding search history. A native reduction
must establish the fresh-input premise across transcript, Merkle, and PoW
roles before applying any bound here.
-/

namespace S31.Gadgets.PcsFri.RawGateTwoStageGrinding

/-- Failure mass after sequentially trying conditional pass probabilities. -/
def failureProduct (trials : List ℚ) : ℚ :=
  (trials.map (fun q => 1 - q)).prod

/-- Search success conditional on entering the stage. -/
def stageHit (trials : List ℚ) : ℚ := 1 - failureProduct trials

/-- Conditional probability that a first-stage search and, after its success,
a second-stage search both succeed. The second list represents conditional
trial probabilities *after* the first accepted nonce and subsequent transcript
events. This product is justified only by that conditional interpretation. -/
def twoStageHit (first second : List ℚ) : ℚ :=
  stageHit first * stageHit second

theorem failure_product_nonneg (trials : List ℚ)
    (h : ∀ q ∈ trials, q ≤ 1) : 0 ≤ failureProduct trials := by
  induction trials with
  | nil => simp [failureProduct]
  | cons q qs ih =>
      have hq : q ≤ 1 := h q (by simp)
      have hqs : ∀ r ∈ qs, r ≤ 1 := by
        intro r hr
        exact h r (by simp [hr])
      simp only [failureProduct, List.map_cons, List.prod_cons]
      exact mul_nonneg (by linarith) (ih hqs)

theorem failure_product_le_one (trials : List ℚ)
    (h : ∀ q ∈ trials, 0 ≤ q ∧ q ≤ 1) : failureProduct trials ≤ 1 := by
  induction trials with
  | nil => simp [failureProduct]
  | cons q qs ih =>
      have hq : 0 ≤ q ∧ q ≤ 1 := h q (by simp)
      have hqs : ∀ r ∈ qs, 0 ≤ r ∧ r ≤ 1 := by
        intro r hr
        exact h r (by simp [hr])
      have hprod := ih hqs
      have hnonneg := failure_product_nonneg qs (fun r hr => (hqs r hr).2)
      change (1 - q) * failureProduct qs ≤ 1
      nlinarith [mul_nonneg hq.1 hnonneg]

/-- Every adaptive fresh trial has conditional pass chance at most `p`.
The all-`p` search dominates its hit probability. -/
theorem failure_product_lower_bound (trials : List ℚ) (p : ℚ)
    (hp : 0 ≤ p ∧ p ≤ 1)
    (h : ∀ q ∈ trials, 0 ≤ q ∧ q ≤ p) :
    (1 - p) ^ trials.length ≤ failureProduct trials := by
  induction trials with
  | nil => simp [failureProduct]
  | cons q qs ih =>
      have hq : 0 ≤ q ∧ q ≤ p := h q (by simp)
      have hqs : ∀ r ∈ qs, 0 ≤ r ∧ r ≤ p := by
        intro r hr
        exact h r (by simp [hr])
      have hpow := pow_nonneg (by linarith : 0 ≤ 1 - p) qs.length
      have hprev := ih hqs
      have hfail := failure_product_nonneg qs (fun r hr => le_trans (hqs r hr).2 hp.2)
      simp only [List.length_cons, pow_succ]
      change (1 - p) ^ qs.length * (1 - p) ≤ (1 - q) * failureProduct qs
      have hleft := mul_le_mul_of_nonneg_right hprev (by linarith : 0 ≤ 1 - p)
      have hright := mul_le_mul_of_nonneg_left (show 1 - p ≤ 1 - q by linarith) hfail
      nlinarith

theorem stage_hit_le_fresh_bound (trials : List ℚ) (p : ℚ)
    (hp : 0 ≤ p ∧ p ≤ 1)
    (h : ∀ q ∈ trials, 0 ≤ q ∧ q ≤ p) :
    stageHit trials ≤ 1 - (1 - p) ^ trials.length := by
  unfold stageHit
  linarith [failure_product_lower_bound trials p hp h]

theorem one_sub_pow_le_linear (p : ℚ) (n : ℕ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    1 - (1 - p) ^ n ≤ (n : ℚ) * p := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow := pow_nonneg (by linarith : 0 ≤ 1 - p) n
      calc
        1 - (1 - p) ^ (n + 1)
            = (1 - (1 - p) ^ n) + p * (1 - p) ^ n := by ring
        _ ≤ (n : ℚ) * p + p := by
          have hpow_le : (1 - p) ^ n ≤ 1 := by
            exact pow_le_one₀ (by linarith) (by linarith)
          nlinarith
        _ = ((n + 1 : ℕ) : ℚ) * p := by push_cast; ring

/-- Union envelope for any adaptive stage whose fresh conditional trials are
bounded by `p`. This is a search-success bound, not a proof-error bound. -/
theorem stage_hit_le_budget (trials : List ℚ) (p : ℚ)
    (hp : 0 ≤ p ∧ p ≤ 1)
    (h : ∀ q ∈ trials, 0 ≤ q ∧ q ≤ p) :
    stageHit trials ≤ min 1 ((trials.length : ℚ) * p) := by
  have hle := stage_hit_le_fresh_bound trials p hp h
  have hlinear := one_sub_pow_le_linear p trials.length hp
  have hnonneg := failure_product_nonneg trials
    (fun q hq => le_trans (h q hq).2 hp.2)
  exact le_min (by unfold stageHit; linarith) (hle.trans hlinear)

/-- Two sequential adaptive stages obey the product of their *conditional*
search envelopes if both stages have fresh conditional trials. An adaptive
strategy may choose its second-stage prefix and trials after first success;
the second premise must hold conditioned on every such choice. -/
theorem two_stage_budget (first second : List ℚ) (p₁ p₂ : ℚ)
    (hp₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (hp₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (hfirst : ∀ q ∈ first, 0 ≤ q ∧ q ≤ p₁)
    (hsecond : ∀ q ∈ second, 0 ≤ q ∧ q ≤ p₂) :
    twoStageHit first second ≤
      min 1 ((first.length : ℚ) * p₁) *
      min 1 ((second.length : ℚ) * p₂) := by
  have h₁ := stage_hit_le_budget first p₁ hp₁ hfirst
  have h₂ := stage_hit_le_budget second p₂ hp₂ hsecond
  have hfirst_nonneg : 0 ≤ stageHit first := by
    unfold stageHit
    linarith [failure_product_le_one first (fun q hq =>
      ⟨(hfirst q hq).1, le_trans (hfirst q hq).2 hp₁.2⟩)]
  have hbound_nonneg : 0 ≤ min 1 ((first.length : ℚ) * p₁) := by
    exact le_min (by norm_num) (mul_nonneg (by positivity) hp₁.1)
  unfold twoStageHit
  exact (mul_le_mul_of_nonneg_left h₂ hfirst_nonneg).trans
    (mul_le_mul_of_nonneg_right h₁ (by
      have hsecond_nonneg : 0 ≤ stageHit second := by
        unfold stageHit
        linarith [failure_product_le_one second (fun q hq =>
          ⟨(hsecond q hq).1, le_trans (hsecond q hq).2 hp₂.2⟩)]
      exact le_trans hsecond_nonneg h₂))

/-- The first accepted nonce can lead to different second-stage prefixes.
`firstMass i` is the probability mass of one disjoint first-stage success
history; `secondConditional i` is the conditional second-stage hit chance on
that history. If every branch has the same proved fresh-trial envelope, the
weighted adaptive search obeys that envelope. This theorem does not assert
that the native raw channel supplies either probability premise. -/
theorem adaptive_second_stage_branches
    {ι : Type*} [Fintype ι]
    (firstMass secondConditional : ι → ℚ)
    (firstBound secondBound : ℚ)
    (hmass : ∀ i, 0 ≤ firstMass i)
    (hfirst : ∑ i, firstMass i ≤ firstBound)
    (hsecond : ∀ i, secondConditional i ≤ secondBound)
    (hsecond_nonneg : 0 ≤ secondBound) :
    (∑ i, firstMass i * secondConditional i) ≤
      firstBound * secondBound := by
  calc
    ∑ i, firstMass i * secondConditional i
        ≤ ∑ i, firstMass i * secondBound := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hsecond i) (hmass i)
    _ = (∑ i, firstMass i) * secondBound := by rw [Finset.sum_mul]
    _ ≤ firstBound * secondBound :=
      mul_le_mul_of_nonneg_right hfirst hsecond_nonneg

/-- A fixed first-stage cap and a per-history second-stage cap. The disjoint
first-success masses may represent any adaptive choice of the first accepted
nonce and the resulting FRI transcript. The `hfirstTotal` premise is a
probability decomposition, not something established by the native verifier. -/
theorem adaptive_two_stage_fresh_trials
    {ι : Type*} [Fintype ι]
    (first : List ℚ) (second : ι → List ℚ) (firstMass : ι → ℚ)
    (p₁ p₂ : ℚ) (secondCap : ℕ)
    (hp₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (hp₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    (hfirstTrials : ∀ q ∈ first, 0 ≤ q ∧ q ≤ p₁)
    (hfirstMass : ∀ i, 0 ≤ firstMass i)
    (hfirstTotal : ∑ i, firstMass i ≤ stageHit first)
    (hsecondCap : ∀ i, (second i).length ≤ secondCap)
    (hsecondTrials : ∀ i q, q ∈ second i → 0 ≤ q ∧ q ≤ p₂) :
    (∑ i, firstMass i * stageHit (second i)) ≤
      min 1 ((first.length : ℚ) * p₁) *
      min 1 ((secondCap : ℚ) * p₂) := by
  have hfirstBound : ∑ i, firstMass i ≤
      min 1 ((first.length : ℚ) * p₁) :=
    hfirstTotal.trans (stage_hit_le_budget first p₁ hp₁ hfirstTrials)
  have hsecondBound : ∀ i, stageHit (second i) ≤
      min 1 ((secondCap : ℚ) * p₂) := by
    intro i
    have hs := stage_hit_le_budget (second i) p₂ hp₂ (hsecondTrials i)
    have hlen : ((second i).length : ℚ) ≤ secondCap := by
      exact_mod_cast hsecondCap i
    have hlinear : ((second i).length : ℚ) * p₂ ≤ secondCap * p₂ :=
      mul_le_mul_of_nonneg_right hlen hp₂.1
    exact le_min (le_trans hs (min_le_left _ _))
      (le_trans hs (le_trans (min_le_right _ _) hlinear))
  exact adaptive_second_stage_branches firstMass
    (fun i => stageHit (second i))
    (min 1 ((first.length : ℚ) * p₁))
    (min 1 ((secondCap : ℚ) * p₂))
    hfirstMass hfirstBound hsecondBound
    (le_min (by norm_num) (mul_nonneg (by positivity) hp₂.1))

/-- At T=2^64, both raw PoW-only union envelopes saturate. This does not
mean a false STARK proof is accepted with probability one. -/
theorem t64_pow_only_envelope_saturates :
    min (1 : ℚ) ((2 : ℚ) ^ 64 / 2 ^ 20) = 1 ∧
    min (1 : ℚ) ((2 : ℚ) ^ 64 / 2 ^ 26) = 1 ∧
    (1 : ℚ) / 2 ^ 64 > 1 / 2 ^ 96 := by
  norm_num

/-- One first-stage nonce and one second-stage nonce have the 46-bit product
only under independent fresh conditional predicates. A two-nonce first-stage
search already exceeds that product in this ideal model. -/
theorem two_first_trials_exceed_single_pair :
    twoStageHit [1 / (2 : ℚ) ^ 20, 1 / (2 : ℚ) ^ 20]
      [1 / (2 : ℚ) ^ 26] > 1 / (2 : ℚ) ^ 46 := by
  norm_num [twoStageHit, stageHit, failureProduct]

/-- Native PoW trial hashes `prefixDigest ++ nonceLE`. -/
def powNonceInput (prefixDigest nonceLE : List Nat) : List Nat :=
  prefixDigest ++ nonceLE

/-- Accepted nonce absorption hashes `channelDigest ++ nonceLE`. -/
def absorbNonceInput (channelDigest nonceLE : List Nat) : List Nat :=
  channelDigest ++ nonceLE

/-- Native PoW trial hashes `prefixDigest ++ nonceLE`; accepted nonce
absorption hashes `channelDigest ++ nonceLE`. Those 40-byte input roles are
not disjoint by construction. This is no claim that BLAKE2s attains the
prefixDigest = channelDigest condition on an accepted proof. -/
theorem pow_nonce_absorption_overlap (digest nonceLE : List Nat)
    (hdigest : digest.length = 32) (hnonce : nonceLE.length = 8) :
    powNonceInput digest nonceLE = absorbNonceInput digest nonceLE ∧
    (powNonceInput digest nonceLE).length = 40 := by
  simp [powNonceInput, absorbNonceInput, hdigest, hnonce]

end S31.Gadgets.PcsFri.RawGateTwoStageGrinding
