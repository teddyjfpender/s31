import S31.Gadgets.PcsFri.FoldAlgebra
import S31.Gadgets.PcsFri.QueryAndTranscript
import S31.Gadgets.PcsFri.ShortTerminalGeometry
import Mathlib.Tactic

/-!
CAS07's one-source-height (`H = 1`) circle-to-line path. Unlike the general
`LayerAcceptance.Layer`, the inverse circle coordinate here depends on the
pair's position. The verifier has no intermediate line commitment at `H = 1`:
it checks the first fold directly against the terminal line polynomial.

`verified` models the exact local equations checked by `verifyFolds` and the
profile's terminal length. `authenticated` is a separate premise identifying
the captured answer pair with a fixed source oracle. This file does not prove
that Zig execution produces these predicates, that source openings are
authenticated, or that the oracle is close to a low-degree polynomial.
-/

namespace S31.Gadgets.PcsFri.Cas07H1Terminal

open S31.Gadgets.PcsFri.FoldAlgebra
open S31.Gadgets.PcsFri.QueryAndTranscript

variable {F : Type*} [Field F]

/-- The line basis used by `LinePoly.evalAtPoint`: `x`, then repeated circle
doubling of the x-coordinate. -/
def doubleX (x : F) : F := 2 * x ^ 2 - 1

def basisAt (x : F) (j : Nat) : F := (doubleX^[j]) x

/-- Ordered coefficient `i` contributes one basis factor for each set bit.
For a power-of-two coefficient count this is the mathematical value of the
native bit-reversed `LinePoly.fromOrderedCoefficients` representation. The
equality with the Zig `poly_utils.fold` implementation remains an explicit
implementation-refinement obligation. -/
def coefficientBasis (x : F) (i m : Nat) : F :=
  ∏ j ∈ Finset.range m, if i.testBit j then basisAt x j else 1

def orderedLineEval (coefficients : List F) (x : F) : F :=
  ∑ i ∈ Finset.range coefficients.length,
    coefficients.getD i 0 * coefficientBasis x i (Nat.log2 coefficients.length)

theorem orderedLineEval_single (c x : F) :
    orderedLineEval [c] x = c := by
  simp [orderedLineEval, coefficientBasis]

theorem orderedLineEval_pair (c₀ c₁ x : F) :
    orderedLineEval [c₀, c₁] x = c₀ + c₁ * x := by
  norm_num [orderedLineEval, coefficientBasis, basisAt, Finset.sum_range_succ,
    Finset.prod_range_succ]

theorem orderedLineEval_four (c₀ c₁ c₂ c₃ x : F) :
    orderedLineEval [c₀, c₁, c₂, c₃] x =
      c₀ + c₁ * x + c₂ * doubleX x + c₃ * (x * doubleX x) := by
  have hlog : Nat.log2 4 = 2 := by decide
  have hbit1 : Nat.testBit 1 1 = false := by decide
  have hbit2 : Nat.testBit 2 1 = true := by decide
  have hbit3 : Nat.testBit 3 1 = true := by decide
  simp [orderedLineEval, coefficientBasis, basisAt, hlog,
    hbit1, hbit2, hbit3, Finset.sum_range_succ, Finset.prod_range_succ]

/-- CAS07 profile inequalities for the `H = 1` route. -/
structure Profile where
  k : Nat
  beta : Nat
  positiveBlowup : 0 < beta
  fits : 1 + beta ≤ k

def terminalCoeffLog (profile : Profile) : Nat :=
  profile.k - 1 - profile.beta

def terminalDomainLog (profile : Profile) : Nat := profile.k - 1

theorem terminalDomainLog_eq_coeff_add_blowup (profile : Profile) :
    terminalDomainLog profile = terminalCoeffLog profile + profile.beta := by
  have h := profile.fits
  dsimp [terminalDomainLog, terminalCoeffLog]
  omega

theorem paperR_zero (profile : Profile) :
    ShortTerminalGeometry.paperR
      ⟨profile.k, profile.beta, 1, profile.positiveBlowup, by omega, profile.fits⟩ = 0 := by
  rfl

/-- One raw query is a position in the original circle domain; the terminal
line position is its right shift by one. -/
def row (q : Nat) : Nat := q / 2

theorem row_eq_foldPosition (q : Nat) : row q = foldPosition 1 q := by
  simp [row, foldPosition]

theorem row_lt_terminal_domain (profile : Profile) (q : Nat)
    (hq : q < 2 ^ profile.k) : row q < 2 ^ terminalDomainLog profile := by
  have hfits := profile.fits
  have hk : 1 ≤ profile.k := by omega
  have hp : 2 ^ profile.k = 2 ^ (profile.k - 1) * 2 := by
    conv_lhs => rw [show profile.k = profile.k - 1 + 1 by omega]
    simp [pow_succ]
  dsimp [row, terminalDomainLog]
  rw [hp] at hq
  exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr hq

/-- `opened q` is stored per raw transcript slot, as in CAS07's answers
array. Repeated draws may have distinct slots; authentication forces them to
the same source pair. -/
structure Trace (F : Type*) [Field F] where
  profile : Profile
  alpha : F
  oracle : Nat → F
  opened : Nat → Fin 2 → F
  y : Nat → F
  x : Nat → F
  coefficients : List F

def openedFold (trace : Trace F) (q : Nat) : F :=
  pairFold trace.alpha (trace.y (row q))⁻¹
    (trace.opened q 0) (trace.opened q 1)

def oracleFold (trace : Trace F) (p : Nat) : F :=
  pairFold trace.alpha (trace.y p)⁻¹
    (trace.oracle (2 * p)) (trace.oracle (2 * p + 1))

def terminalAt (trace : Trace F) (p : Nat) : F :=
  orderedLineEval trace.coefficients (trace.x p)

/-- This is the H=1 verifier's local success relation after transcript
sampling and source answer construction. It includes no intermediate line
oracle. The coordinate nonzero condition records successful native inversion. -/
def verified (trace : Trace F) (raw : List Nat) : Prop :=
  trace.coefficients.length = 2 ^ terminalCoeffLog trace.profile ∧
  ∀ q ∈ raw, q < 2 ^ trace.profile.k ∧
    trace.y (row q) ≠ 0 ∧
    openedFold trace q = terminalAt trace (row q)

/-- This equality needs the source Merkle opening and quotient-answer custody
arguments. It is deliberately not inferred from the fold check itself. -/
def authenticated (trace : Trace F) (raw : List Nat) : Prop :=
  ∀ q ∈ raw, ∀ r : Fin 2,
    trace.opened q r = trace.oracle (2 * row q + r.val)

theorem openedFold_eq_oracleFold (trace : Trace F) (raw : List Nat)
    (hauth : authenticated trace raw) (q : Nat) (hq : q ∈ raw) :
    openedFold trace q = oracleFold trace (row q) := by
  simp only [openedFold, oracleFold]
  rw [hauth q hq 0, hauth q hq 1]
  simp

/-- Successful H=1 checking and authenticated answers force the *fixed*
source oracle's indexed circle fold to equal the terminal polynomial at every
raw draw. This includes repeated draws and the two queries in one pair. -/
theorem verified_authenticated_terminal (trace : Trace F) (raw : List Nat)
    (hverify : verified trace raw) (hauth : authenticated trace raw)
    (q : Nat) (hq : q ∈ raw) :
    row q < 2 ^ terminalDomainLog trace.profile ∧
    trace.y (row q) ≠ 0 ∧
    oracleFold trace (row q) = terminalAt trace (row q) := by
  rcases hverify with ⟨_, hraw⟩
  rcases hraw q hq with ⟨hbound, hy, hfold⟩
  exact ⟨row_lt_terminal_domain trace.profile q hbound, hy,
    (openedFold_eq_oracleFold trace raw hauth q hq).symm.trans hfold⟩

/-- Equal folded positions cannot be assigned inconsistent values by two
authenticated raw slots, even when the transcript contains duplicates. -/
theorem same_row_openings_agree (trace : Trace F) (raw : List Nat)
    (hauth : authenticated trace raw) (q₁ q₂ : Nat)
    (hq₁ : q₁ ∈ raw) (hq₂ : q₂ ∈ raw) (hrow : row q₁ = row q₂) :
    openedFold trace q₁ = openedFold trace q₂ := by
  rw [openedFold_eq_oracleFold trace raw hauth q₁ hq₁,
    openedFold_eq_oracleFold trace raw hauth q₂ hq₂, hrow]

/-- For an affine pair `(c₀ ± y c₁)`, the native inverse butterfly is twice
the line value at `alpha`; there is no division by two. -/
theorem affine_pair_terminal (c₀ c₁ alpha y : F) (hy : y ≠ 0) :
    pairFold alpha y⁻¹ (c₀ + y * c₁) (c₀ - y * c₁) =
      2 * (c₀ + alpha * c₁) :=
  pairFold_affine c₀ c₁ alpha y hy

/-- Hand calculation: `c₀=4`, `c₁=2`, `y=3`, `alpha=7` gives pair `(10,-2)`;
the zero-previous fold is `36`, matching a one-word terminal polynomial. -/
example : pairFold (7 : ℚ) (3 : ℚ)⁻¹ 10 (-2) =
    orderedLineEval [36] (11 : ℚ) := by
  norm_num [pairFold, orderedLineEval_single]

/-- Changing the claimed constant from `36` to `37` fails at the same row. -/
example : pairFold (7 : ℚ) (3 : ℚ)⁻¹ 10 (-2) ≠
    orderedLineEval [37] (11 : ℚ) := by
  norm_num [pairFold, orderedLineEval_single]

end S31.Gadgets.PcsFri.Cas07H1Terminal
