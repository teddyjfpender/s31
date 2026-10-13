import Mathlib.Tactic

/-!
The S-two whitepaper, Protocols 2 and 3, permits `r + 1` circle/line folds
with `0 ≤ r < n`; the final line polynomial is sent in plain and checked in
`F[x]_{< 2^(n-1-r)}`. This module translates the *shape* of a proposed
`heightCount`-fold native cascade into those published indices. It does not
establish that native openings, folds, terminal evaluation, or transcript
sampling refine the paper's protocol.
-/

namespace S31.Gadgets.PcsFri.ShortTerminalGeometry

/-- Initial domain `2^k`, blowup `2^beta`, and `h` native folds. -/
structure Shape where
  k : Nat
  beta : Nat
  h : Nat
  positiveBlowup : 0 < beta
  positiveFolds : 0 < h
  fits : h + beta ≤ k

def paperN (s : Shape) : Nat := s.k - s.beta
def paperR (s : Shape) : Nat := s.h - 1
def terminalCoeffLog (s : Shape) : Nat := s.k - s.h - s.beta
def terminalDomainLog (s : Shape) : Nat := s.k - s.h

/-- The paper's hypothesis `0 ≤ r < n` follows from native profile shape. -/
theorem paperR_lt_paperN (s : Shape) : paperR s < paperN s := by
  have hk := s.fits
  have hh := s.positiveFolds
  dsimp [paperR, paperN]
  omega

/-- The native terminal coefficient exponent is the paper's `n-1-r`. -/
theorem terminalCoeffLog_eq_paper (s : Shape) :
    terminalCoeffLog s = paperN s - 1 - paperR s := by
  have hk := s.fits
  have hh := s.positiveFolds
  dsimp [terminalCoeffLog, paperN, paperR]
  omega

/-- The terminal evaluation domain retains the original blowup. -/
theorem terminalDomainLog_eq_coeff_add_blowup (s : Shape) :
    terminalDomainLog s = terminalCoeffLog s + s.beta := by
  have hk := s.fits
  dsimp [terminalDomainLog, terminalCoeffLog]
  omega

theorem terminalDomainRows_eq_coeffWords_mul_blowup (s : Shape) :
    2 ^ terminalDomainLog s = 2 ^ terminalCoeffLog s * 2 ^ s.beta := by
  rw [terminalDomainLog_eq_coeff_add_blowup, pow_add]

/-- `D₀=2^22`, `B=2`, eight folds: the published terminal space has
8192 coefficients evaluated over a 16384-point line domain. -/
def illustrative : Shape := ⟨22, 1, 8, by omega, by omega, by omega⟩

theorem illustrative_paper_index :
    paperN illustrative = 21 ∧ paperR illustrative = 7 := by
  norm_num [paperN, paperR, illustrative]

theorem illustrative_terminal :
    2 ^ terminalCoeffLog illustrative = 8192 ∧
    2 ^ terminalDomainLog illustrative = 16384 := by
  norm_num [terminalCoeffLog, terminalDomainLog, illustrative]

/-- With the draft dense host prover's log-size cap 16 and the same eight
folds, the terminal has 128 coefficients on 256 evaluation points. -/
def denseHostMaximal : Shape := ⟨16, 1, 8, by omega, by omega, by omega⟩

theorem denseHostMaximal_terminal :
    paperN denseHostMaximal = 15 ∧
    paperR denseHostMaximal = 7 ∧
    2 ^ terminalCoeffLog denseHostMaximal = 128 ∧
    2 ^ terminalDomainLog denseHostMaximal = 256 := by
  norm_num [paperN, paperR, terminalCoeffLog, terminalDomainLog, denseHostMaximal]

end S31.Gadgets.PcsFri.ShortTerminalGeometry
