import S31.Gadgets.Air.DirectGateOodsArithmetic

/-!
The two denominator-cleared `qm31_ops` LogUp polynomials at the verifier's
QM31 OODS samples. Every local fixed, main, and interaction sample may be a
nonbase QM31 value. The previous interaction sample is supplied separately;
its source from the native `at_prev` mask is a distinct obligation.
-/

namespace S31.Gadgets.Air.DirectGateOodsLogUp

open S31.Gadgets.Air.DirectGateOodsArithmetic

structure Cells where
  localFixed : Fin 8 → QM
  main : Fin 12 → QM
  interaction : Fin 8 → QM
  previousInteraction : Fin 8 → QM

/-- Six-word Gate denominator in relation/address/limb order, written in
Horner form independently of the bytecode's alpha-power sum. -/
def denominator (address a b c d alpha z : QM) : QM :=
  (((((d * alpha + c) * alpha + b) * alpha + a) * alpha +
    address) * alpha + 378353459) - z

def inputZeroDenominator (cells : Cells) (alpha z : QM) : QM :=
  denominator (cells.localFixed 4) (cells.main 0) (cells.main 1)
    (cells.main 2) (cells.main 3) alpha z

def inputOneDenominator (cells : Cells) (alpha z : QM) : QM :=
  denominator (cells.localFixed 5) (cells.main 4) (cells.main 5)
    (cells.main 6) (cells.main 7) alpha z

def outputDenominator (cells : Cells) (alpha z : QM) : QM :=
  denominator (cells.localFixed 6) (cells.main 8) (cells.main 9)
    (cells.main 10) (cells.main 11) alpha z

def firstColumn (cells : Cells) : QM :=
  fromPartialEvals (cells.interaction 0) (cells.interaction 1)
    (cells.interaction 2) (cells.interaction 3)

def lastColumn (cells : Cells) : QM :=
  fromPartialEvals (cells.interaction 4) (cells.interaction 5)
    (cells.interaction 6) (cells.interaction 7)

def previousLastColumn (cells : Cells) : QM :=
  fromPartialEvals (cells.previousInteraction 4)
    (cells.previousInteraction 5) (cells.previousInteraction 6)
    (cells.previousInteraction 7)

def pair (cells : Cells) (alpha z : QM) : QM :=
  firstColumn cells *
    (inputZeroDenominator cells alpha z *
      inputOneDenominator cells alpha z) -
    (inputZeroDenominator cells alpha z +
      inputOneDenominator cells alpha z)

/-- `claimedScaled` is the native extension parameter `claimed / rows`.
The trace size and transcript binding of that parameter are separate. -/
def last (cells : Cells) (alpha z claimedScaled : QM) : QM :=
  (lastColumn cells - previousLastColumn cells - firstColumn cells +
    claimedScaled) * outputDenominator cells alpha z +
    cells.localFixed 7

/-- Denominator clearing represents the intended reciprocal sum only when
both input denominators are nonzero. -/
theorem pair_zero_iff_reciprocal_sum (cells : Cells) (alpha z : QM)
    (h₀ : inputZeroDenominator cells alpha z ≠ 0)
    (h₁ : inputOneDenominator cells alpha z ≠ 0) :
    pair cells alpha z = 0 ↔
      firstColumn cells =
        (inputZeroDenominator cells alpha z)⁻¹ +
        (inputOneDenominator cells alpha z)⁻¹ := by
  dsimp [pair]
  field_simp
  constructor <;> intro h <;> linear_combination h

/-- The final denominator-cleared root enforces the running-sum increment
when the output denominator is nonzero. -/
theorem last_zero_iff_increment (cells : Cells) (alpha z claimedScaled : QM)
    (hout : outputDenominator cells alpha z ≠ 0) :
    last cells alpha z claimedScaled = 0 ↔
      lastColumn cells - previousLastColumn cells - firstColumn cells +
        claimedScaled =
        -(cells.localFixed 7) / outputDenominator cells alpha z := by
  dsimp [last]
  field_simp
  constructor <;> intro h <;> linear_combination h

end S31.Gadgets.Air.DirectGateOodsLogUp
