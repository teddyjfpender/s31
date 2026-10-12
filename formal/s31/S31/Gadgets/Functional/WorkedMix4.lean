import S31.Gadgets.Sequence

/-!
Hand-checkable three-round instance for `returned_mix4_3.s31`.
The Python docs checker separately checks that the source and direct form
normalize to one `repeat` node with body `mix4`. This file proves the
abstract step values and arbitrary-witness output binding for that body.
-/

namespace S31.Functional

private def word (n : Nat) : M31 := RiscvRefinement.M31.reduce n

def mixInput : List M31 := [word 1, word 2, word 3, word 4]
def mixRound1 : List M31 := [word 11, word 12, word 13, word 14]
def mixRound2 : List M31 := [word 61, word 62, word 63, word 64]
def mixRound3 : List M31 := [word 311, word 312, word 313, word 314]

theorem mixRound1_value : applyStep mixInput .mix4 = mixRound1 := by decide
theorem mixRound2_value : applyStep mixRound1 .mix4 = mixRound2 := by decide
theorem mixRound3_value : applyStep mixRound2 .mix4 = mixRound3 := by decide

theorem mixThreeRounds_value : repeatBody [.mix4] 3 mixInput = mixRound3 := by
  simp [repeatBody, applyBody, mixRound1_value, mixRound2_value, mixRound3_value]

/-- Any satisfying abstract trace has the documented output; the documented
output has an honest trace. -/
theorem mixThreeRounds_accepts (claimed : List M31) :
    Gadgets.Sequence.RepeatAccepts [.mix4] 3 mixInput claimed ↔
      claimed = mixRound3 := by
  simpa only [mixThreeRounds_value] using
    (Gadgets.Sequence.repeat_sound_complete [.mix4] 3 mixInput claimed)

end S31.Functional
