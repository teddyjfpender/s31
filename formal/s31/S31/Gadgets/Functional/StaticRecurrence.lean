import S31.Gadgets.Sequence

/-!
Mathematical meaning of the static `square; add_const 7` step in
`functional_step16.s31` and `captured_step16.s31`. The Python compiler checks
that both source forms emit this body; this module proves the body acts
independently on every lane and that arbitrary satisfying repeat witnesses
bind the output for any number of rounds. It does not prove source parsing or
the production AIR correspondence.
-/

namespace S31.Functional

private def seven : M31 := RiscvRefinement.M31.reduce 7

def squarePlusSeven (x : M31) : M31 := x * x + seven

def squarePlusSevenBody : List Step := [.square, .add_const seven]

theorem squarePlusSevenBody_lanes (xs : List M31) :
    applyBody squarePlusSevenBody xs = xs.map squarePlusSeven := by
  simp [squarePlusSevenBody, applyBody, applyStep, squarePlusSeven,
    List.map_map, Function.comp_def]

def squarePlusSevenRounds : Nat → M31 → M31
  | 0, x => x
  | n + 1, x => squarePlusSevenRounds n (squarePlusSeven x)

/-- The recurrence is pointwise for every array length and round count. -/
theorem squarePlusSevenRepeat_lanes (n : Nat) (xs : List M31) :
    repeatBody squarePlusSevenBody n xs = xs.map (squarePlusSevenRounds n) := by
  induction n generalizing xs with
  | zero => simp [repeatBody, squarePlusSevenRounds]
  | succ n ih =>
      rw [repeatBody, squarePlusSevenBody_lanes, ih]
      simp [List.map_map, squarePlusSevenRounds, Function.comp_def]

/-- All satisfying witnesses yield the same list of lane-wise results; the
honest recurrence yields a satisfying witness. -/
theorem squarePlusSevenRepeat_accepts (n : Nat) (xs ys : List M31) :
    Gadgets.Sequence.RepeatAccepts squarePlusSevenBody n xs ys ↔
      ys = xs.map (squarePlusSevenRounds n) := by
  simpa only [squarePlusSevenRepeat_lanes] using
    (Gadgets.Sequence.repeat_sound_complete squarePlusSevenBody n xs ys)

end S31.Functional
