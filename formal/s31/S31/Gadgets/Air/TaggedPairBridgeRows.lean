import Mathlib.Tactic

/-!
The staged native tagged bridge has eight M31 endpoint columns and sixteen
rows. Its first eight row residuals are `current[lane] - next[lane]`.
Assuming the AIR-to-trace reduction makes those residuals zero on the first
fifteen logical row adjacencies, each endpoint column is constant. The native
AIR also checks the cyclic last-to-first edge, which this theorem does not
need. This is a local row fact, not a Gate/chip lookup or PCS theorem.
-/

namespace S31.Gadgets.Air.TaggedPairBridgeRows

variable {F : Type*} [AddGroup F]

/-- Residual for one of the eight endpoint columns at one of the first
fifteen logical row adjacencies. -/
def adjacentResidual (rows : Fin 8 → Fin 16 → F)
    (lane : Fin 8) (index : Fin 15) : F :=
  rows lane ⟨index.val, by omega⟩ -
    rows lane ⟨index.val + 1, by omega⟩

/-- All eight endpoint columns are constant if their native-form adjacent
equality residuals vanish on the sixteen-row bridge trace. -/
theorem eight_columns_constant (rows : Fin 8 → Fin 16 → F)
    (hzero : ∀ lane index, adjacentResidual rows lane index = 0) :
    ∀ lane row, rows lane row = rows lane ⟨0, by decide⟩ := by
  intro lane row
  have hprefix (n : Nat) (hn : n < 16) :
      rows lane ⟨n, hn⟩ = rows lane ⟨0, by decide⟩ := by
    induction n with
    | zero => rfl
    | succ n ih =>
        have hn15 : n < 15 := by omega
        have hadj :
            rows lane ⟨n, by omega⟩ =
              rows lane ⟨n + 1, by omega⟩ := by
          apply sub_eq_zero.mp
          exact hzero lane ⟨n, hn15⟩
        exact hadj.symm.trans (ih (by omega))
  exact hprefix row.val row.isLt

end S31.Gadgets.Air.TaggedPairBridgeRows
