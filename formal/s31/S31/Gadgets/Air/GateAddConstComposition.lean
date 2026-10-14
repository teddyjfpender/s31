import S31.Gadgets.Air.GateSourcePhysicalRows

/-!
The first nonprimitive source-node composition over the installed QM31 AIR:
`add_const` lowers to one add row per packed word and one interned broadcast
constant address. Address/value joins, constant finalization, local AIR
authentication, and proof-cell authentication remain explicit premises.
-/

namespace S31.Gadgets.Air.GateAddConstComposition

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateSourcePhysicalRows

def broadcast (constant : F) : Quad :=
  ⟨constant, constant, constant, constant⟩

def activeLane (index : Nat) : Fin 4 :=
  ⟨index % 4, Nat.mod_lt _ (by decide)⟩

theorem coord_broadcast (constant : F) (lane : Fin 4) :
    coord (broadcast constant) lane = constant := by
  fin_cases lane <;> rfl

theorem coord_add (left right : Quad) (lane : Fin 4) :
    coord (Packed.add left right) lane = coord left lane + coord right lane := by
  fin_cases lane <;> rfl

/-- For arbitrary source length, including a short final packed word, every
active result lane equals its source operand plus the source constant. The
row at `j / 4` is the one certified by the native add-const port check. -/
theorem active_lanes_sound (length : Nat) (constant : F)
    (input output : Fin length → F) (rows : Nat → PhysicalRow)
    (hop : ∀ index : Fin length, (rows (index.val / 4)).op = .add)
    (hfixed : ∀ index : Fin length,
      (rows (index.val / 4)).flags = encode (rows (index.val / 4)).op)
    (hair : ∀ index : Fin length, ∀ residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals
        (rows (index.val / 4)).flags (rows (index.val / 4)).lhs
        (rows (index.val / 4)).rhs (rows (index.val / 4)).output,
        residual = 0)
    (hconstant : ∀ index : Fin length,
      (rows (index.val / 4)).rhs = broadcast constant)
    (hinput : ∀ index : Fin length,
      coord (rows (index.val / 4)).lhs (activeLane index.val) = input index)
    (houtput : ∀ index : Fin length,
      coord (rows (index.val / 4)).output (activeLane index.val) = output index) :
    ∀ index : Fin length, output index = input index + constant := by
  intro index
  let row := rows (index.val / 4)
  have hrow : row.output = evaluate row.op row.lhs row.rhs :=
    physical_row_sound row (hfixed index) (hair index)
  calc
    output index = coord row.output (activeLane index.val) := (houtput index).symm
    _ = coord (Packed.add row.lhs row.rhs) (activeLane index.val) := by
      rw [hrow, hop index]
      rfl
    _ = input index + constant := by
      rw [coord_add, hinput index, hconstant index, coord_broadcast]

/-- The same theorem in S31's executable M31 value domain. No assumption is
made about inactive padding lanes; only `Fin length` is claimed. -/
theorem active_lanes_m31_sound (length : Nat) (constant : S31.M31)
    (input output : Fin length → S31.M31) (rows : Nat → PhysicalRow)
    (hop : ∀ index : Fin length, (rows (index.val / 4)).op = .add)
    (hfixed : ∀ index : Fin length,
      (rows (index.val / 4)).flags = encode (rows (index.val / 4)).op)
    (hair : ∀ index : Fin length, ∀ residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals
        (rows (index.val / 4)).flags (rows (index.val / 4)).lhs
        (rows (index.val / 4)).rhs (rows (index.val / 4)).output,
        residual = 0)
    (hconstant : ∀ index : Fin length,
      (rows (index.val / 4)).rhs = broadcast (S31.Field.toZMod constant))
    (hinput : ∀ index : Fin length,
      coord (rows (index.val / 4)).lhs (activeLane index.val) =
        S31.Field.toZMod (input index))
    (houtput : ∀ index : Fin length,
      coord (rows (index.val / 4)).output (activeLane index.val) =
        S31.Field.toZMod (output index)) :
    ∀ index : Fin length, output index = input index + constant := by
  have hfield := active_lanes_sound length (S31.Field.toZMod constant)
    (fun index => S31.Field.toZMod (input index))
    (fun index => S31.Field.toZMod (output index)) rows
    hop hfixed hair hconstant hinput houtput
  intro index
  apply S31.Field.toZMod_injective
  simpa [S31.Field.toZMod_add] using hfield index

/-- Local AIR alone cannot identify which source constant was intended. The
wrong broadcast value gives an honest AIR row and a different source claim. -/
def wrongConstantRow : PhysicalRow :=
  { op := .add, flags := encode .add,
    lhs := ⟨1, 0, 0, 0⟩, rhs := broadcast 8,
    output := Packed.add ⟨1, 0, 0, 0⟩ (broadcast 8) }

theorem wrong_constant_row_accepts :
    ∀ residual ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      wrongConstantRow.flags wrongConstantRow.lhs wrongConstantRow.rhs
      wrongConstantRow.output, residual = 0 := by
  rw [S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq]
  exact Qm31Ops.honest_row .add _ _

theorem wrong_constant_changes_claim :
    coord wrongConstantRow.output ⟨0, by decide⟩ ≠ (1 : F) + 7 := by
  decide

end S31.Gadgets.Air.GateAddConstComposition
