import S31.Gadgets.Air.GeneratedDirectGateBaseVm
import S31.Gadgets.Air.GeneratedDirectGateExtVm
import S31.Gadgets.Air.GeneratedDirectGateComposition

/-!
The selected Gate's nine arithmetic base-opcode roots and two extension
LogUp-opcode roots enter the one-component quotient fold in installed order.
This combines local Lean opcode interpreters. It does not establish that Zig
executes those instructions, that the remaining base mask reads authenticate
OODS cells, or that PCS/FRI proves the required low-degree statement.
-/

namespace S31.Gadgets.Air.DirectGateVmComposition

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.GeneratedDirectGateBaseVm
open S31.Gadgets.Air.GeneratedDirectGateExtVm
open S31.Gadgets.Air.GeneratedDirectGateComposition

/-- The eleven selected constraint roots, assembled from both Lean opcode
interpreters in the source-bound installed root order. -/
def vmRoots (cells : Cells) (alpha z claimedScaled : QM) : List QM :=
  arithmeticRoots (arithmeticCells cells) ++
    [(logupRoots cells alpha z claimedScaled).1,
     (logupRoots cells alpha z claimedScaled).2]

theorem vm_roots_eq_bytecode (cells : Cells)
    (alpha z claimedScaled : QM) :
    vmRoots cells alpha z claimedScaled =
      bytecodeRoots cells alpha z claimedScaled := by
  simp [vmRoots, bytecodeRoots, installedArithmeticRoots,
    arithmeticRoots_eq_generated, logupRoots_eq_generated,
    fromPartialEvals_three_zero]

theorem vm_roots_eq_pure (cells : Cells)
    (alpha z claimedScaled : QM) :
    vmRoots cells alpha z claimedScaled =
      pureRoots cells alpha z claimedScaled := by
  rw [vm_roots_eq_bytecode, bytecode_roots_eq_pure]

/-- The quotient fold of interpreted opcode roots is the pure AIR fold.
The nonzero zeroifier remains an explicit premise, as in the selected
generated composition theorem. -/
theorem vm_composition_eq_pure (cells : Cells)
    (alpha z claimedScaled coefficient zeroifier : QM)
    (hzero : zeroifier ≠ 0) :
    quotientFold coefficient zeroifier⁻¹
      (vmRoots cells alpha z claimedScaled) =
      S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots cells alpha z claimedScaled) / zeroifier := by
  rw [vm_roots_eq_bytecode]
  exact bytecode_composition_eq_pure cells alpha z claimedScaled
    coefficient zeroifier hzero

end S31.Gadgets.Air.DirectGateVmComposition
