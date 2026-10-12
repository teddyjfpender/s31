-- Generated from the checked one-component STWZEVA/1 direct Gate package.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Root order: extension registers 0..8 (base injections), then 88 and 96.
-- Native quotient/accumulator statements are checked source contracts.
import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
import S31.Gadgets.Air.DirectGateOodsComposition

namespace S31.Gadgets.Air.GeneratedDirectGateComposition

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition

/-- The installed root order of the selected direct Gate component. -/
def bytecodeRoots (cells : Cells) (alpha z claimedScaled : QM) : List QM :=
  installedArithmeticRoots (arithmeticCells cells) ++
    [(GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled).1,
     (GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled).2]

theorem bytecode_roots_eq_pure (cells : Cells) (alpha z claimedScaled : QM) :
    bytecodeRoots cells alpha z claimedScaled =
      pureRoots cells alpha z claimedScaled := by
  simp [bytecodeRoots, pureRoots,
    installed_arithmetic_roots_eq_oods_polynomials,
    GeneratedDirectGateBytecodeLogUp.bytecode_logup_eq]

/-- Native `zeroifier.inv()` succeeds only when the zeroifier is
nonzero. The selected component's eleven ordered quotient evaluations
then contribute this exact Horner fold. -/
theorem bytecode_composition_eq_pure (cells : Cells)
    (alpha z claimedScaled coefficient zeroifier : QM)
    (_hzero : zeroifier ≠ 0) :
    quotientFold coefficient zeroifier⁻¹
      (bytecodeRoots cells alpha z claimedScaled) =
      S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots cells alpha z claimedScaled) / zeroifier := by
  rw [bytecode_roots_eq_pure, quotient_fold_factor]
  rfl

end S31.Gadgets.Air.GeneratedDirectGateComposition
