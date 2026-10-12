-- Generated from the checked selected direct Gate package and native source contracts.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Extension source order: alpha^1..alpha^5, z, claimed_sum / 512.
-- `z` is draw 0 and `alpha` is draw 1 after main commitment.
import S31.Gadgets.Air.DirectGateTranscriptParams
import S31.Gadgets.Air.GeneratedDirectGateComposition

namespace S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateTranscriptParams

/-- Supply the installed bytecode using the exact selected verifier
lookup pair `(z, alpha)` and first claimed sum. -/
def transcriptRoots (cells : Cells) (z alpha claimed : QM) : List QM :=
  GeneratedDirectGateComposition.bytecodeRoots cells alpha z
    (extensionParam z alpha claimed 6)

theorem transcript_roots_eq_pure (cells : Cells) (z alpha claimed : QM) :
    transcriptRoots cells z alpha claimed =
      pureRoots cells alpha z (claimed / 512) := by
  simp [transcriptRoots, extensionParam, claimed_scaled_eq_div,
    GeneratedDirectGateComposition.bytecode_roots_eq_pure]

theorem transcript_composition_eq_pure (cells : Cells)
    (z alpha claimed coefficient zeroifier : QM)
    (_hzero : zeroifier ≠ 0) :
    quotientFold coefficient zeroifier⁻¹
      (transcriptRoots cells z alpha claimed) =
      S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots cells alpha z (claimed / 512)) / zeroifier := by
  rw [transcript_roots_eq_pure, quotient_fold_factor]
  rfl

end S31.Gadgets.Air.GeneratedDirectGateTranscriptParams
