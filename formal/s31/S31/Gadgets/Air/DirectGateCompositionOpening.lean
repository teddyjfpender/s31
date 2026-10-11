import S31.Gadgets.Air.DirectGateOodsOpenings

/-!
The selected direct Gate verifier uses the default one-level composition
split. Its final proof-sample tree has two QM31 coefficient chunks, each
represented by four singleton coordinate columns. The circle-point factor
is supplied by native `repeatedDouble(composition_log_size - 2).x`.

This module only models extraction from supplied values. It says nothing
about those values opening the committed composition columns.
-/

namespace S31.Gadgets.Air.DirectGateCompositionOpening

open S31.Gadgets.Air.DirectGateOodsArithmetic

/-- Exact accepted eight-column shape of native split-one extraction. -/
def extractSplitOne (factor : QM) : List (List QM) → Option QM
  | [[a₀], [a₁], [a₂], [a₃], [b₀], [b₁], [b₂], [b₃]] =>
      some (fromPartialEvals a₀ a₁ a₂ a₃ +
        factor * fromPartialEvals b₀ b₁ b₂ b₃)
  | _ => none

theorem extract_exact (factor a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : QM) :
    extractSplitOne factor
      [[a₀], [a₁], [a₂], [a₃], [b₀], [b₁], [b₂], [b₃]] =
      some (fromPartialEvals a₀ a₁ a₂ a₃ +
        factor * fromPartialEvals b₀ b₁ b₂ b₃) := by
  rfl

/-- A missing coordinate cannot be silently filled with zero. -/
theorem extract_rejects_missing_column (factor a₀ a₁ a₂ a₃ b₀ b₁ b₂ : QM) :
    extractSplitOne factor
      [[a₀], [a₁], [a₂], [a₃], [b₀], [b₁], [b₂]] = none := by
  rfl

theorem extract_rejects_extra_column (factor a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ x : QM) :
    extractSplitOne factor
      [[a₀], [a₁], [a₂], [a₃], [b₀], [b₁], [b₂], [b₃], [x]] = none := by
  rfl

/-- A column with two samples cannot be silently truncated. -/
theorem extract_rejects_two_samples (factor a₀ x a₁ a₂ a₃ b₀ b₁ b₂ b₃ : QM) :
    extractSplitOne factor
      [[a₀, x], [a₁], [a₂], [a₃], [b₀], [b₁], [b₂], [b₃]] = none := by
  rfl

end S31.Gadgets.Air.DirectGateCompositionOpening
