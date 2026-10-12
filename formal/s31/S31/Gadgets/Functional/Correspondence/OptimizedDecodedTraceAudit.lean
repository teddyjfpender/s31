import S31.Gadgets.Functional.Correspondence.OptimizedDecodedTrace

/-!
Independent nonvacuity and grammar-scope checks for the conditional decoded
trace theorem. The first theorem proves that the pinned source, normalized
JSON, and compact IR bytes really satisfy its `checkBytes` premise. The second
checks that a separate Python-admitted alias-let source now enters the Lean
grammar with exactly two arithmetic producers. The third proves exact byte
admission for the optimized alias plus CSE fixture. These checks do not
construct a decoded trace or prove verifier acceptance.
-/

namespace S31.Functional.Correspondence.OptimizedDecodedTraceAudit

open S31.Functional.SSATextBytes (Token token)
open S31.Functional.Correspondence.CanonicalDagOptimization
open S31.Functional.Correspondence.OptimizedTextBytes

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem pinned_checked_byte_triple :
    checkBytes reversedAndRepeatedBytes reversedAndRepeatedNormalized
      reversedAndRepeatedCanonical = some compactExample := by
  native_decide

def aliasLetBytes : Token := token
  "circuit alias_add(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let copy = a; let b = copy + x; b }"

theorem alias_let_inside_modeled_grammar :
    (parseBytes aliasLetBytes).map (·.raw) =
      some ⟨[⟨1, 0, 0, false⟩, ⟨2, 1, 0, false⟩], 2⟩ := by
  native_decide

theorem optimized_alias_exact_byte_triple :
    checkBytes aliasedReversedSource reversedAndRepeatedNormalized
      reversedAndRepeatedCanonical = some compactExample :=
  aliased_reversed_exact_bytes

end S31.Functional.Correspondence.OptimizedDecodedTraceAudit
