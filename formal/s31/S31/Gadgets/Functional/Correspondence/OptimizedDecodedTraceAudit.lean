import S31.Gadgets.Functional.Correspondence.OptimizedDecodedTrace

/-!
Independent nonvacuity and grammar-scope checks for the conditional decoded
trace theorem. The first theorem proves that the pinned source, normalized
JSON, and compact IR bytes really satisfy its `checkBytes` premise. It does
not construct a decoded trace or prove verifier acceptance. The second theorem
exhibits an alias-let syntax that the executable optimized package parser
accepts but this Lean grammar deliberately excludes.
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
  decide

def aliasLetBytes : Token := token
  "circuit alias_add(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let copy = a; let b = copy + x; b }"

theorem alias_let_outside_modeled_grammar :
    parseBytes aliasLetBytes = none := by
  decide

end S31.Functional.Correspondence.OptimizedDecodedTraceAudit
