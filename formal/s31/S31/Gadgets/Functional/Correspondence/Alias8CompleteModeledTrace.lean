import S31.Gadgets.Functional.Correspondence.AliasCheckedPhysicalModeledComposition
import S31.Gadgets.Functional.Correspondence.Alias8ConstantIslandCertificate
import S31.Gadgets.Functional.Correspondence.GeneratedNativeSourceCells

/-!
The exact case07 alias source and native diagnostic have a complete modeled
512-row direct-Gate trace for every four-lane input. The separately admitted
producer-only spelling is explicit. This theorem is about a synthetic trace;
it does not bind it to native PCS openings or prove FRI soundness.
-/

namespace S31.Functional.Correspondence.Alias8CompleteModeledTrace

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAPublicInputBinding
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMutationRows
open S31.Functional.Correspondence.GeneratedAlias8NativeFixture
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.Alias8ConstantIslandCertificate
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence
open S31.Functional.Correspondence.AliasCheckedPhysicalModeledComposition

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-- The simple spelling has exactly the same eight producer instructions and
selected wire as the admitted alias source. Its byte check is separate from
the alias parser's canonical-IR admission. -/
theorem direct_spelling_check :
    checkRelation GeneratedAlias8NativeFixture.directBytes
      case07NormalizedBytes = some case07Certificate := by decide

/-- The address-only Gate ledger closes on all 512 fixed rows, including the
479 checked native constant rows, with one unit feeder and eight scalar
public feeders. This is ideal modeled event balance, not native LogUp proof. -/
theorem complete_address_check :
    CheckedGateAddressLedger.check
      (joinedCells case07Certificate
        Alias8ConstantIslandCertificate.constantCells)
      [2, 3, 4, 5, 6, 7, 8, 9, 10] [] = true := by decide

/-- For every four-lane input, the admitted case07 alias program has a
source-consistent, fixed-row-complete physical model with zero installed
arithmetic roots and balanced ideal Gate events. The 479-row island comes
from a checked native diagnostic export, not authenticated openings. -/
theorem complete_modeled_trace (input : Lanes) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      SSAAliasTextBytes.denotation case07Bytes input = some output ∧
      physical = traceWithExternal
        (joinedCells case07Certificate
          Alias8ConstantIslandCertificate.constantCells)
        wire [2, 3, 4, 5, 6, 7, 8, 9, 10] [] ∧
      (joinedCells case07Certificate
        Alias8ConstantIslandCertificate.constantCells).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells case07Certificate
        Alias8ConstantIslandCertificate.constantCells,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells case07Certificate
        Alias8ConstantIslandCertificate.constantCells,
        fixedMatches physical cell) ∧
      allArithmeticRootsZero physical ∧
      wire (address case07Certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary case07Certificate (compiledAddRows case07Certificate)
        wire input ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  exact checked_alias_with_direct_physical_trace
    case07Bytes case07NormalizedBytes case07CanonicalBytes
    GeneratedAlias8NativeFixture.directBytes case07NormalizedBytes
    case07Certificate input Alias8ConstantIslandCertificate.constantCells
    Alias8ConstantIslandCertificate.nativeValues
    [2, 3, 4, 5, 6, 7, 8, 9, 10] []
    GeneratedNativeSourceCells.case07_source_to_native_cells.1
    direct_spelling_check alias8_constant_check complete_address_check

end S31.Functional.Correspondence.Alias8CompleteModeledTrace
