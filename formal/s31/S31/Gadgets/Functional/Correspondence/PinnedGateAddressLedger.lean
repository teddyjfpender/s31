import S31.Gadgets.Functional.Correspondence.CheckedGateAddressLedger
import S31.Gadgets.Functional.Correspondence.PinnedFullFixedRoster
import S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Witness

/-!
Concrete address-ledger check for the complete 512-row pinned native square4
fixed roster. The nine external feeder addresses are those used by the
production direct-Gate component's public boundary in this fixture.
-/

namespace S31.Functional.Correspondence.PinnedGateAddressLedger

open S31.Functional.SSAAirColumnCells
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Functional.Correspondence.CheckedGateAddressLedger

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def cellAt (i : Nat) : ColumnCell :=
  let row := S31.Functional.Correspondence.PinnedFullFixedRoster.fixedRows[i]!
  { traceRow := i,
    addFlag := row[0]!, subFlag := row[1]!, mulFlag := row[2]!,
    pointwiseMulFlag := row[3]!, in0 := row[4]!, in1 := row[5]!,
    out := row[6]!, mults := row[7]! }

def cells : List ColumnCell := (List.range 512).map cellAt

def feederAddresses : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- These exact addresses are the projection of the existing pinned native
base witness's external Gate feeder events. The production rule is
`witness/trace.zig`'s `U_VAR_IDX = 2` and `lookupSum`'s use of addresses
`U_VAR_IDX` and `U_VAR_IDX + 1 + index` for eight public words. This fixture
equality does not itself authenticate a proof's external events. -/
theorem feeder_matches_pinned_native_fixture :
    feederAddresses =
      S31.Functional.Correspondence.PinnedNativeSquare4Witness.trace.externalUses.map
        Prod.fst ∧
    S31.Functional.Correspondence.PinnedNativeSquare4Witness.trace.externalYields =
      [] := by
  constructor
  · decide
  · rfl

/-- The complete pinned native fixed roster passes the bounded address-only
Gate ledger. This checks all 512 fixed rows and 1033 expected reads/yields,
not merely the selected source/public cells. -/
theorem pinned_square4_address_check :
    check cells feederAddresses [] = true := by decide

theorem pinned_square4_event_lengths :
    cells.length = 512 ∧
    (readAddresses cells feederAddresses).length = 1033 ∧
    (producedAddresses cells []).length = 1033 := by decide

/-- The pinned fixed address/multiplicity roster is balanced independently
of secret values whenever every gate and feeder event uses one coherent
address-to-value assignment. Actual native main-column coherence is a
separate correspondence obligation. -/
theorem pinned_square4_balanced_for_coherent_wire (wire : Nat → Quad) :
    balanced (gateRows cells wire) (wireEvents wire feederAddresses) [] := by
  simpa [wireEvents] using
    check_sound cells wire feederAddresses [] pinned_square4_address_check

end S31.Functional.Correspondence.PinnedGateAddressLedger
