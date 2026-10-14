import S31.Gadgets.Functional.Correspondence.StructuralNativeGateOwnership

/-!
The local join from physical direct-Gate cells to the source-gate AIR premise.
Each covered source gate must occur at an actual physical row with the exact
preprocessed selector and addresses and all twelve base coordinates. The
nine local AIR residuals are required on the physical rows themselves. This
does not assert that a STARK proof authenticates those cells or residuals.
-/

namespace S31.Functional.Correspondence.StructuralPhysicalAirBridge

open S31
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeGateOwnership
open S31.Functional.Correspondence.StructuralNativeTraceDecoder
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open S31.Functional.Correspondence.GeneralLinearSSAEffects
open S31.Gadgets.Air.Qm31Ops

/-- One row of the installed direct-Gate eight fixed and twelve base columns.
The multiplicity cell belongs to Gate LogUp and is carried here but is not
used by the nine arithmetic residuals. -/
structure PhysicalGateRow where
  flags : Flags
  in0 : Nat
  in1 : Nat
  out : Nat
  multiplicity : Nat
  left : Quad
  right : Quad
  result : Quad

/-- Exact selector, address, and all-coordinate equality with a source gate. -/
def PhysicalGateRow.matches (row : PhysicalGateRow)
    (wire : Nat → Quad) (gate : Gate) : Prop :=
  row.flags = encode gate.op.airOp ∧
  row.in0 = gate.in0 ∧ row.in1 = gate.in1 ∧ row.out = gate.out ∧
  row.left = wire gate.in0 ∧ row.right = wire gate.in1 ∧
  row.result = wire gate.out

/-- Every source gate has a row in the physical roster. A source gate may be
shared by several SSA steps after common subexpression elimination. -/
def CoversGates (rows : List PhysicalGateRow)
    (wire : Nat → Quad) (gates : List Gate) : Prop :=
  ∀ gate ∈ gates, ∃ row ∈ rows, row.matches wire gate

/-- Every selected physical row satisfies the native nine-residual AIR. The
actual proof-to-row implication is a separate cryptographic obligation. -/
def AcceptedPhysicalRows (rows : List PhysicalGateRow) : Prop :=
  ∀ row ∈ rows, ∀ residual ∈
    S31.Gadgets.Air.NativeQm31Air.residuals row.flags
      (packM31 row.left) (packM31 row.right) (packM31 row.result),
    residual = 0

/-- Exact physical cells plus their local AIR evaluations discharge the
abstract `NativeAirRows` premise for every source-owned gate. -/
theorem physical_rows_imply_native_air (rows : List PhysicalGateRow)
    (wire : Nat → Quad) (gates : List Gate)
    (hcover : CoversGates rows wire gates)
    (hrows : AcceptedPhysicalRows rows) :
    NativeAirRows wire gates := by
  intro gate hgate residual hresidual
  obtain ⟨row, hrow, hmatch⟩ := hcover gate hgate
  rcases hmatch with ⟨hflags, hin0, hin1, hout, hleft, hright, hresult⟩
  have hphysical : residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals row.flags
        (packM31 row.left) (packM31 row.right) (packM31 row.result) := by
    simpa [hflags, hleft, hright, hresult] using hresidual
  exact hrows row hrow residual hphysical

/-- The general bounded source theorem now consumes physical row cells,
instead of an unqualified abstract arithmetic-AIR premise. It still assumes
the source certificate, native graph projection, exact row coverage, public
ports, assertions, and local AIR acceptance. -/
theorem checked_source_from_physical_rows {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes : String)
    (ssa : EmittedSSA) (meaning : Source) (certificate : Certificate)
    (graph : ExportedGraph) (rows : List PhysicalGateRow)
    (inputs : Nat → Lanes n) (claimed : Lanes n) (final : List (Lanes n))
    (hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hgraph : decodeExportedGraph graphBytes = .ok graph)
    (hnames : graph.sourceNames = ssa.names)
    (hlanes : ssa.lane_count = n)
    (hports : checkInputPorts hn graph.wire graph.addresses
      certificate.inputs inputs = true)
    (howned : checkOwnedSteps hn graph.wire graph.gates graph.addresses
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      certificate.steps = some final)
    (houtput : checkOutputPort hn graph.wire graph.addresses final
      certificate.output claimed = true)
    (hassert : checkAssertions final certificate.assertions = true)
    (hcover : CoversGates rows graph.wire graph.gates)
    (hrows : AcceptedPhysicalRows rows) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes inputs claimed := by
  exact (checked_direct_owned_source_air_sound hn sourceBytes
    certificateBytes graphBytes ssa meaning certificate graph inputs claimed
    final hsource hgraph hnames hlanes hports howned houtput hassert
    (physical_rows_imply_native_air rows graph.wire graph.gates hcover hrows)).1

end S31.Functional.Correspondence.StructuralPhysicalAirBridge
