import S31.Gadgets.Air.NativeQm31AirProof

/-!
The quantified local AIR half of the source-to-physical-row certificate. The
native certificate checker supplies the source/canonical row map and compares
the fixed selector and address cells with the installed preprocessed circuit.
The assumptions below deliberately leave authentication of arbitrary proof
openings, the Gate lookup, and the source parser outside this theorem.
-/

namespace S31.Gadgets.Air.GateSourcePhysicalRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

structure PhysicalRow where
  op : Qm31Ops.Op
  flags : Flags
  lhs : Quad
  rhs : Quad
  output : Quad

structure SourceNode where
  name : String
  canonicalId : Nat
  physicalRows : List Nat

/-- A source alias inherits the same canonical row list. This models the
native certificate's checked CSE aliases, without assuming unique names. -/
structure Certificate where
  sourceNodes : List SourceNode
  canonicalRows : Nat → List Nat
  physical : Nat → PhysicalRow
  sourceMap : ∀ node ∈ sourceNodes,
    node.physicalRows = canonicalRows node.canonicalId
  fixedSelector : ∀ node ∈ sourceNodes, ∀ row ∈ node.physicalRows,
    (physical row).flags = encode (physical row).op

/-- The native nine residuals, including one-hot selectors and all four
packed output limbs, force the chosen operation at any certified row. This
uses the proved exact equality with the installed AIR expression tree. -/
theorem physical_row_sound (row : PhysicalRow)
    (hfixed : row.flags = encode row.op)
    (hair : ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      row.flags row.lhs row.rhs row.output, r = 0) :
    row.output = evaluate row.op row.lhs row.rhs := by
  rw [S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq] at hair
  exact (accepts_encoded row.op row.lhs row.rhs row.output).mp
    (by simpa [accepts, hfixed] using hair)

/-- Applies to every source node and every physical QM31 row in its checked
canonical span, including programs with arbitrarily many nodes and aliases. -/
theorem every_source_row_sound (cert : Certificate)
    (hair : ∀ node ∈ cert.sourceNodes, ∀ index ∈ node.physicalRows,
      ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
        (cert.physical index).flags (cert.physical index).lhs
        (cert.physical index).rhs (cert.physical index).output, r = 0)
    (node : SourceNode) (hnode : node ∈ cert.sourceNodes)
    (index : Nat) (hindex : index ∈ node.physicalRows) :
    (cert.physical index).output = evaluate (cert.physical index).op
      (cert.physical index).lhs (cert.physical index).rhs := by
  exact physical_row_sound (cert.physical index)
    (cert.fixedSelector node hnode index hindex)
    (hair node hnode index hindex)

/-- Two names that resolve to the same canonical node cannot silently claim
different physical row lists. -/
theorem alias_rows_equal (cert : Certificate)
    (left right : SourceNode)
    (hl : left ∈ cert.sourceNodes) (hr : right ∈ cert.sourceNodes)
    (hid : left.canonicalId = right.canonicalId) :
    left.physicalRows = right.physicalRows := by
  rw [cert.sourceMap left hl, cert.sourceMap right hr, hid]

end S31.Gadgets.Air.GateSourcePhysicalRows
