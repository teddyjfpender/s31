import S31.Gadgets.Air.SourceMixedFixedLocalCertificate

/-!
Construct the source-owned canonical Gate row list directly from one decoded
512-row trace. Exact N1/N8 fixed-column exports prove every input and output
address is below the native 512-variable bound. The resulting boundary keeps
the source call metadata, words, public outputs, and external events supplied
by its template; only its Gate rows are replaced. Its decoded-to-boundary row
identity is then a theorem by construction, not an external premise.

This construction does not prove that the decoded trace is authenticated by a
succinct proof, that source metadata equals native inspection, or that its
main values satisfy the remaining `ValueAt` pins.
-/

namespace S31.Gadgets.Air.SourceMixedDecodedBoundary

open S31.Gadgets.Packed
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedScheduledPublicPath
open S31.Gadgets.Air.SourceMixedFixedLocalCertificate
open S31.Gadgets.Air.SourceMixedFixedOutputSchedule
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.UnpackRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every decoded Gate address is a declared circuit variable. The native
constructor checks all 512 rows, including inactive ones. -/
def DeclaredAddressBounds (trace : Trace 9) : Prop :=
  ∀ i : Fin 512,
    (trace.fixed i ⟨4, by decide⟩).val < 512 ∧
    (trace.fixed i ⟨5, by decide⟩).val < 512 ∧
    (trace.fixed i ⟨6, by decide⟩).val < 512

/-- Turn a decoded row into a canonical row while retaining every main
value, flag, address, and multiplicity exactly. -/
def canonicalRowAt (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) (i : Fin 512) : CanonicalRow :=
  { in0Address := ⟨(trace.fixed i ⟨4, by decide⟩).val,
      Nat.lt_trans (hbound i).1 (by decide)⟩,
    in1Address := ⟨(trace.fixed i ⟨5, by decide⟩).val,
      Nat.lt_trans (hbound i).2.1 (by decide)⟩,
    outAddress := ⟨(trace.fixed i ⟨6, by decide⟩).val,
      Nat.lt_trans (hbound i).2.2 (by decide)⟩,
    flags := (row trace i).flags,
    in0 := (row trace i).in0,
    in1 := (row trace i).in1,
    output := (row trace i).output,
    multiplicity := (row trace i).multiplicity }

theorem canonicalRowAt_toGate (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) (i : Fin 512) :
    (canonicalRowAt trace hbound i).toGate = row trace i := by
  rfl

def canonicalRows (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) : List CanonicalRow :=
  List.ofFn (canonicalRowAt trace hbound)

theorem canonicalRows_toGate (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) :
    (canonicalRows trace hbound).map CanonicalRow.toGate =
      nativeRows trace := by
  simp only [canonicalRows, nativeRows, List.map_ofFn]
  congr 1

/-- Preserve all source metadata while sourcing Gate rows from the decoded
trace itself. -/
def boundaryFromTrace {N : Nat} (template : Boundary N) (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) : Boundary N :=
  { template with rows := canonicalRows trace hbound }

theorem boundaryFromTrace_rows (template : Boundary N) (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) :
    nativeRows trace =
      (boundaryFromTrace template trace hbound).rows.map CanonicalRow.toGate := by
  exact (canonicalRows_toGate trace hbound).symm

private theorem n1_export_address_bounds :
    ∀ i : Fin 512,
      (N1.fixedAt i ⟨4, by decide⟩).val < 512 ∧
      (N1.fixedAt i ⟨5, by decide⟩).val < 512 ∧
      (N1.fixedAt i ⟨6, by decide⟩).val < 512 := by decide

private theorem n8_export_address_bounds :
    ∀ i : Fin 512,
      (N8.fixedAt i ⟨4, by decide⟩).val < 512 ∧
      (N8.fixedAt i ⟨5, by decide⟩).val < 512 ∧
      (N8.fixedAt i ⟨6, by decide⟩).val < 512 := by decide

theorem n1_trace_bounds (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c) :
    DeclaredAddressBounds trace := by
  intro i
  rw [hfixed i ⟨4, by decide⟩, hfixed i ⟨5, by decide⟩,
    hfixed i ⟨6, by decide⟩]
  exact n1_export_address_bounds i

theorem n8_trace_bounds (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c) :
    DeclaredAddressBounds trace := by
  intro i
  rw [hfixed i ⟨4, by decide⟩, hfixed i ⟨5, by decide⟩,
    hfixed i ⟨6, by decide⟩]
  exact n8_export_address_bounds i

def n1Boundary (template : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c) : Boundary 1 :=
  boundaryFromTrace template trace (n1_trace_bounds trace hfixed)

def n8Boundary (template : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c) : Boundary 8 :=
  boundaryFromTrace template trace (n8_trace_bounds trace hfixed)

/-- Source-shaped metadata for the pinned chain. The caller supplies the
remaining endpoint words and public outputs through `template`; only the
first four input words are fixed by the declared initial state. -/
def pinnedBoundary {N : Nat} (hN : N ≤ 8) (template : Boundary N)
    (trace : Trace 9) (hbound : DeclaredAddressBounds trace)
    (initial : State) : Boundary N :=
  { template with
    rounds := fun _ => 16
    constants := fun call => (13 + call.val : F)
    addresses := fun call slot => canonicalAddress hN call slot
    words := fun call slot =>
      if call.val = 0 then
        if hslot : slot.val < 4 then initial ⟨slot.val, hslot⟩
        else template.words call slot
      else template.words call slot
    rows := canonicalRows trace hbound }

theorem pinnedBoundary_rows {N : Nat} (hN : N ≤ 8)
    (template : Boundary N) (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) (initial : State) :
    nativeRows trace =
      (pinnedBoundary hN template trace hbound initial).rows.map
        CanonicalRow.toGate := by
  exact (canonicalRows_toGate trace hbound).symm

theorem pinnedBoundary_first {N : Nat} (hN : N ≤ 8) (hpositive : 0 < N)
    (template : Boundary N) (trace : Trace 9)
    (hbound : DeclaredAddressBounds trace) (initial : State) :
    (pinnedBoundary hN template trace hbound initial).start
      ⟨0, hpositive⟩ = initial := by
  funext lane
  simp [Boundary.start, pinnedBoundary,
    S31.Gadgets.Air.TaggedPairSourceCorrespondence.bridgeInputLane]

def n1PinnedBoundary (template : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c) (initial : State) : Boundary 1 :=
  pinnedBoundary (by decide) template trace (n1_trace_bounds trace hfixed)
    initial

def n8PinnedBoundary (template : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c) (initial : State) : Boundary 8 :=
  pinnedBoundary (by decide) template trace (n8_trace_bounds trace hfixed)
    initial

/-- The N1 local public schedule with decoded-to-boundary Gate row equality
eliminated. Value pins are about the reconstructed trace-owned boundary. -/
theorem n1_local_schedule_from_decoded (template : Boundary 1)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (rows : ∀ call, Fin (template.rounds call) → NativeRow)
    (initial : State)
    (hbaseline : template.baselineYields = [])
    (haddresses : ∀ call slot,
      template.addresses call slot =
        canonicalAddress (by decide : 1 ≤ 8) call slot)
    (hfirst : template.start ⟨0, by decide⟩ = initial)
    (hconstants : ∀ call, template.constants call = (13 + call.val : F))
    (hpackedInitial : ValueAt (n1Boundary template trace hfixed) 22
      (packState initial))
    (hpackedFinal : ValueAt (n1Boundary template trace hfixed) (22 + 10 * 1)
      (packState ((n1Boundary template trace hfixed).finish
        ⟨1 - 1, by omega⟩)))
    (hzero : ValueAt (n1Boundary template trace hfixed) 0 (base 0))
    (hunit : ∀ lane, ValueAt (n1Boundary template trace hfixed)
      (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt (n1Boundary template trace hfixed)
        (inverseAddress 1 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 1 ≤ 8) (by decide : 0 < 1)
      (n1Boundary template trace hfixed) rows initial := by
  have hrows : nativeRows trace =
      (n1Boundary template trace hfixed).rows.map CanonicalRow.toGate :=
    boundaryFromTrace_rows template trace (n1_trace_bounds trace hfixed)
  exact n1_local_schedule (n1Boundary template trace hfixed) rows initial
    trace hfixed hrows (by simpa [n1Boundary, boundaryFromTrace] using hbaseline)
    (by simpa [n1Boundary, boundaryFromTrace] using haddresses)
    (by simpa [n1Boundary, boundaryFromTrace] using hfirst)
    (by simpa [n1Boundary, boundaryFromTrace] using hconstants)
    hpackedInitial hpackedFinal hzero hunit hinverse

/-- The same construction for the N8 chain. -/
theorem n8_local_schedule_from_decoded (template : Boundary 8)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (rows : ∀ call, Fin (template.rounds call) → NativeRow)
    (initial : State)
    (hbaseline : template.baselineYields = [])
    (haddresses : ∀ call slot,
      template.addresses call slot =
        canonicalAddress (by decide : 8 ≤ 8) call slot)
    (hfirst : template.start ⟨0, by decide⟩ = initial)
    (hconstants : ∀ call, template.constants call = (13 + call.val : F))
    (hpackedInitial : ValueAt (n8Boundary template trace hfixed) 22
      (packState initial))
    (hpackedFinal : ValueAt (n8Boundary template trace hfixed) (22 + 10 * 8)
      (packState ((n8Boundary template trace hfixed).finish
        ⟨8 - 1, by omega⟩)))
    (hzero : ValueAt (n8Boundary template trace hfixed) 0 (base 0))
    (hunit : ∀ lane, ValueAt (n8Boundary template trace hfixed)
      (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt (n8Boundary template trace hfixed)
        (inverseAddress 8 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 8 ≤ 8) (by decide : 0 < 8)
      (n8Boundary template trace hfixed) rows initial := by
  have hrows : nativeRows trace =
      (n8Boundary template trace hfixed).rows.map CanonicalRow.toGate :=
    boundaryFromTrace_rows template trace (n8_trace_bounds trace hfixed)
  exact n8_local_schedule (n8Boundary template trace hfixed) rows initial
    trace hfixed hrows (by simpa [n8Boundary, boundaryFromTrace] using hbaseline)
    (by simpa [n8Boundary, boundaryFromTrace] using haddresses)
    (by simpa [n8Boundary, boundaryFromTrace] using hfirst)
    (by simpa [n8Boundary, boundaryFromTrace] using hconstants)
    hpackedInitial hpackedFinal hzero hunit hinverse

/-- N1 certificate for a trace-owned boundary whose source schedule metadata
is fixed by construction. No row-identity, address, constant, or first-state
premise is supplied by the caller. -/
theorem n1_pinned_local_schedule (template : Boundary 1)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (initial : State)
    (rows : ∀ call, Fin ((n1PinnedBoundary template trace hfixed initial).rounds call) →
      NativeRow)
    (hbaseline : template.baselineYields = [])
    (hpackedInitial : ValueAt (n1PinnedBoundary template trace hfixed initial)
      22 (packState initial))
    (hpackedFinal : ValueAt (n1PinnedBoundary template trace hfixed initial)
      (22 + 10 * 1)
      (packState ((n1PinnedBoundary template trace hfixed initial).finish
        ⟨1 - 1, by omega⟩)))
    (hzero : ValueAt (n1PinnedBoundary template trace hfixed initial)
      0 (base 0))
    (hunit : ∀ lane, ValueAt (n1PinnedBoundary template trace hfixed initial)
      (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt (n1PinnedBoundary template trace hfixed initial)
        (inverseAddress 1 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 1 ≤ 8) (by decide : 0 < 1)
      (n1PinnedBoundary template trace hfixed initial) rows initial := by
  let boundary := n1PinnedBoundary template trace hfixed initial
  have hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate :=
    pinnedBoundary_rows (by decide : 1 ≤ 8) template trace
      (n1_trace_bounds trace hfixed) initial
  exact n1_local_schedule boundary rows initial trace hfixed hrows
    (by simpa [boundary, n1PinnedBoundary, pinnedBoundary] using hbaseline)
    (by intro call slot; rfl)
    (pinnedBoundary_first (by decide : 1 ≤ 8) (by decide : 0 < 1)
      template trace (n1_trace_bounds trace hfixed) initial)
    (by intro call; rfl)
    hpackedInitial hpackedFinal hzero hunit hinverse

/-- N8 analogue of the source-shaped trace-owned boundary certificate. -/
theorem n8_pinned_local_schedule (template : Boundary 8)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (initial : State)
    (rows : ∀ call, Fin ((n8PinnedBoundary template trace hfixed initial).rounds call) →
      NativeRow)
    (hbaseline : template.baselineYields = [])
    (hpackedInitial : ValueAt (n8PinnedBoundary template trace hfixed initial)
      22 (packState initial))
    (hpackedFinal : ValueAt (n8PinnedBoundary template trace hfixed initial)
      (22 + 10 * 8)
      (packState ((n8PinnedBoundary template trace hfixed initial).finish
        ⟨8 - 1, by omega⟩)))
    (hzero : ValueAt (n8PinnedBoundary template trace hfixed initial)
      0 (base 0))
    (hunit : ∀ lane, ValueAt (n8PinnedBoundary template trace hfixed initial)
      (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt (n8PinnedBoundary template trace hfixed initial)
        (inverseAddress 8 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 8 ≤ 8) (by decide : 0 < 8)
      (n8PinnedBoundary template trace hfixed initial) rows initial := by
  let boundary := n8PinnedBoundary template trace hfixed initial
  have hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate :=
    pinnedBoundary_rows (by decide : 8 ≤ 8) template trace
      (n8_trace_bounds trace hfixed) initial
  exact n8_local_schedule boundary rows initial trace hfixed hrows
    (by simpa [boundary, n8PinnedBoundary, pinnedBoundary] using hbaseline)
    (by intro call slot; rfl)
    (pinnedBoundary_first (by decide : 8 ≤ 8) (by decide : 0 < 8)
      template trace (n8_trace_bounds trace hfixed) initial)
    (by intro call; rfl)
    hpackedInitial hpackedFinal hzero hunit hinverse

end S31.Gadgets.Air.SourceMixedDecodedBoundary
