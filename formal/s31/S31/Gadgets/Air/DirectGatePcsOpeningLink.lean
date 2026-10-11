import S31.Gadgets.Air.GeneratedDirectGateCircleFactor

/-!
The resident Gate verifier reads the same `sampled_values` tree for its OODS
equation and for the later PCS quotient/FRI check. The polynomial and point
objects below make the evaluation claim precise. A successful native PCS check
implying that claim is an external premise, not a theorem here.
-/

namespace S31.Gadgets.Air.DirectGatePcsOpeningLink

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateCompositionOpening
open S31.Gadgets.Air.DirectGateCircleFactor
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Gadgets.Air.GeneratedDirectGateCircleFactor
open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

/-- A finite bivariate polynomial restricted to the circle. Native Stwo uses
its own circle basis; refinement of that basis and native degree bounds are
separate PCS premises. This concrete representation excludes arbitrary
point-to-value functions. -/
structure Monomial where
  xPower : Nat
  yPower : Nat
  coefficient : QM

structure CirclePolynomial where
  terms : List Monomial

def evalPolynomial (poly : CirclePolynomial) (point : Point) : QM :=
  poly.terms.foldl (fun acc term =>
    acc + term.coefficient * point.x ^ term.xPower * point.y ^ term.yPower) 0

/-- Four commitment trees, in native preprocessed/main/interaction/composition
order. The byte strings represent roots; Lean deliberately leaves hashing and
Merkle authentication to the assumed PCS relation. -/
abbrev Digest := Fin 32 → UInt8

structure TreeRoots where
  fixed : Digest
  main : Digest
  interaction : Digest
  composition : Digest

structure PolynomialInventory where
  fixed : Fin 8 → CirclePolynomial
  main : Fin 12 → CirclePolynomial
  interaction : Fin 8 → CirclePolynomial
  composition : Fin 8 → CirclePolynomial

/-- Native `CanonicCoset.new(max_log_degree_bound).step()`: the M31 circle
generator raised to `2^(31 - max_log_degree_bound)`, embedded in QM31. The
accepted theorem requires the native range `1 ≤ bound ≤ 31`. -/
def circleGenerator : Point := ⟨2, 1268011823⟩

def traceStep (maxLogDegreeBound : Nat) : Point :=
  repeatedDouble (31 - maxLogDegreeBound) circleGenerator

def circleNeg (point : Point) : Point := ⟨point.x, -point.y⟩

def circleAdd (left right : Point) : Point :=
  ⟨left.x * right.x - left.y * right.y,
    left.x * right.y + left.y * right.x⟩

/-- The native `point.add(step.mulSigned(-1))` mask point. -/
def previousPoint (seed : QM) (maxLogDegreeBound : Nat) : Point :=
  circleAdd (fromSeed seed) (circleNeg (traceStep maxLogDegreeBound))

/-- A nonconstant opening distinguishes the two mask points. This guards
against silently treating a previous-row interaction value as a second
opening at the current OODS point. -/
def coordinateX : CirclePolynomial := ⟨[⟨1, 0, 1⟩]⟩

theorem coordinateX_eval (point : Point) :
    evalPolynomial coordinateX point = point.x := by
  simp [coordinateX, evalPolynomial]

theorem previous_coordinate_differs_at_zero_seed :
    evalPolynomial coordinateX (previousPoint 0 31) ≠
      evalPolynomial coordinateX (fromSeed 0) := by
  simp only [coordinateX_eval, previousPoint, circleAdd, circleNeg,
    traceStep, repeatedDouble, circleGenerator, fromSeed]
  decide

def expectedCells (polys : PolynomialInventory) (seed : QM)
    (maxLogDegreeBound : Nat) : Cells where
  localFixed i := evalPolynomial (polys.fixed (fixedReadOrder i)) (fromSeed seed)
  main i := evalPolynomial (polys.main i) (fromSeed seed)
  interaction i := evalPolynomial (polys.interaction i) (fromSeed seed)
  previousInteraction i := if i.val < 4 then 0 else
    evalPolynomial (polys.interaction i) (previousPoint seed maxLogDegreeBound)

def expectedCompositionTree (polys : PolynomialInventory) (seed : QM) :
    List (List QM) :=
  [[evalPolynomial (polys.composition 0) (fromSeed seed)],
   [evalPolynomial (polys.composition 1) (fromSeed seed)],
   [evalPolynomial (polys.composition 2) (fromSeed seed)],
   [evalPolynomial (polys.composition 3) (fromSeed seed)],
   [evalPolynomial (polys.composition 4) (fromSeed seed)],
   [evalPolynomial (polys.composition 5) (fromSeed seed)],
   [evalPolynomial (polys.composition 6) (fromSeed seed)],
   [evalPolynomial (polys.composition 7) (fromSeed seed)]]

/-- An external PCS premise. `commitmentBinds roots polys` must mean that
these exact four native roots bind these polynomial objects, subject to the
native degree limits. The other fields require evaluation at the exact Gate
mask points derived from the transcript seed and maximum degree bound. A
successful verifier flag does not construct this structure in Lean. -/
structure PcsOpeningAssumption (samples : Samples)
    (compositionTree : List (List QM))
    (roots : TreeRoots) (polys : PolynomialInventory)
    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)
    (seed : QM) (maxLogDegreeBound : Nat) : Prop where
  bound : commitmentBinds roots polys
  fixed : ∀ i, samples.fixed i =
    [evalPolynomial (polys.fixed i) (fromSeed seed)]
  main : ∀ i, samples.main i =
    [evalPolynomial (polys.main i) (fromSeed seed)]
  interactionFirst : ∀ i, i.val < 4 →
    samples.interaction i =
      [evalPolynomial (polys.interaction i) (fromSeed seed)]
  interactionLast : ∀ i, 4 ≤ i.val →
    samples.interaction i =
      [evalPolynomial (polys.interaction i) (previousPoint seed maxLogDegreeBound),
       evalPolynomial (polys.interaction i) (fromSeed seed)]
  composition : compositionTree = expectedCompositionTree polys seed

theorem authenticated_shape (samples : Samples)
    (compositionTree : List (List QM)) (roots : TreeRoots)
    (polys : PolynomialInventory)
    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)
    (seed : QM) (maxLogDegreeBound : Nat)
    (auth : PcsOpeningAssumption samples compositionTree roots polys
      commitmentBinds seed maxLogDegreeBound) :
    DirectGateOodsOpenings.Shape samples := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [auth.fixed i]; rfl
  · intro i; rw [auth.main i]; rfl
  · intro i hi; rw [auth.interactionFirst i hi]; rfl
  · intro i hi; rw [auth.interactionLast i hi]; rfl

theorem authenticated_cells (samples : Samples)
    (compositionTree : List (List QM)) (roots : TreeRoots)
    (polys : PolynomialInventory)
    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)
    (seed : QM) (maxLogDegreeBound : Nat)
    (auth : PcsOpeningAssumption samples compositionTree roots polys
      commitmentBinds seed maxLogDegreeBound) :
    cellsOfSamples samples = expectedCells polys seed maxLogDegreeBound := by
  have hf : (cellsOfSamples samples).localFixed =
      (expectedCells polys seed maxLogDegreeBound).localFixed := by
    funext i
    simp [cellsOfSamples, expectedCells, fixedRead, auth.fixed]
  have hm : (cellsOfSamples samples).main =
      (expectedCells polys seed maxLogDegreeBound).main := by
    funext i
    simp [cellsOfSamples, expectedCells, mainRead, auth.main]
  have hi : (cellsOfSamples samples).interaction =
      (expectedCells polys seed maxLogDegreeBound).interaction := by
    funext i
    fin_cases i <;>
      simp [cellsOfSamples, expectedCells, interactionRead,
        interactionMaskRead, interactionOffsets, offsetIndex,
        auth.interactionFirst, auth.interactionLast]
  have hp : (cellsOfSamples samples).previousInteraction =
      (expectedCells polys seed maxLogDegreeBound).previousInteraction := by
    funext i
    fin_cases i <;>
      simp [cellsOfSamples, expectedCells, interactionRead,
        interactionMaskRead, interactionOffsets, offsetIndex,
        auth.interactionFirst, auth.interactionLast]
  cases h : cellsOfSamples samples with
  | mk fixed main interaction previousInteraction =>
    cases h' : expectedCells polys seed maxLogDegreeBound with
    | mk fixed' main' interaction' previousInteraction' =>
      simp only [h, h'] at hf hm hi hp
      cases hf
      cases hm
      cases hi
      cases hp
      rfl

theorem authenticated_composition_tree (samples : Samples)
    (compositionTree : List (List QM)) (roots : TreeRoots)
    (polys : PolynomialInventory)
    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)
    (seed : QM) (maxLogDegreeBound : Nat)
    (auth : PcsOpeningAssumption samples compositionTree roots polys
      commitmentBinds seed maxLogDegreeBound)
    (factor : QM) :
    extractSplitOne factor compositionTree =
      extractSplitOne factor (expectedCompositionTree polys seed) := by
  rw [auth.composition]

/-- Given one authenticated opening inventory and the native OODS equality,
the accepted Gate claim is the eleven-root pure polynomial identity *at those
authenticated evaluations*. This is conditional on a sound PCS opening
assumption and the checked seed/conversion and zeroifier premises. -/
theorem accepted_of_authenticated_openings (samples : Samples)
    (compositionTree : List (List QM)) (roots : TreeRoots)
    (polys : PolynomialInventory)
    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)
    (maxLogDegreeBound : Nat)
    (seed z alpha claimed coefficient zeroifier : QM)
    (compositionLogSize : Nat) (hsize : 2 ≤ compositionLogSize)
    (_hbound : 1 ≤ maxLogDegreeBound ∧ maxLogDegreeBound ≤ 31)
    (auth : PcsOpeningAssumption samples compositionTree roots polys
      commitmentBinds seed maxLogDegreeBound)
    (seedAccepted : checkedFromSeed seed = some (fromSeed seed))
    (hzero : zeroifier ≠ 0)
    (accepted : extractSplitOne
      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x
      compositionTree = some (quotientFold coefficient zeroifier⁻¹
        (transcriptRoots (cellsOfSamples samples) z alpha claimed))) :
    extractSplitOne (factor seed compositionLogSize)
      (expectedCompositionTree polys seed) =
      some (S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots (expectedCells polys seed maxLogDegreeBound)
          alpha z (claimed / 512)) /
        zeroifier) := by
  have shape := authenticated_shape samples compositionTree roots polys
    commitmentBinds seed maxLogDegreeBound auth
  have claim := accepted_seeded_tree_eq_pure samples shape compositionTree
    seed z alpha claimed coefficient zeroifier compositionLogSize hsize
    seedAccepted hzero accepted
  rw [auth.composition, authenticated_cells samples compositionTree roots polys
    commitmentBinds seed maxLogDegreeBound auth]
    at claim
  exact claim

end S31.Gadgets.Air.DirectGatePcsOpeningLink
