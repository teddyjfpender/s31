import S31.Gadgets.Air.SourceMixedEventAlignment

/-!
The chip event projection fixes more than a lookup multiset: its ordered row
lists identify each of the sixteen committed chip input and output tuples
with the source-shaped native rows. Tuple injectivity then transports the
chip AIR arithmetic equation to those rows. This remains conditional on the
projection and fixed chip constant; it does not extract rows from a succinct
proof.
-/

namespace S31.Gadgets.Air.SourceMixedChipRowProjection

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace
open S31.Gadgets.Air.SourceMixedEventAlignment

/-- Equal chip event lists force the native row count to equal the fixed
sixteen-row chip, and carry its arithmetic equation to every native row. -/
private theorem projected_chip_step {N R : Nat} {alpha z : GateSecure}
    (call : Fin N) (chip : ChipRows 8 (by decide) alpha z)
    (rows : Fin R → NativeRow) (constant : F)
    (hinputs : chip.inputEvents =
      List.ofFn (fun row : Fin R =>
        nativeTuple call (rows row).step (rows row).input))
    (houtputs : chip.outputEvents =
      List.ofFn (fun row : Fin R =>
        nativeTuple call ((rows row).step + 1) (rows row).output))
    (hconstant : chip.constant = constant) :
    ∀ row, (rows row).output =
      fun lane => (rows row).input lane ^ 2 + constant := by
  have hR : R = 16 := by
    have hlength := congrArg List.length hinputs
    simpa [ChipRows.inputEvents] using hlength.symm
  subst R
  have hinList :
      List.ofFn (sourceChipInputTuple chip.call chip.step chip.input) =
        List.ofFn (fun row : Fin 16 =>
          nativeTuple call (rows row).step (rows row).input) := by
    simpa only [ChipRows.inputEvents] using hinputs
  have houtList :
      List.ofFn (sourceChipOutputTuple chip.call chip.step chip.output) =
        List.ofFn (fun row : Fin 16 =>
          nativeTuple call ((rows row).step + 1) (rows row).output) := by
    simpa only [ChipRows.outputEvents] using houtputs
  have hinTuple := List.ofFn_injective hinList
  have houtTuple := List.ofFn_injective houtList
  intro row
  have hin : chip.input row = (rows row).input := by
    have htuple := congrFun hinTuple row
    exact (chipTuple7_injective _ _ _ _ _ _
      (by simpa only [sourceChipInputTuple, nativeTuple] using htuple)).2.2
  have hout : chip.output row = (rows row).output := by
    have htuple := congrFun houtTuple row
    exact (chipTuple7_injective _ _ _ _ _ _
      (by simpa only [sourceChipOutputTuple, nativeTuple] using htuple)).2.2
  funext lane
  calc
    (rows row).output lane = chip.output row lane := congrFun hout.symm lane
    _ = chip.input row lane ^ 2 + chip.constant := chip.arithmetic_sound row lane
    _ = (rows row).input lane ^ 2 + constant := by rw [hin, hconstant]

/-- Source-shaped chip input and output events plus the verifier-fixed call
constant discharge the public-path transition equation. -/
theorem EventProjection.chip_step {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {gate : GateRows alpha z}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → BridgeRows alpha z}
    {words : List Quad}
    (projection : EventProjection boundary rows alpha z gate chip bridge words)
    (hconstant : ∀ call, (chip call).constant = boundary.constants call) :
    ∀ call row,
      (rows call row).output = boundary.step call (rows call row).input := by
  intro call row
  have h := projected_chip_step call (chip call) (rows call)
    (boundary.constants call) (projection.chipInputs call)
    (projection.chipOutputs call) (hconstant call) row
  simpa only [Boundary.step] using h

end S31.Gadgets.Air.SourceMixedChipRowProjection
