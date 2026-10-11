import S31.Gadgets.Functional.SSADeadRowGateJoin
import S31.Gadgets.Functional.GeneratedDirectGateMixedReturn

/-!
The generated early-return source has three physical source instructions but
returns its first result. Its final row has zero source uses. This instance
checks the finite source-use dependency condition and applies the selective
Gate theorem to that actual source/normalized-byte pair and its exported
fixed-cell plans. Physical rows, exact Gate balance, public pin events, and
producer uniqueness remain explicit verifier-refinement premises.
-/

namespace S31.Functional.SSADeadRowMixedReturn

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSADeadRowGateJoin
open S31.Functional.GeneratedDirectGateMixedReturn

theorem generated_used_dependencies : usedDependencies certificate :=
  usedDependencies_of_sourceUses certificate

theorem generated_selected_use :
    0 < sourceUses certificate certificate.output :=
  sourceUses_selected_pos certificate

theorem generated_dead_final_row : sourceUses certificate 3 = 0 :=
  unused_source_row_detected

theorem early_return_public_io_sound (input claimed : Lanes)
    (rows : List Row) (externalUses externalYields : List Event)
    (hsourceRows : sourceGateBytecodeRowsAllowDead certificate
      observedColumnCells rows)
    (hinputRows : physicalGateBytecodeRows observedInputCells rows)
    (houtputRows : physicalGateBytecodeRows observedOutputCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈ allYields rows externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈ allYields rows externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈ allYields rows externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈ allYields rows externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate observedAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields rows externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (S31.Field.toZMod (input i))) ∈ externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (S31.Field.toZMod (claimed i))) ∈ externalYields) :
    denotation sourceBytes input = some claimed := by
  exact bytecode_exact_gate_public_io_allow_dead_sound
    sourceBytes normalizedBytes certificate observedAddRows
    observedColumnCells observedInputCells observedOutputCells
    input claimed rows externalUses externalYields
    normalized_bytes_check observed_source_columns_match hsourceRows
    observed_input_cells_match hinputRows
    observed_output_cells_match houtputRows hbalance hunique
    hzero hbasis1 hbasis2 hbasis3 hmaskBasis hinverseBasis
    (fun i => List.mem_append_right _ (hpublicInputPins i))
    (fun i => List.mem_append_right _ (hpublicOutputPins i))

end S31.Functional.SSADeadRowMixedReturn
