import S31.Gadgets.Functional.Correspondence.AcceptedSourcePhysicalTrace
import S31.Gadgets.Functional.SSAPublicInputBinding
import S31.Gadgets.Functional.SSAInstalledBytecodePublicOutput
import S31.Gadgets.Air.PackRows

/-!
Constructed values for the direct-Gate public input/output boundary around
an honest source SSA execution. These are mathematical gate values, not a
native full-roster or Gate-balanced proof witness.
-/

namespace S31.Functional.Correspondence.HonestPublicBoundaryWire

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.Correspondence.HonestSourceCellWitness
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.SSAAirRows

/-- Native addresses 0–21: constants, public scalar slots, raw input
scalars, three basis values, and five input-pack intermediates. -/
def lowerValue (input output : Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) : Nat → Quad
  | 0 => base 0
  | 1 => unit ⟨0, by decide⟩
  | 2 => unit ⟨2, by decide⟩
  | 3 => base (Field.toZMod (input ⟨0, by decide⟩))
  | 4 => base (Field.toZMod (input ⟨1, by decide⟩))
  | 5 => base (Field.toZMod (input ⟨2, by decide⟩))
  | 6 => base (Field.toZMod (input ⟨3, by decide⟩))
  | 7 => base (Field.toZMod (output ⟨0, by decide⟩))
  | 8 => base (Field.toZMod (output ⟨1, by decide⟩))
  | 9 => base (Field.toZMod (output ⟨2, by decide⟩))
  | 10 => base (Field.toZMod (output ⟨3, by decide⟩))
  | 11 => base (Field.toZMod (input ⟨0, by decide⟩))
  | 12 => base (Field.toZMod (input ⟨1, by decide⟩))
  | 13 => base (Field.toZMod (input ⟨2, by decide⟩))
  | 14 => base (Field.toZMod (input ⟨3, by decide⟩))
  | 15 => unit ⟨1, by decide⟩
  | 16 => unit ⟨3, by decide⟩
  | 17 => term1
  | 18 => sum1
  | 19 => term2
  | 20 => sum2
  | 21 => term3
  | _ => base 0

/-- Ten allocated values immediately after the final source wire:
four masked lanes, three inverse constants, and three restored scalar
results. Their offsets match `expectedOutputCells`. -/
def upperValue (output : Lanes) : Nat → Quad
  | 0 => pointwise (packM31 output) (unit ⟨0, by decide⟩)
  | 1 => pointwise (packM31 output) (unit ⟨1, by decide⟩)
  | 2 => unitInverse ⟨1, by decide⟩
  | 3 => base (Field.toZMod (output ⟨1, by decide⟩))
  | 4 => pointwise (packM31 output) (unit ⟨2, by decide⟩)
  | 5 => unitInverse ⟨2, by decide⟩
  | 6 => base (Field.toZMod (output ⟨2, by decide⟩))
  | 7 => pointwise (packM31 output) (unit ⟨3, by decide⟩)
  | 8 => unitInverse ⟨3, by decide⟩
  | 9 => base (Field.toZMod (output ⟨3, by decide⟩))
  | _ => base 0

/-- Source wires occupy `[22, 22 + final.length)`. This interval is
disjoint from the public input/basis prefix and from the ten public output
wire slots. -/
def extendedWire (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (a : Nat) : Quad :=
  if a < 22 then lowerValue input output term1 term2 term3 sum1 sum2 a
  else if a < 22 + final.length then wireOfFinal final a
  else upperValue output (a - (22 + final.length))

theorem extendedWire_lower (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (a : Nat) (ha : a < 22) :
    extendedWire input output final term1 term2 term3 sum1 sum2 a =
      lowerValue input output term1 term2 term3 sum1 sum2 a := by
  simp [extendedWire, ha]

theorem extendedWire_source (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (id : Nat)
    (hid : id < final.length) :
    extendedWire input output final term1 term2 term3 sum1 sum2 (address id) =
      wireOfFinal final (address id) := by
  have hlo : ¬ address id < 22 := by simp [address]
  have hhi : address id < 22 + final.length := by simp [address, hid]
  simp [extendedWire, hlo, hhi]

theorem extendedWire_upper (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (offset : Nat) :
    extendedWire input output final term1 term2 term3 sum1 sum2
      (22 + final.length + offset) = upperValue output offset := by
  have hlo : ¬ 22 + final.length + offset < 22 := by omega
  have hhi : ¬ 22 + final.length + offset < 22 + final.length := by omega
  simp [extendedWire, hlo, hhi]

theorem accepted_trace_length {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    final.length = initial.length + instructions.length := by
  induction h with
  | done values => simp
  | @next values final instruction rest output _ _ ih =>
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih

/-- The public scalar input, its four copies, and all six pack operations
have an honest address-coherent assignment. The source wire at address 22
is the initial SSA value in `final`. -/
theorem honest_input_boundary (certificate : Certificate) (totalAddRows : Nat)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hfirst : final[0]? = some input)
    (hpack : S31.Gadgets.Air.PackRows.acceptsPack input
      term1 term2 term3 sum1 sum2 (packM31 input)) :
    InputBoundary certificate totalAddRows
      (extendedWire input output final term1 term2 term3 sum1 sum2) input := by
  let wire := extendedWire input output final term1 term2 term3 sum1 sum2
  have hzero : wire 0 = base 0 := by
    simp [wire, extendedWire_lower, lowerValue]
  have hfirstBound : 0 < final.length :=
    (List.getElem?_eq_some_iff.mp hfirst).1
  have hwire22 : wire 22 = packM31 input := by
    have hsource := extendedWire_source input output final
      term1 term2 term3 sum1 sum2 0 hfirstBound
    simpa [wire, wireOfFinal, address, hfirst] using hsource
  rcases hpack with ⟨hm1, hm2, hm3, ha1, ha2, ha3⟩
  refine ⟨hzero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [expectedInputCopyCell, extendedWire_lower,
        lowerValue, accepts_encoded, evaluate,
        S31.Gadgets.Packed.add, base]
  · intro i
    fin_cases i <;>
      simp [extendedWire_lower, lowerValue]
  · simp [extendedWire_lower, lowerValue]
  · simp [extendedWire_lower, lowerValue]
  · simp [extendedWire_lower, lowerValue]
  · intro i
    fin_cases i
    · simpa [wire, expectedPackMulCell, maskBasisAddress,
        extendedWire_lower, lowerValue] using hm1
    · simpa [wire, expectedPackMulCell, maskBasisAddress,
        extendedWire_lower, lowerValue] using hm2
    · simpa [wire, expectedPackMulCell, maskBasisAddress,
        extendedWire_lower, lowerValue] using hm3
  · intro i
    fin_cases i
    · simpa [wire, expectedPackAddCell, extendedWire_lower,
        lowerValue] using ha1
    · simpa [wire, expectedPackAddCell, extendedWire_lower,
        lowerValue] using ha2
    · simpa [wire, expectedPackAddCell, extendedWire_lower,
        lowerValue, ← hwire22] using ha3

/-- In the final SSA value list, the source-selected packed output lies in
the source interval of the global public/source wire assignment. -/
theorem extendedWire_selected (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hselected : final[certificate.output]? = some output) :
    extendedWire input output final term1 term2 term3 sum1 sum2
      (address certificate.output) = packM31 output := by
  have hid : certificate.output < final.length :=
    (List.getElem?_eq_some_iff.mp hselected).1
  rw [extendedWire_source input output final
    term1 term2 term3 sum1 sum2 certificate.output hid]
  simp [wireOfFinal, address, hselected]

/-- The public output address schedule names exactly the ten values after
the last source wire. -/
theorem output_mask_values (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hlen : final.length = 1 + certificate.instructions.length) :
    ∀ i : Fin 4,
      extendedWire input output final term1 term2 term3 sum1 sum2
        (maskAddress certificate.instructions.length i.val) =
      pointwise (packM31 output) (unit i) := by
  intro i
  fin_cases i
  · have ha : maskAddress certificate.instructions.length 0 =
        22 + final.length + 0 := by simp [maskAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 0
  · have ha : maskAddress certificate.instructions.length 1 =
        22 + final.length + 1 := by simp [maskAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 1
  · have ha : maskAddress certificate.instructions.length 2 =
        22 + final.length + 4 := by simp [maskAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 4
  · have ha : maskAddress certificate.instructions.length 3 =
        22 + final.length + 7 := by simp [maskAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 7

theorem output_result_values (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hlen : final.length = 1 + certificate.instructions.length) :
    ∀ i : Fin 4,
      extendedWire input output final term1 term2 term3 sum1 sum2
        (resultAddress certificate.instructions.length i.val) =
      base (Field.toZMod (output i)) := by
  intro i
  fin_cases i
  · have ha : resultAddress certificate.instructions.length 0 =
        22 + final.length + 0 := by simp [resultAddress, hlen]; omega
    simpa [ha, upperValue, packM31, pointwise, unit, base] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 0
  · have ha : resultAddress certificate.instructions.length 1 =
        22 + final.length + 3 := by simp [resultAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 3
  · have ha : resultAddress certificate.instructions.length 2 =
        22 + final.length + 6 := by simp [resultAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 6
  · have ha : resultAddress certificate.instructions.length 3 =
        22 + final.length + 9 := by simp [resultAddress, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 9

theorem output_inverse_values (certificate : Certificate)
    (totalAddRows : Nat) (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hlen : final.length = 1 + certificate.instructions.length) :
    ∀ i : Fin 3,
      extendedWire input output final term1 term2 term3 sum1 sum2
        ((expectedInverseCell certificate totalAddRows i.val).in1) =
      unitInverse ⟨i.val + 1, by omega⟩ := by
  intro i
  fin_cases i
  · have ha : (expectedInverseCell certificate totalAddRows 0).in1 =
        22 + final.length + 2 := by simp [expectedInverseCell, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 2
  · have ha : (expectedInverseCell certificate totalAddRows 1).in1 =
        22 + final.length + 5 := by simp [expectedInverseCell, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 5
  · have ha : (expectedInverseCell certificate totalAddRows 2).in1 =
        22 + final.length + 8 := by simp [expectedInverseCell, hlen]; omega
    simpa only [ha, upperValue] using
      extendedWire_upper input output final term1 term2 term3 sum1 sum2 8

/-- Once the checked source has selected `output`, the same global wire
assignment satisfies all eleven modeled output-path cells and four public
output pins. No Gate balance or full native fixed roster is claimed. -/
theorem honest_output_boundary (certificate : Certificate)
    (totalAddRows : Nat) (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (hlen : final.length = 1 + certificate.instructions.length)
    (hselected : final[certificate.output]? = some output) :
    OutputBoundary certificate totalAddRows
      (extendedWire input output final term1 term2 term3 sum1 sum2)
      output := by
  let wire := extendedWire input output final term1 term2 term3 sum1 sum2
  have hzero : wire 0 = base 0 := by
    simp [wire, extendedWire_lower, lowerValue]
  have hselectedWire : wire (address certificate.output) =
      packM31 output := by
    exact extendedWire_selected certificate input output final
      term1 term2 term3 sum1 sum2 hselected
  have hmask := output_mask_values certificate input output final
    term1 term2 term3 sum1 sum2 hlen
  have hresult := output_result_values certificate input output final
    term1 term2 term3 sum1 sum2 hlen
  have hinverse := output_inverse_values certificate totalAddRows input output
    final term1 term2 term3 sum1 sum2 hlen
  have hbasis : ∀ i : Fin 4, wire (maskBasisAddress i.val) = unit i := by
    intro i
    fin_cases i <;>
      simp [wire, maskBasisAddress, extendedWire_lower, lowerValue, unit]
  have hpin : ∀ i : Fin 4,
      wire (7 + i.val) = base (Field.toZMod (output i)) := by
    intro i
    fin_cases i <;>
      simp [wire, extendedWire_lower, lowerValue]
  refine ⟨hzero, hbasis, hinverse, ?_, ?_, ?_, hpin⟩
  · intro i
    change accepts (encode .pointwiseMul)
      (wire (address certificate.output))
      (wire (maskBasisAddress i.val))
      (wire (maskAddress certificate.instructions.length i.val))
    change accepts (encode .pointwiseMul)
      (wire (address certificate.output))
      (wire (maskBasisAddress i.val))
      (extendedWire input output final term1 term2 term3 sum1 sum2
        (maskAddress certificate.instructions.length i.val))
    rw [hselectedWire, hbasis i, hmask i]
    exact honest_row _ _ _
  · intro i
    let j : Fin 4 := ⟨i.val + 1, by omega⟩
    change accepts (encode .mul)
      (wire (maskAddress certificate.instructions.length j.val))
      (wire ((expectedInverseCell certificate totalAddRows i.val).in1))
      (wire (resultAddress certificate.instructions.length j.val))
    change accepts (encode .mul)
      (extendedWire input output final term1 term2 term3 sum1 sum2
        (maskAddress certificate.instructions.length j.val))
      (extendedWire input output final term1 term2 term3 sum1 sum2
        ((expectedInverseCell certificate totalAddRows i.val).in1))
      (extendedWire input output final term1 term2 term3 sum1 sum2
        (resultAddress certificate.instructions.length j.val))
    rw [hmask j, hinverse i, hresult j]
    apply (accepts_encoded .mul _ _ _).mpr
    simpa [j, evaluate, coord_packM31] using
      (unpack_coordinate (packM31 output) j).symm
  · intro i
    change accepts (encode .add)
      (wire (resultAddress certificate.instructions.length i.val))
      (wire 0) (wire (7 + i.val))
    change accepts (encode .add)
      (extendedWire input output final term1 term2 term3 sum1 sum2
        (resultAddress certificate.instructions.length i.val))
      (wire 0) (wire (7 + i.val))
    rw [hresult i, hzero, hpin i]
    apply (accepts_encoded .add _ _ _).mpr
    simp [evaluate, S31.Gadgets.Packed.add, base]

private theorem accepted_trace_extends {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    ∃ suffix, final = initial ++ suffix := by
  induction h with
  | done values => exact ⟨[], by simp⟩
  | @next values final instruction rest output _ _ ih =>
      obtain ⟨suffix, hfinal⟩ := ih
      exact ⟨output :: suffix, by simpa [List.append_assoc] using hfinal⟩

private theorem accepted_trace_indices {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    ∀ instruction ∈ instructions,
      instruction.lhs < final.length ∧
      instruction.rhs < final.length ∧
      instruction.id < final.length := by
  induction h with
  | done => simp
  | @next values final instruction rest output hrow hrest ih =>
      have hlen : (values ++ [output]).length ≤ final.length := by
        have hsize := accepted_trace_length hrest
        omega
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        obtain ⟨_, _, hid, hleft, hright, _⟩ := hrow
        have hl := (List.getElem?_eq_some_iff.mp hleft).1
        have hr := (List.getElem?_eq_some_iff.mp hright).1
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      · exact ih item htail

/-- The honest SSA execution's source arithmetic remains valid in the
larger wire assignment used by the public input and output boundary. -/
theorem extended_source_polynomials {final : List Lanes}
    (certificate : Certificate) (input output : Lanes)
    (term1 term2 term3 sum1 sum2 : Quad)
    (htrace : AcceptsTrace [input] certificate.instructions final) :
    nativePolynomialRows certificate
      (extendedWire input output final term1 term2 term3 sum1 sum2) := by
  intro instruction hmember
  obtain ⟨hl, hr, ho⟩ := accepted_trace_indices htrace instruction hmember
  simpa only [extendedWire_source input output final
      term1 term2 term3 sum1 sum2 instruction.lhs hl,
    extendedWire_source input output final
      term1 term2 term3 sum1 sum2 instruction.rhs hr,
    extendedWire_source input output final
      term1 term2 term3 sum1 sum2 instruction.id ho] using
    honest_trace_source_polynomials htrace instruction hmember

/-- Construct one coherent modeled source/public wire assignment from a
successful positional SSA execution. This lemma is source-parser independent:
the byte grammar supplies `hexecute`, while all public and source cells are
determined by the certificate. It also supports an early selected output with
later eager instructions, since `final[certificate.output]` is read directly. -/
theorem executed_public_boundary_exists
    (certificate : Certificate) (input output : Lanes)
    (hexecute : executeNormalized certificate input = some output) :
    ∃ wire : Nat → Quad,
      nativePolynomialRows certificate wire ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      OutputBoundary certificate (compiledAddRows certificate) wire output ∧
      wire (address certificate.output) = packM31 output ∧
      wire 1 = unit ⟨0, by decide⟩ := by
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselected : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have htrace : AcceptsTrace [input] certificate.instructions final :=
        executing_trace_has_air_rows certificate.instructions [input] final
          hrun
      obtain ⟨suffix, hprefix⟩ := accepted_trace_extends htrace
      have hfirst : final[0]? = some input := by
        simp [hprefix]
      have hlen : final.length = 1 + certificate.instructions.length := by
        simpa using accepted_trace_length htrace
      obtain ⟨term1, term2, term3, sum1, sum2, hpack⟩ :=
        S31.Gadgets.Air.PackRows.acceptsPack_honest input
      let wire := extendedWire input output final
        term1 term2 term3 sum1 sum2
      exact ⟨wire,
        extended_source_polynomials certificate input output
          term1 term2 term3 sum1 sum2 htrace,
        honest_input_boundary certificate (compiledAddRows certificate)
          input output final term1 term2 term3 sum1 sum2 hfirst hpack,
        honest_output_boundary certificate (compiledAddRows certificate)
          input output final term1 term2 term3 sum1 sum2 hlen hselected,
        extendedWire_selected certificate input output final
          term1 term2 term3 sum1 sum2 hselected,
        by simp [wire, extendedWire_lower, lowerValue]⟩

/-- Every exact byte-admitted bounded direct-Gate source and every public
input have one coherent honest assignment for all source arithmetic rows,
all six input-pack rows, all four input copies, all eleven output rows, and
the public scalar pins. This is a constructive modeled circuit witness.

The native constant derivation/padding rows, exact Gate balance, committed
column authentication, and proof-system verifier remain separate gaps. -/
theorem checked_direct_public_boundary_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSATextBytes.denotation sourceBytes input = some output ∧
      nativePolynomialRows certificate wire ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      OutputBoundary certificate (compiledAddRows certificate) wire output ∧
      wire (address certificate.output) = packM31 output ∧
      wire 1 = unit ⟨0, by decide⟩ := by
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hcheck
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hcheck
    | some parsed => exact ⟨parsed, rfl⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : SSATextBytes.denotation sourceBytes input =
      some output := by
    simp [SSATextBytes.denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input
      hcheck]
    exact hdenotation
  obtain ⟨wire, hsource, hinput, houtput, hselected, hunit⟩ :=
    executed_public_boundary_exists certificate input output hexecute
  exact ⟨wire, output, hdenotation, hsource, hinput, houtput, hselected,
    hunit⟩

end S31.Functional.Correspondence.HonestPublicBoundaryWire
