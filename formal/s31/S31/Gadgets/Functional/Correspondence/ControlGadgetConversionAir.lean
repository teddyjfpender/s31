import S31.Gadgets.Functional.Correspondence.ControlGadgetPublicPins

/-!
The installed `m_31_to_u_32` component has four trace columns: input, low,
high, and inverse-or-one. Its two AIR residuals below, three `RangeCheck_16`
uses, and Gate input/output tuples are kept separate. The range and Gate
membership premises describe authenticated lookup closure; the theorem does
not derive that closure from a PCS/FRI proof.
-/

namespace S31.Functional.Correspondence.ControlGadgetConversionAir

open S31.Gadgets.Packed
open S31.Functional.Correspondence.ControlGadgetAir
open S31.Functional.Correspondence.ControlGadgetPublicPins

structure ConversionCell where
  input : F
  low : F
  high : F
  inverseOrOne : F

/-- The two arithmetic residuals, in the installed evaluator's order. -/
def residuals (c : ConversionCell) : List F :=
  [(c.input * c.inverseOrOne - 1) * c.low,
    c.input - (c.low + c.high * 65536)]

/-- The exact three table uses, in the installed evaluator's order. -/
def rangeUses (c : ConversionCell) : List F :=
  [c.low, c.high, 32767 - c.high]

def range16 (x : F) : Prop := x.val ∈ Finset.range 65536

theorem wraparound_alias_rejected (inverseOrOne : F) :
    ((0 : F) * inverseOrOne - 1) * (65535 : F) ≠ 0 := by
  have hn : (65535 : F) ≠ 0 := by
    intro h
    have heq := (S31.Field.bounded_equation 65535 0 (by omega) (by omega)).mp h
    omega
  simpa using (neg_ne_zero.mpr hn)

/-- Local row data plus the consequences of authenticated RangeCheck_16 and
Gate lookup closure. The latter identifies the positive input tuple and
negative output tuple with the physical Gate wire at the fixed row addresses. -/
structure InstalledConversionRows (wire : Wire) (rows : List ConversionGate) where
  cell : ConversionGate → ConversionCell
  air : ∀ row ∈ rows, ∀ r ∈ residuals (cell row), r = 0
  range_lookup : ∀ row ∈ rows, ∀ value ∈ rangeUses (cell row), range16 value
  gate_input : ∀ row ∈ rows, wire row.input = base (cell row).input
  gate_output : ∀ row ∈ rows,
    wire row.out = ⟨(cell row).low, (cell row).high, 0, 0⟩

private theorem high_bounded (high : F)
    (hhigh : range16 high) (hcomplement : range16 (32767 - high)) :
    high.val ≤ 32767 := by
  have hh : high.val < 65536 := by simpa [range16, Finset.mem_range] using hhigh
  have hc : (32767 - high).val < 65536 := by
    simpa [range16, Finset.mem_range] using hcomplement
  have hsum : high.val + (32767 - high).val < 2147483647 := by omega
  have heq : ((high.val + (32767 - high).val : Nat) : F) = 32767 := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    ring
  have hnat : high.val + (32767 - high).val = 32767 :=
    (S31.Field.bounded_equation _ _ hsum (by omega)).mp heq
  omega

/-- The first residual rejects the only bounded false decomposition:
`65535 + 65536 * 32767 = p`, which would otherwise encode input zero. -/
theorem conversion_cell_sound (c : ConversionCell)
    (hair : ∀ r ∈ residuals c, r = 0)
    (hrange : ∀ value ∈ rangeUses c, range16 value) :
    c.low.val + 65536 * c.high.val = c.input.val ∧
      c.low.val < 65536 ∧ c.high.val ≤ 32767 := by
  have hlow : c.low.val < 65536 := by
    simpa [range16, Finset.mem_range] using hrange c.low (by simp [rangeUses])
  have hhigh : c.high.val ≤ 32767 :=
    high_bounded c.high
      (hrange c.high (by simp [rangeUses]))
      (hrange (32767 - c.high) (by simp [rangeUses]))
  have hzero : (c.input * c.inverseOrOne - 1) * c.low = 0 :=
    hair _ (by simp [residuals])
  have hrec : c.input = c.low + c.high * 65536 :=
    sub_eq_zero.mp (hair _ (by simp [residuals]))
  have hcast : c.input = ((c.low.val + 65536 * c.high.val : Nat) : F) := by
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm, ZMod.natCast_zmod_val] using hrec
  have hmod : c.input.val =
      (c.low.val + 65536 * c.high.val) % 2147483647 := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
  have hsum : c.low.val + 65536 * c.high.val ≤ 2147483647 := by omega
  have hless : c.low.val + 65536 * c.high.val < 2147483647 := by
    by_contra hnot
    have heq : c.low.val = 65535 ∧ c.high.val = 32767 := by omega
    have hx : c.input = 0 := by
      apply ZMod.val_injective
      simp [hmod, heq]
    have hl : c.low = 0 := by simpa [hx] using hzero
    have hlval : c.low.val = 0 := by simpa using congrArg ZMod.val hl
    omega
  have hvalue : c.input.val = c.low.val + 65536 * c.high.val := by
    simpa [Nat.mod_eq_of_lt hless] using hmod
  exact ⟨hvalue.symm, hlow, hhigh⟩

theorem conversion_cell_encoded (c : ConversionCell)
    (hair : ∀ r ∈ residuals c, r = 0)
    (hrange : ∀ value ∈ rangeUses c, range16 value) :
    (⟨c.low, c.high, 0, 0⟩ : Quad) = encodeM31ToU32 c.input := by
  obtain ⟨hvalue, hlow, hhigh⟩ := conversion_cell_sound c hair hrange
  have hlow' : c.low.val = c.input.val % 65536 := by omega
  have hhigh' : c.high.val = c.input.val / 65536 := by omega
  apply Quad.ext
  · apply ZMod.val_injective
    change c.low.val = ((c.input.val % 65536 : Nat) : F).val
    rw [ZMod.val_natCast_of_lt (by omega)]
    exact hlow'
  · apply ZMod.val_injective
    change c.high.val = ((c.input.val / 65536 : Nat) : F).val
    rw [ZMod.val_natCast_of_lt (by omega)]
    exact hhigh'
  · rfl
  · rfl

/-- The former conversion-law premise follows from the exact installed AIR
residuals and the three range and two Gate tuple closure facts per row. -/
theorem conversion_semantics_of_installed_rows (wire : Wire)
    (rows : List ConversionGate) (installed : InstalledConversionRows wire rows) :
    ConversionSemantics wire rows := by
  intro row hrow _
  rw [installed.gate_output row hrow]
  have hin := installed.gate_input row hrow
  have hencoded := conversion_cell_encoded (installed.cell row)
    (installed.air row hrow) (installed.range_lookup row hrow)
  simpa [hin, base] using hencoded

/-- Public pin soundness with the component law discharged by installed row
AIR plus authenticated lookup closure, rather than assumed separately. -/
theorem control_pipeline_public_pin_sound_of_installed_rows
    (wire : Wire) (gates : List Gate) (conversions : List ConversionGate)
    (x hint z zp zc zd zx za zb : Nat)
    (falseBranch trueBranch selected sc sl sr : Nat)
    (result ip idiff ia mask : Nat)
    (basis masked inverseBasis scalar converted : Fin 4 → Nat)
    (zeroRows : ZeroTestRows wire gates x hint z zp zc zd zx za zb)
    (selectRows : SelectRows wire gates z falseBranch trueBranch sc sl sr selected)
    (inverseRows : InverseRows wire gates selected result ip idiff ia mask)
    (outputRows : ∀ i : Fin 4, OutputLaneRows wire gates conversions result i
      (basis i) (masked i) (inverseBasis i) (scalar i) (converted i))
    (hair : AirRows wire gates)
    (installed : InstalledConversionRows wire conversions)
    (hmask : ∀ i : Fin 4, coord (wire mask) i = 1) :
    let bit := if (wire x).a = 0 then (1 : F) else 0
    wire selected = (if bit = 0 then wire falseBranch else wire trueBranch) ∧
      (∀ i : Fin 4,
        decodeU32 (wire (publicOutputPin i)) = (coord (wire result) i).val ∧
        coord (if bit = 0 then wire falseBranch else wire trueBranch) i *
          (decodeU32 (wire (publicOutputPin i)) : F) = 1) := by
  exact control_pipeline_public_pin_sound wire gates conversions
    x hint z zp zc zd zx za zb falseBranch trueBranch selected sc sl sr
    result ip idiff ia mask basis masked inverseBasis scalar converted
    zeroRows selectRows inverseRows outputRows hair
    (conversion_semantics_of_installed_rows wire conversions installed) hmask

end S31.Functional.Correspondence.ControlGadgetConversionAir
