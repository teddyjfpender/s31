import S31.Gadgets.Functional.Correspondence.ControlGadgetAir

/-!
The public-output boundary for the bounded scalar-control source shape.
Native topology admission checks the exact extraction, conversion, and pin
addresses. This theorem uses the generic Gate AIR equations for extraction
and pinning, plus an explicit semantic premise for the M31-to-u32 component.
That premise is not derived from native lookup/permutation acceptance here.
-/

namespace S31.Functional.Correspondence.ControlGadgetPublicPins

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.Correspondence.ControlGadgetAir

def encodeM31ToU32 (x : F) : Quad :=
  ⟨(↑(x.val % 65536) : F), (↑(x.val / 65536) : F), 0, 0⟩

def decodeU32 (value : Quad) : Nat := value.a.val + 65536 * value.b.val

theorem decode_encode (x : F) : decodeU32 (encodeM31ToU32 x) = x.val := by
  have hval : x.val < 2147483647 := ZMod.val_lt x
  have hlo : x.val % 65536 < 2147483647 := by omega
  have hhi : x.val / 65536 < 2147483647 := by omega
  change (↑(x.val % 65536) : F).val + 65536 * (↑(x.val / 65536) : F).val = x.val
  rw [ZMod.val_natCast_of_lt hlo, ZMod.val_natCast_of_lt hhi]
  omega

theorem encode_canonical_limbs (x : F) :
    (encodeM31ToU32 x).a.val < 65536 ∧
      (encodeM31ToU32 x).b.val < 32768 := by
  have hval : x.val < 2147483647 := ZMod.val_lt x
  have hlo : x.val % 65536 < 2147483647 := by omega
  have hhi : x.val / 65536 < 2147483647 := by omega
  change (↑(x.val % 65536) : F).val < 65536 ∧
    (↑(x.val / 65536) : F).val < 32768
  rw [ZMod.val_natCast_of_lt hlo, ZMod.val_natCast_of_lt hhi]
  constructor <;> omega

structure ConversionGate where
  input : Nat
  out : Nat
  deriving DecidableEq

/-- The component-level conversion law. Membership and fixed addresses are
checked by the native topology audit; deriving this law from the installed
M31-to-u32 AIR and its lookup closure remains a separate obligation. -/
def ConversionSemantics (wire : Wire) (rows : List ConversionGate) : Prop :=
  ∀ row ∈ rows, wire row.input = base (wire row.input).a →
    wire row.out = encodeM31ToU32 (wire row.input).a

def publicOutputPin (i : Fin 4) : Nat := 4 + i.val

/-- The first lane needs only a basis mask. The other three lanes multiply
their masked QM31 basis coordinate by its derived inverse basis constant. -/
structure OutputLaneRows (wire : Wire) (gates : List Gate)
    (conversions : List ConversionGate) (result : Nat) (i : Fin 4)
    (basis masked inverseBasis scalar converted : Nat) : Prop where
  zero : wire 0 = base 0
  basis_value : wire basis = unit i
  inverse_basis_value : wire inverseBasis = unitInverse i
  mask_gate : ⟨.pointwiseMul, result, basis, masked⟩ ∈ gates
  first_scalar : i.val = 0 → scalar = masked
  later_scalar : i.val ≠ 0 → ⟨.mul, masked, inverseBasis, scalar⟩ ∈ gates
  conversion_row : ⟨scalar, converted⟩ ∈ conversions
  pin_gate : ⟨.add, converted, 0, publicOutputPin i⟩ ∈ gates

theorem output_lane_pin_sound (wire : Wire) (gates : List Gate)
    (conversions : List ConversionGate) (result : Nat) (i : Fin 4)
    (basis masked inverseBasis scalar converted : Nat)
    (rows : OutputLaneRows wire gates conversions result i basis masked
      inverseBasis scalar converted)
    (hair : AirRows wire gates) (hconversion : ConversionSemantics wire conversions) :
    decodeU32 (wire (publicOutputPin i)) = (coord (wire result) i).val := by
  have hm : wire masked = pointwise (wire result) (unit i) := by
    simpa [evaluate, rows.basis_value] using
      gate_sound wire gates hair _ rows.mask_gate
  have hs : wire scalar = base (coord (wire result) i) := by
    by_cases hi : i.val = 0
    · have hfirst := rows.first_scalar hi
      have hi0 : i = ⟨0, by decide⟩ := Fin.ext hi
      subst i
      rw [hfirst, hm]
      ext <;> simp [pointwise, unit, base, coord]
    · have hscale : wire scalar = mul (wire masked) (wire inverseBasis) := by
        simpa [evaluate] using gate_sound wire gates hair _ (rows.later_scalar hi)
      rw [hscale, hm, rows.inverse_basis_value, unpack_coordinate]
  have hc : wire converted = encodeM31ToU32 (wire scalar).a :=
    hconversion _ rows.conversion_row (by rw [hs]; rfl)
  have hp : wire (publicOutputPin i) = S31.Gadgets.Packed.add (wire converted) (wire 0) := by
    simpa [evaluate] using gate_sound wire gates hair _ rows.pin_gate
  have hp' : wire (publicOutputPin i) = wire converted := by
    simpa [rows.zero, S31.Gadgets.Packed.add, base] using hp
  rw [hp', hc, hs]
  exact decode_encode _

/-- The source-selected branch's inverse is the value exposed at each of the
four public output pins, under the explicit M31-to-u32 component law. -/
theorem control_pipeline_public_pin_sound (wire : Wire) (gates : List Gate)
    (conversions : List ConversionGate)
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
    (hconversion : ConversionSemantics wire conversions)
    (hmask : ∀ i : Fin 4, coord (wire mask) i = 1) :
    let bit := if (wire x).a = 0 then (1 : F) else 0
    wire selected = (if bit = 0 then wire falseBranch else wire trueBranch) ∧
      (∀ i : Fin 4,
        decodeU32 (wire (publicOutputPin i)) = (coord (wire result) i).val ∧
        coord (if bit = 0 then wire falseBranch else wire trueBranch) i *
          (decodeU32 (wire (publicOutputPin i)) : F) = 1) := by
  obtain ⟨hselected, hinverse⟩ := control_pipeline_air_sound wire gates
    x hint z zp zc zd zx za zb falseBranch trueBranch selected sc sl sr
    result ip idiff ia mask zeroRows selectRows inverseRows hair hmask
  refine ⟨hselected, ?_⟩
  intro i
  have hpin := output_lane_pin_sound wire gates conversions result i
    (basis i) (masked i) (inverseBasis i) (scalar i) (converted i)
    (outputRows i) hair hconversion
  refine ⟨hpin, ?_⟩
  rw [hpin, ZMod.natCast_zmod_val]
  exact hinverse i

end S31.Functional.Correspondence.ControlGadgetPublicPins
