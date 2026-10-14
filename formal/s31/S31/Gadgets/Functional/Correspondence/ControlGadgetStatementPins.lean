import S31.Gadgets.Functional.Correspondence.ControlGadgetConversionAir

/-!
The last local algebraic join for the bounded control program: a public-only
statement's eight canonical words are placed at Gate addresses 3 through 10.
The equality between the public output lookup events and physical Gate cells
is an explicit global LogUp premise. Accepted PCS/FRI proofs are not assumed
to imply that premise by this theorem.
-/

namespace S31.Functional.Correspondence.ControlGadgetStatementPins

open S31.Gadgets.Packed
open S31.Functional.Correspondence.ControlGadgetAir
open S31.Functional.Correspondence.ControlGadgetPublicPins
open S31.Functional.Correspondence.ControlGadgetConversionAir

def claimAddress (i : Fin 8) : Nat := 3 + i.val

/-- The exact `QM31.fromU32Unchecked(low, high, 0, 0)` used by the native
verifier after `relation.claimedWords` has checked canonical M31 values. -/
def encodeClaimWord (word : Nat) : Quad :=
  ⟨((word % 65536 : Nat) : F), ((word / 65536 : Nat) : F), 0, 0⟩

theorem decode_claim_word (word : Nat) (hcanonical : word < 2147483647) :
    decodeU32 (encodeClaimWord word) = word := by
  have hlo : word % 65536 < 2147483647 := by omega
  have hhi : word / 65536 < 2147483647 := by omega
  simp only [decodeU32, encodeClaimWord]
  change ((word % 65536 : Nat) : F).val +
    65536 * ((word / 65536 : Nat) : F).val = word
  rw [ZMod.val_natCast_of_lt hlo, ZMod.val_natCast_of_lt hhi]
  omega

/-- `output_event` is the **remaining authenticated lookup premise**: the
eight verifier-supplied output values must equal the addressed Gate cells.
The audit checks the exact native event order, but cannot derive this equality
from mere acceptance without global LogUp and PCS soundness. -/
structure PublicStatementLookup (wire : Wire) (words : Fin 8 → Nat) : Prop where
  canonical : ∀ i, words i < 2147483647
  output_event : ∀ i, wire (claimAddress i) = encodeClaimWord (words i)

structure InputPublicPinRows (wire : Wire) (gates : List Gate)
    (conversions : List ConversionGate) (x converted : Nat) : Prop where
  zero : wire 0 = base 0
  conversion_row : ⟨x, converted⟩ ∈ conversions
  pin_gate : ⟨.add, converted, 0, 3⟩ ∈ gates

theorem input_pin_sound (wire : Wire) (gates : List Gate)
    (conversions : List ConversionGate) (x converted : Nat)
    (rows : InputPublicPinRows wire gates conversions x converted)
    (hx : wire x = base (wire x).a)
    (hair : AirRows wire gates)
    (installed : InstalledConversionRows wire conversions) :
    decodeU32 (wire 3) = (wire x).a.val := by
  have hc := (conversion_semantics_of_installed_rows wire conversions installed)
    ⟨x, converted⟩ rows.conversion_row hx
  have hp : wire 3 = S31.Gadgets.Packed.add (wire converted) (wire 0) := by
    simpa [S31.Gadgets.Air.Qm31Ops.evaluate] using
      gate_sound wire gates hair _ rows.pin_gate
  have hp' : wire 3 = wire converted := by
    simpa [rows.zero, S31.Gadgets.Packed.add, base] using hp
  rw [hp', hc]
  exact decode_encode _

theorem control_program_public_statement_sound
    (wire : Wire) (gates : List Gate) (conversions : List ConversionGate)
    (words : Fin 8 → Nat)
    (x hint z zp zc zd zx za zb : Nat)
    (falseBranch trueBranch selected sc sl sr : Nat)
    (result ip idiff ia mask inputConverted : Nat)
    (basis masked inverseBasis scalar converted : Fin 4 → Nat)
    (zeroRows : ZeroTestRows wire gates x hint z zp zc zd zx za zb)
    (selectRows : SelectRows wire gates z falseBranch trueBranch sc sl sr selected)
    (inverseRows : InverseRows wire gates selected result ip idiff ia mask)
    (inputRows : InputPublicPinRows wire gates conversions x inputConverted)
    (outputRows : ∀ i : Fin 4, OutputLaneRows wire gates conversions result i
      (basis i) (masked i) (inverseBasis i) (scalar i) (converted i))
    (hair : AirRows wire gates)
    (installed : InstalledConversionRows wire conversions)
    (hmask : ∀ i : Fin 4, coord (wire mask) i = 1)
    (statement : PublicStatementLookup wire words) :
    let bit := if (wire x).a = 0 then (1 : F) else 0
    words ⟨0, by decide⟩ = (wire x).a.val ∧
      wire selected = (if bit = 0 then wire falseBranch else wire trueBranch) ∧
      (∀ i : Fin 4,
        words ⟨i.val + 1, by omega⟩ = (coord (wire result) i).val ∧
        coord (if bit = 0 then wire falseBranch else wire trueBranch) i *
          (words ⟨i.val + 1, by omega⟩ : F) = 1) := by
  obtain ⟨hselected, hresult⟩ :=
    control_pipeline_public_pin_sound_of_installed_rows wire gates conversions
      x hint z zp zc zd zx za zb falseBranch trueBranch selected sc sl sr
      result ip idiff ia mask basis masked inverseBasis scalar converted
      zeroRows selectRows inverseRows outputRows hair installed hmask
  have hinput := input_pin_sound wire gates conversions x inputConverted
    inputRows zeroRows.x_scalar hair installed
  refine ⟨?_, hselected, ?_⟩
  · have hclaim := statement.output_event ⟨0, by decide⟩
    have hdecode := decode_claim_word (words ⟨0, by decide⟩)
      (statement.canonical ⟨0, by decide⟩)
    have hlookup : decodeU32 (wire 3) = words ⟨0, by decide⟩ := by
      have haddr : claimAddress ⟨0, by decide⟩ = 3 := by rfl
      rw [← haddr, hclaim, hdecode]
    exact hlookup.symm.trans hinput
  · intro i
    obtain ⟨hpin, hinverse⟩ := hresult i
    let j : Fin 8 := ⟨i.val + 1, by omega⟩
    have hclaim := statement.output_event j
    have hdecode := decode_claim_word (words j) (statement.canonical j)
    have hword : words j = (coord (wire result) i).val := by
      have haddr : claimAddress j = publicOutputPin i := by
        simp only [claimAddress, publicOutputPin, j]
        omega
      rw [← haddr, hclaim, hdecode] at hpin
      exact hpin
    have hinverse' : coord (if (if (wire x).a = 0 then (1 : F) else 0) = 0
        then wire falseBranch else wire trueBranch) i * (words j : F) = 1 := by
      have haddr : claimAddress j = publicOutputPin i := by
        simp only [claimAddress, publicOutputPin, j]
        omega
      rw [← haddr, hclaim, hdecode] at hinverse
      exact hinverse
    exact ⟨hword, hinverse'⟩

end S31.Functional.Correspondence.ControlGadgetStatementPins
