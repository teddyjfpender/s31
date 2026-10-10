import S31.Gadgets.Air.TaggedPairAirClosure
import Mathlib.Tactic

/-!
Concrete source-level encodings for the staged tagged-pair verifier. This
models the fixed Gate relation words, source output addresses, fixed `u`
word, and claim-fold order. It does not prove Zig-to-Lean data conversion or
PCS/Fiat–Shamir soundness.
-/

namespace S31.Gadgets.Air.TaggedPairSourceCorrespondence

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge

/-- Six-word Gate tuple `[relation,address,a,b,c,d]` padded with a zero
seventh word for the joint seven-coordinate compression. -/
def paddedGateTuple (address : F) (value : Quad) : JointTuple :=
  fun i => match i.val with
    | 0 => liftBase 378353459
    | 1 => liftBase address
    | 2 => liftBase value.a
    | 3 => liftBase value.b
    | 4 => liftBase value.c
    | 5 => liftBase value.d
    | _ => 0

theorem padded_gate_compression_eq_native_six
    (address : F) (value : Quad) (alpha : GateSecure) :
    tupleHorner7 (paddedGateTuple address value) alpha =
      GateChallenge.tupleHorner
        (GateChallenge.gateTuple address value) alpha := by
  dsimp [tupleHorner7, GateChallenge.tupleHorner, paddedGateTuple,
    GateChallenge.gateTuple]
  simp

/-- The source loop in `trace.zig::lookupSum` starts public outputs at
`U_VAR_IDX + 1 = 3`, incrementing once per output. -/
def outputEventsAux (index : Nat) : List Quad → List JointTuple
  | [] => []
  | value :: rest =>
      paddedGateTuple ((3 + index : Nat) : F) value ::
        outputEventsAux (index + 1) rest

/-- Source `U_VALUE = QM31.fromU32Unchecked(0,0,1,0)` at address 2. -/
def fixedUEvent : JointTuple :=
  paddedGateTuple 2 ⟨0, 0, 1, 0⟩

def publicOutputYields (outputs : List Quad) : List JointTuple :=
  outputEventsAux 0 outputs ++ [fixedUEvent]

/-- The native `lookupSum` loop adds the output Gate inverses to the circuit
claimed sum, then adds the fixed `u` inverse. -/
def nativeOutputLoop (alpha z : GateSecure) :
    Nat → List Quad → GateSecure → GateSecure
  | _, [], sum => sum
  | index, value :: rest, sum =>
      nativeOutputLoop alpha z (index + 1) rest
        (sum + 1 / combine7
          (paddedGateTuple ((3 + index : Nat) : F) value) alpha z)

theorem nativeOutputLoop_eq_events (alpha z : GateSecure)
    (index : Nat) (outputs : List Quad) (initial : GateSecure) :
    nativeOutputLoop alpha z index outputs initial =
      initial + productionReciprocalSum7
        (outputEventsAux index outputs) alpha z := by
  induction outputs generalizing index initial with
  | nil => simp [nativeOutputLoop, outputEventsAux,
      productionReciprocalSum7]
  | cons value rest ih =>
      rw [nativeOutputLoop, ih]
      simp [outputEventsAux, productionReciprocalSum7]
      ring

def nativeLookupSum (outputs : List Quad)
    (claimed alpha z : GateSecure) : GateSecure :=
  nativeOutputLoop alpha z 0 outputs claimed +
    1 / combine7 fixedUEvent alpha z

theorem nativeLookupSum_eq_public_events (outputs : List Quad)
    (claimed alpha z : GateSecure) :
    nativeLookupSum outputs claimed alpha z =
      claimed + productionReciprocalSum7
        (publicOutputYields outputs) alpha z := by
  rw [nativeLookupSum, nativeOutputLoop_eq_events]
  simp [publicOutputYields, productionReciprocalSum7]
  ring

/-- Exact source order in `direct_pair_arithmetic.verifyBorrowed`:
`[circuit,chip0,chip1,bridge0,bridge1]`; only the circuit claim is first
passed through `direct_trace.lookupSum`, which adds public output and `u`
Gate terms. -/
def verifierClaimFold (outputs : List Quad)
    (claims : Fin 5 → GateSecure) (alpha z : GateSecure) : GateSecure :=
  nativeLookupSum outputs (claims 0) alpha z +
    claims 1 + claims 2 + claims 3 + claims 4

theorem verifierClaimFold_eq_source_closure
    (outputs : List Quad) (claims : Fin 5 → GateSecure)
    (alpha z : GateSecure) :
    verifierClaimFold outputs claims alpha z =
      claims 0 + claims 1 + claims 2 + claims 3 + claims 4 +
      productionReciprocalSum7 (publicOutputYields outputs)
        alpha z := by
  rw [verifierClaimFold, nativeLookupSum_eq_public_events]
  ring

/-- `utils.circleDomainIndexToCosetIndex` for a power-of-two domain
of size `N = 2m`. The source interleaves the first half and the reverse of
the second half. -/
def circleToCosetIndex (m : Nat) (index : Fin (2 * m)) :
    Fin (2 * m) :=
  ⟨if index.val < m then 2 * index.val
    else 2 * (2 * m - 1 - index.val) + 1, by
      have h := index.isLt
      split_ifs with hi <;> omega⟩

/-- `utils.cosetIndexToCircleDomainIndex` with the source's even/odd
formula. The odd branch is `(2N-j)/2`. -/
def cosetToCircleIndex (m : Nat) (index : Fin (2 * m)) :
    Fin (2 * m) :=
  ⟨if index.val % 2 = 0 then index.val / 2
    else (4 * m - index.val) / 2, by
      have h := index.isLt
      split_ifs with hi <;> omega⟩

theorem cosetToCircle_circleToCoset (m : Nat)
    (index : Fin (2 * m)) :
    cosetToCircleIndex m (circleToCosetIndex m index) = index := by
  apply Fin.ext
  simp only [circleToCosetIndex, cosetToCircleIndex]
  by_cases hi : index.val < m
  · simp [hi]
  · simp [hi]
    omega

theorem circleToCoset_cosetToCircle (m : Nat)
    (index : Fin (2 * m)) :
    circleToCosetIndex m (cosetToCircleIndex m index) = index := by
  have hinj : Function.Injective (circleToCosetIndex m) :=
    Function.LeftInverse.injective (cosetToCircle_circleToCoset m)
  have hsurj : Function.Surjective (circleToCosetIndex m) :=
    Finite.surjective_of_injective hinj
  obtain ⟨preimage, hpreimage⟩ := hsurj index
  rw [← hpreimage, cosetToCircle_circleToCoset]


def circleCosetEquiv (m : Nat) : Fin (2 * m) ≃ Fin (2 * m) where
  toFun := circleToCosetIndex m
  invFun := cosetToCircleIndex m
  left_inv := cosetToCircle_circleToCoset m
  right_inv := circleToCoset_cosetToCircle m

/-- Source `@mod(coset_index + @mod(-1,N),N)` is addition by `N−1`
in the cyclic index group. -/
def cosetPrevEquiv (m : Nat) (hm : 0 < m) :
    Fin (2 * m) ≃ Fin (2 * m) := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  exact Equiv.addLeft (⟨2 * m - 1, by omega⟩ : Fin (2 * m))

theorem cosetPrevEquiv_val (m : Nat) (hm : 0 < m)
    (index : Fin (2 * m)) :
    ((cosetPrevEquiv m hm) index).val =
      (index.val + (2 * m - 1)) % (2 * m) := by
  simp [cosetPrevEquiv, Fin.val_add, Nat.add_comm]

/-- At `domain_log_size = eval_log_size`, the source predecessor mask is a
composition: bit reverse, circle→coset, cyclic offset −1, coset→circle,
bit reverse. The actual machine `bitReverseIndex` is supplied as an
*equivalence premise*; its Zig-to-Lean identity is not proved here. -/
def nativePrevMask (m : Nat) (hm : 0 < m)
    (bitReverse : Fin (2 * m) ≃ Fin (2 * m)) :
    Fin (2 * m) ≃ Fin (2 * m) :=
  bitReverse.trans (circleCosetEquiv m) |>.trans (cosetPrevEquiv m hm)
    |>.trans (circleCosetEquiv m).symm |>.trans bitReverse

theorem nativePrevMask_source_formula (m : Nat) (hm : 0 < m)
    (bitReverse : Fin (2 * m) ≃ Fin (2 * m))
    (index : Fin (2 * m)) :
    nativePrevMask m hm bitReverse index =
      bitReverse (cosetToCircleIndex m
        (cosetPrevEquiv m hm
          (circleToCosetIndex m (bitReverse index)))) := rfl

/-- This is the row-mask permutation premise used by
`TaggedPairAirClosure`: any source bit reversal that is itself a
permutation makes the equal-size-domain predecessor mask a permutation.
No claim is made for the larger quotient evaluation domain here. -/
theorem nativePrevMask_bijective (m : Nat) (hm : 0 < m)
    (bitReverse : Fin (2 * m) ≃ Fin (2 * m)) :
    Function.Bijective (nativePrevMask m hm bitReverse) :=
  (nativePrevMask m hm bitReverse).bijective

end S31.Gadgets.Air.TaggedPairSourceCorrespondence
