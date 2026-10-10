import S31.Gadgets.Air.TaggedPairAirClosure
import S31.Gadgets.Air.TaggedPairBridgeRows
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

/-- The source bridge's `offset=+1` mask in coset order. -/
def cosetNextEquiv (m : Nat) (hm : 0 < m) :
    Fin (2 * m) ≃ Fin (2 * m) := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  exact Equiv.addLeft (1 : Fin (2 * m))

theorem cosetNextEquiv_val (m : Nat) (hm : 0 < m)
    (index : Fin (2 * m)) :
    ((cosetNextEquiv m hm) index).val =
      (index.val + 1) % (2 * m) := by
  simp [cosetNextEquiv, Fin.val_add, Nat.add_comm]

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

/-- An explicit source obligation for `utils.bitReverseIndex`: applying it
twice on every logical trace index returns the original index. The Lean
result below needs exactly this property, rather than an unexplained
`Equiv` value. Proving the Zig `@bitReverse` intrinsic and shift implement
this property remains a machine-word correspondence task. -/
def bitReverseEquivOfInvolution {N : Nat}
    (bitReverseIndex : Fin N → Fin N)
    (hinvolution : ∀ index, bitReverseIndex (bitReverseIndex index) = index) :
    Fin N ≃ Fin N where
  toFun := bitReverseIndex
  invFun := bitReverseIndex
  left_inv := hinvolution
  right_inv := hinvolution

/-- Concrete logical-row predecessor formula from the equal-size branch of
`utils.previousBitReversedCircleDomainIndex`. The use of `cosetPrevEquiv`
expresses the source's modular offset `-1`. -/
def sourcePreviousIndex (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (index : Fin (2 * m)) : Fin (2 * m) :=
  bitReverseIndex (cosetToCircleIndex m
    (cosetPrevEquiv m hm
      (circleToCosetIndex m (bitReverseIndex index))))

theorem sourcePreviousIndex_bijective (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index) :
    Function.Bijective (sourcePreviousIndex m hm bitReverseIndex) := by
  let bitReverse := bitReverseEquivOfInvolution bitReverseIndex hinvolution
  have heq : sourcePreviousIndex m hm bitReverseIndex =
      nativePrevMask m hm bitReverse := by
    funext index
    rfl
  rw [heq]
  exact (nativePrevMask m hm bitReverse).bijective

/-- Concrete logical-row next mask used for the bridge's eight
`current-next` residuals. It uses modular offset `+1`, the inverse of
`cosetPrevEquiv`; all factors are permutations. -/
def sourceNextIndex (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (index : Fin (2 * m)) : Fin (2 * m) :=
  bitReverseIndex (cosetToCircleIndex m
    (cosetNextEquiv m hm
      (circleToCosetIndex m (bitReverseIndex index))))

theorem sourceNextIndex_bijective (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index) :
    Function.Bijective (sourceNextIndex m hm bitReverseIndex) := by
  let bitReverse := bitReverseEquivOfInvolution bitReverseIndex hinvolution
  let nextMask : Fin (2 * m) ≃ Fin (2 * m) :=
    bitReverse.trans (circleCosetEquiv m) |>.trans (cosetNextEquiv m hm)
      |>.trans (circleCosetEquiv m).symm |>.trans bitReverse
  have heq : sourceNextIndex m hm bitReverseIndex = nextMask := by
    funext index
    rfl
  rw [heq]
  exact nextMask.bijective

/-- Coset order exposes the source bridge's shifted mask as the ordinary
successor on sixteen rows. The conjugating map uses the *same* bit reversal
as the native source mask. -/
def bridgeCosetOrder
    (bitReverseIndex : Fin 16 → Fin 16)
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index) :
    Fin 16 ≃ Fin 16 :=
  (bitReverseEquivOfInvolution bitReverseIndex hinvolution).trans
    (circleCosetEquiv 8)

theorem bridgeCosetOrder_sourceNext
    (bitReverseIndex : Fin 16 → Fin 16)
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index)
    (index : Fin 16) :
    bridgeCosetOrder bitReverseIndex hinvolution
        (sourceNextIndex 8 (by decide) bitReverseIndex index) =
      cosetNextEquiv 8 (by decide)
        (bridgeCosetOrder bitReverseIndex hinvolution index) := by
  simp [bridgeCosetOrder, sourceNextIndex, bitReverseEquivOfInvolution,
    circleCosetEquiv, hinvolution, circleToCoset_cosetToCircle]

theorem sourceNext_bridgeCosetOrder_symm
    (bitReverseIndex : Fin 16 → Fin 16)
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index)
    (index : Fin 16) :
    sourceNextIndex 8 (by decide) bitReverseIndex
        ((bridgeCosetOrder bitReverseIndex hinvolution).symm index) =
      (bridgeCosetOrder bitReverseIndex hinvolution).symm
        (cosetNextEquiv 8 (by decide) index) := by
  apply (bridgeCosetOrder bitReverseIndex hinvolution).injective
  rw [bridgeCosetOrder_sourceNext]
  simp

/-- Logical source rows reordered by bit reversal and circle-to-coset. -/
def bridgeOrderedWords {F : Type*}
    (bitReverseIndex : Fin 16 → Fin 16)
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index)
    (rows : Fin 8 → Fin 16 → F) : Fin 8 → Fin 16 → F :=
  fun lane index => rows lane
    ((bridgeCosetOrder bitReverseIndex hinvolution).symm index)

/-- Source-shaped `current[lane]-next[lane]=0` on all sixteen bridge
logical rows entails eight constant endpoint columns. This discharges the
mask geometry of `TaggedPairBridgeRows.eight_columns_constant`, conditional
on the bit reversal involution and on accepted AIR residuals at each row. -/
theorem bridgeWords_constant_of_source_residuals
    {F : Type*} [AddGroup F]
    (bitReverseIndex : Fin 16 → Fin 16)
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index)
    (rows : Fin 8 → Fin 16 → F)
    (hzero : ∀ lane index,
      rows lane index -
        rows lane (sourceNextIndex 8 (by decide) bitReverseIndex index) = 0) :
    ∀ lane index,
      rows lane index =
        rows lane ((bridgeCosetOrder bitReverseIndex hinvolution).symm
          ⟨0, by decide⟩) := by
  let ordered := bridgeOrderedWords bitReverseIndex hinvolution rows
  have hadj : ∀ lane index,
      TaggedPairBridgeRows.adjacentResidual ordered lane index = 0 := by
    intro lane index
    have hsucc : cosetNextEquiv 8 (by decide)
          (⟨index.val, by omega⟩ : Fin 16) =
        (⟨index.val + 1, by omega⟩ : Fin 16) := by
      apply Fin.ext
      rw [cosetNextEquiv_val]
      change (index.val + 1) % 16 = index.val + 1
      omega
    simpa [TaggedPairBridgeRows.adjacentResidual, ordered,
      bridgeOrderedWords,
      sourceNext_bridgeCosetOrder_symm bitReverseIndex hinvolution,
      hsucc] using hzero lane
        ((bridgeCosetOrder bitReverseIndex hinvolution).symm
          (⟨index.val, by omega⟩ : Fin 16))
  have hconstant := TaggedPairBridgeRows.eight_columns_constant ordered hadj
  intro lane index
  simpa [ordered, bridgeOrderedWords] using
    hconstant lane (bridgeCosetOrder bitReverseIndex hinvolution index)

/-- Four-bit reversal for the bridge's fixed `log_size = 4`. The expression
is the low four bits of Zig's `@bitReverse(usize) >> (word_bits - 4)` on an
index in `0..15`. The machine-word identity is still an external source
correspondence obligation. -/
def bitReverse4 (index : Fin 16) : Fin 16 :=
  ⟨8 * (index.val % 2) +
    4 * ((index.val / 2) % 2) +
    2 * ((index.val / 4) % 2) +
    (index.val / 8) % 2, by omega⟩

theorem bitReverse4_involutive :
    ∀ index : Fin 16, bitReverse4 (bitReverse4 index) = index := by
  decide

/-- The bridge constancy result specialized to the exact four-bit reversal
formula and the native fixed sixteen-row shape. -/
theorem bridgeWords_constant_bitReverse4
    {F : Type*} [AddGroup F]
    (rows : Fin 8 → Fin 16 → F)
    (hzero : ∀ lane index,
      rows lane index -
        rows lane (sourceNextIndex 8 (by decide) bitReverse4 index) = 0) :
    ∀ lane index,
      rows lane index =
        rows lane ((bridgeCosetOrder bitReverse4
          bitReverse4_involutive).symm ⟨0, by decide⟩) :=
  bridgeWords_constant_of_source_residuals
    bitReverse4 bitReverse4_involutive rows hzero

end S31.Gadgets.Air.TaggedPairSourceCorrespondence
