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

def bridgeEvenLane (slot : Fin 4) : Fin 8 :=
  ⟨2 * slot.val, by omega⟩

def bridgeOddLane (slot : Fin 4) : Fin 8 :=
  ⟨2 * slot.val + 1, by omega⟩

def bridgeInputLane (slot : Fin 4) : Fin 8 :=
  ⟨slot.val, by omega⟩

def bridgeOutputLane (slot : Fin 4) : Fin 8 :=
  ⟨4 + slot.val, by omega⟩

/-- Native source's eight Gate endpoint words and two tagged chip endpoints,
formed from one row of eight committed bridge main columns. -/
def sourceBridgeGateTuple
    (addresses : Fin 8 → F) (words : Fin 8 → Fin 16 → F)
    (lane : Fin 8) (row : Fin 16) : JointTuple :=
  gateTuple7 (addresses lane) (words lane row)

def sourceBridgeStartTuple
    (call : F) (words : Fin 8 → Fin 16 → F)
    (row : Fin 16) : JointTuple :=
  chipTuple7 call 0 (fun slot => words (bridgeInputLane slot) row)

def sourceBridgeFinishTuple
    (call rounds : F) (words : Fin 8 → Fin 16 → F)
    (row : Fin 16) : JointTuple :=
  chipTuple7 call rounds (fun slot => words (bridgeOutputLane slot) row)

/-- Native-shaped bridge denominator fields, before constancy is derived. -/
def sourceBridgeD0 (addresses : Fin 8 → F)
    (words : Fin 8 → Fin 16 → F)
    (alpha z : GateSecure) (slot : Fin 4) (row : Fin 16) : GateSecure :=
  combine7 (sourceBridgeGateTuple addresses words (bridgeEvenLane slot) row)
    alpha z

def sourceBridgeD1 (addresses : Fin 8 → F)
    (words : Fin 8 → Fin 16 → F)
    (alpha z : GateSecure) (slot : Fin 4) (row : Fin 16) : GateSecure :=
  combine7 (sourceBridgeGateTuple addresses words (bridgeOddLane slot) row)
    alpha z

def sourceBridgeFirst (call : F) (words : Fin 8 → Fin 16 → F)
    (alpha z : GateSecure) (row : Fin 16) : GateSecure :=
  combine7 (sourceBridgeStartTuple call words row) alpha z

def sourceBridgeLast (call rounds : F)
    (words : Fin 8 → Fin 16 → F)
    (alpha z : GateSecure) (row : Fin 16) : GateSecure :=
  combine7 (sourceBridgeFinishTuple call rounds words row) alpha z

def sourceBridgeAnchor : Fin 16 :=
  (bridgeCosetOrder bitReverse4 bitReverse4_involutive).symm 0

def sourceBridgeGateEvents (addresses : Fin 8 → F)
    (words : Fin 8 → Fin 16 → F) : List JointTuple :=
  [sourceBridgeGateTuple addresses words (bridgeEvenLane 0) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeOddLane 0) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeEvenLane 1) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeOddLane 1) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeEvenLane 2) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeOddLane 2) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeEvenLane 3) sourceBridgeAnchor,
   sourceBridgeGateTuple addresses words (bridgeOddLane 3) sourceBridgeAnchor]

def sourceBridgeStartEvents (call : F)
    (words : Fin 8 → Fin 16 → F) : List JointTuple :=
  [sourceBridgeStartTuple call words sourceBridgeAnchor]

def sourceBridgeFinishEvents (call rounds : F)
    (words : Fin 8 → Fin 16 → F) : List JointTuple :=
  [sourceBridgeFinishTuple call rounds words sourceBridgeAnchor]

/-- All eight native main-column residuals and five native interaction
residuals imply the claimed bridge sum is the exact endpoint event sum.
The source fixed `+1` and `-1` masks are used directly. The accepted-row
premises and nonzero denominators remain explicit; this does not infer them
from PCS or a native verifier result. -/
theorem source_bridge_claim_eq_endpoint_events
    (addresses : Fin 8 → F) (call rounds : F)
    (words : Fin 8 → Fin 16 → F)
    (current : Fin 5 → Fin 16 → GateSecure)
    (claim alpha z : GateSecure)
    (h16 : (16 : GateSecure) ≠ 0)
    (hwords : ∀ lane row,
      words lane row - words lane
        (sourceNextIndex 8 (by decide) bitReverse4 row) = 0)
    (hinteraction : TaggedPairAirClosure.BridgeAccepted
      (nativePrevMask 8 (by decide)
        (bitReverseEquivOfInvolution bitReverse4 bitReverse4_involutive))
      (sourceBridgeD0 addresses words alpha z)
      (sourceBridgeD1 addresses words alpha z)
      (sourceBridgeFirst call words alpha z)
      (sourceBridgeLast call rounds words alpha z)
      current claim)
    (hnonzero0 : ∀ slot,
      sourceBridgeD0 addresses words alpha z slot
        sourceBridgeAnchor ≠ 0)
    (hnonzero1 : ∀ slot,
      sourceBridgeD1 addresses words alpha z slot
        sourceBridgeAnchor ≠ 0)
    (hnonzeroFirst :
      sourceBridgeFirst call words alpha z
        sourceBridgeAnchor ≠ 0)
    (hnonzeroLast :
      sourceBridgeLast call rounds words alpha z
        sourceBridgeAnchor ≠ 0) :
    claim = productionReciprocalSum7
      (sourceBridgeGateEvents addresses words) alpha z -
      productionReciprocalSum7 (sourceBridgeStartEvents call words) alpha z +
      productionReciprocalSum7
        (sourceBridgeFinishEvents call rounds words) alpha z := by
  let anchor := sourceBridgeAnchor
  have hconst := bridgeWords_constant_bitReverse4 words hwords
  have hd0 : ∀ slot row,
      sourceBridgeD0 addresses words alpha z slot row =
        sourceBridgeD0 addresses words alpha z slot anchor := by
    intro slot row
    simp [sourceBridgeD0, sourceBridgeGateTuple, hconst]
  have hd1 : ∀ slot row,
      sourceBridgeD1 addresses words alpha z slot row =
        sourceBridgeD1 addresses words alpha z slot anchor := by
    intro slot row
    simp [sourceBridgeD1, sourceBridgeGateTuple, hconst]
  have hfirst : ∀ row,
      sourceBridgeFirst call words alpha z row =
        sourceBridgeFirst call words alpha z anchor := by
    intro row
    simp [sourceBridgeFirst, sourceBridgeStartTuple, hconst]
  have hlast : ∀ row,
      sourceBridgeLast call rounds words alpha z row =
        sourceBridgeLast call rounds words alpha z anchor := by
    intro row
    simp [sourceBridgeLast, sourceBridgeFinishTuple, hconst]
  have haccepted : TaggedPairAirClosure.BridgeAccepted
      (nativePrevMask 8 (by decide)
        (bitReverseEquivOfInvolution bitReverse4 bitReverse4_involutive))
      (fun slot _ => sourceBridgeD0 addresses words alpha z slot anchor)
      (fun slot _ => sourceBridgeD1 addresses words alpha z slot anchor)
      (fun _ => sourceBridgeFirst call words alpha z anchor)
      (fun _ => sourceBridgeLast call rounds words alpha z anchor)
      current claim := by
    intro row
    simpa only [hd0, hd1, hfirst, hlast] using hinteraction row
  have hsum := TaggedPairAirClosure.bridge_air_claim_eq_endpoint_reciprocals
    (nativePrevMask 8 (by decide)
      (bitReverseEquivOfInvolution bitReverse4 bitReverse4_involutive))
    (fun slot => sourceBridgeD0 addresses words alpha z slot anchor)
    (fun slot => sourceBridgeD1 addresses words alpha z slot anchor)
    (sourceBridgeFirst call words alpha z anchor)
    (sourceBridgeLast call rounds words alpha z anchor)
    current claim h16 haccepted hnonzero0 hnonzero1
    hnonzeroFirst hnonzeroLast
  rw [hsum]
  simp only [sourceBridgeGateEvents, sourceBridgeStartEvents,
    sourceBridgeFinishEvents, productionReciprocalSum7,
    List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  simp only [sourceBridgeD0, sourceBridgeD1, sourceBridgeFirst,
    sourceBridgeLast, div_eq_mul_inv, one_mul]
  ring

/-- The source chip's seven-word input tuple uses verifier-fixed `call`,
witness `step`, and four witness input lanes. -/
def sourceChipInputTuple {R : Nat} (call : F)
    (step : Fin R → F) (input : Fin R → Fin 4 → F)
    (row : Fin R) : JointTuple :=
  chipTuple7 call (step row) (input row)

/-- The chip's output event has the same fixed call tag and witness
`step + 1` in the M31 field. Exact event balance, not a local AIR range
check, later rules out wrapped or duplicate steps for `R < p`. -/
def sourceChipOutputTuple {R : Nat} (call : F)
    (step : Fin R → F) (output : Fin R → Fin 4 → F)
    (row : Fin R) : JointTuple :=
  chipTuple7 call (step row + 1) (output row)

def sourceChipQin {R : Nat} (call : F)
    (step : Fin R → F) (input : Fin R → Fin 4 → F)
    (alpha z : GateSecure) (row : Fin R) : GateSecure :=
  combine7 (sourceChipInputTuple call step input row) alpha z

def sourceChipQout {R : Nat} (call : F)
    (step : Fin R → F) (output : Fin R → Fin 4 → F)
    (alpha z : GateSecure) (row : Fin R) : GateSecure :=
  combine7 (sourceChipOutputTuple call step output row) alpha z

/-- Native-shaped chip interaction closure with the source's equal-size
logical predecessor mask. The fixed call ID is separate from all witness
columns. This theorem does not assume canonical step order; exact tagged
event balance and `R < p` are used later to prove that property. -/
theorem source_chip_claim_eq_transition_events
    (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (hinvolution : ∀ index,
      bitReverseIndex (bitReverseIndex index) = index)
    (call : F)
    (step : Fin (2 * m) → F)
    (input output : Fin (2 * m) → Fin 4 → F)
    (first current : Fin (2 * m) → GateSecure)
    (claim alpha z : GateSecure)
    (hR : ((2 * m : Nat) : GateSecure) ≠ 0)
    (hinteraction : TaggedPairAirClosure.ChipAccepted
      (nativePrevMask m hm
        (bitReverseEquivOfInvolution bitReverseIndex hinvolution))
      (sourceChipQin call step input alpha z)
      (sourceChipQout call step output alpha z)
      first current claim) :
    claim = productionReciprocalSum7
      (List.ofFn (sourceChipInputTuple call step input)) alpha z -
      productionReciprocalSum7
        (List.ofFn (sourceChipOutputTuple call step output)) alpha z := by
  exact TaggedPairAirClosure.chip_air_claim_eq_event_sums
    (nativePrevMask m hm
      (bitReverseEquivOfInvolution bitReverseIndex hinvolution))
    (sourceChipInputTuple call step input)
    (sourceChipOutputTuple call step output)
    (sourceChipQin call step input alpha z)
    (sourceChipQout call step output alpha z)
    first current claim alpha z hR hinteraction
    (by intro row; rfl) (by intro row; rfl)
    (TaggedPairAirClosure.chip_accepted_input_nonzero hinteraction)
    (TaggedPairAirClosure.chip_accepted_output_nonzero hinteraction)

private theorem liftBase_add (left right : F) :
    liftBase (left + right) = liftBase left + liftBase right := by
  rfl

private theorem liftBase_mul (left right : F) :
    liftBase (left * right) = liftBase left * liftBase right := by
  simp [liftBase]

/-- The chip's four secure-field residuals imply the four actual M31
affine-square transitions. This uses injectivity of the M31-to-QM31
embedding and its addition/multiplication compatibility. -/
theorem source_chip_arithmetic_residuals_sound
    {R : Nat} (constant : F)
    (input output : Fin R → Fin 4 → F)
    (hresidual : ∀ row lane,
      liftBase (output row lane) -
        (liftBase (input row lane)) ^ 2 - liftBase constant = 0) :
    ∀ row lane,
      output row lane = (input row lane) ^ 2 + constant := by
  intro row lane
  apply liftBase_injective
  rw [liftBase_add, pow_two, liftBase_mul]
  have h := hresidual row lane
  linear_combination h

end S31.Gadgets.Air.TaggedPairSourceCorrespondence
