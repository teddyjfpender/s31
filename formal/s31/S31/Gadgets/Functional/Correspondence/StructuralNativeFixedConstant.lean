import S31.Gadgets.Functional.Correspondence.StructuralNativeGateOwnership

/-!
Local native AIR ownership of bounded nonzero M31 literals. The direct Gate
builder derives its interned constants from reserved zero, one, and `u` wires;
the `u` word is a verifier public output. This module keeps that public-output
authentication as an explicit premise and derives the remaining chain from
native AIR rows. It does not authenticate supplied graph bytes or proof cells.
-/

namespace S31.Functional.Correspondence.StructuralNativeFixedConstant

open S31
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open S31.Functional.Correspondence.GeneralLinearSSAEffects
open S31.Functional.Correspondence.StructuralNativeTraceDecoder
open S31.Functional.Correspondence.GeneralLinearSSABytes
  (Parse fields field nat array)
open Lean
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeGateOwnership

structure MulGate where
  in0 : Nat
  in1 : Nat
  out : Nat
  deriving DecidableEq, Repr

def NativeMulAirRows (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List MulGate) : Prop :=
  ∀ gate ∈ gates, ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
    (S31.Gadgets.Air.Qm31Ops.encode .mul)
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out)), r = 0

theorem mul_gate_packed_sound
    (wire : Nat → StructuralNativeGateCertificate.Quad) (gates : List MulGate)
    (gate : MulGate) (hgate : gate ∈ gates)
    (hair : NativeMulAirRows wire gates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out) =
      S31.Gadgets.Packed.mul
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1)) := by
  have h := S31.Gadgets.Air.NativeQm31AirProof.native_accepts_iff
    (S31.Gadgets.Air.Qm31Ops.encode .mul)
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out))
  have haccepted := h.mp (hair gate hgate)
  obtain ⟨op, heq, hout⟩ := haccepted
  have hop : op = S31.Gadgets.Air.Qm31Ops.Op.mul := by
    cases op <;> simp_all [S31.Gadgets.Air.Qm31Ops.encode]
  subst op
  simpa [S31.Gadgets.Air.Qm31Ops.evaluate] using hout

private theorem u_mul_one_unique (candidate : S31.Gadgets.Packed.Quad)
    (h : S31.Gadgets.Packed.mul ⟨0, 0, 1, 0⟩ candidate = ⟨0, 0, 1, 0⟩) :
    candidate = ⟨1, 0, 0, 0⟩ := by
  have ha := congrArg S31.Gadgets.Packed.Quad.a h
  have hb := congrArg S31.Gadgets.Packed.Quad.b h
  have hc := congrArg S31.Gadgets.Packed.Quad.c h
  have hd := congrArg S31.Gadgets.Packed.Quad.d h
  have ha' : 2 * candidate.c - candidate.d = 0 := by
    simpa [S31.Gadgets.Packed.mul] using ha
  have hb' : candidate.c + 2 * candidate.d = 0 := by
    simpa [S31.Gadgets.Packed.mul] using hb
  have hc' : candidate.a = 1 := by
    simpa [S31.Gadgets.Packed.mul] using hc
  have hd' : candidate.b = 0 := by
    simpa [S31.Gadgets.Packed.mul] using hd
  have hfive : (5 : S31.Field.F) ≠ 0 := by decide
  have hproduct : (5 : S31.Field.F) * candidate.c = 0 := by
    linear_combination 2 * ha' + hb'
  have hczero : candidate.c = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left hfive
  have hdzero : candidate.d = 0 := by
    linear_combination -ha' + 2 * hczero
  exact S31.Gadgets.Packed.Quad.ext hc' hd' hczero hdzero

/-- The verifier-public `u` output, together with its actual native
`Mul(u, one, u)` finalization row, fixes the reserved one wire. Authenticating
the supplied public-output cell to a proof remains an explicit premise. -/
theorem one_anchor_air_sound
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (mulGates : List MulGate)
    (hpublicU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hanchor : (⟨2, 1, 2⟩ : MulGate) ∈ mulGates)
    (hair : NativeMulAirRows wire mulGates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire 1) = ⟨1, 0, 0, 0⟩ := by
  have hgate := mul_gate_packed_sound wire mulGates ⟨2, 1, 2⟩ hanchor hair
  exact u_mul_one_unique _ (by simpa [hpublicU] using hgate.symm)

/-- Reuse the exact native nine-residual relation for finalization's linear
add and subtract rows, retaining the gate's physical addresses. -/
theorem linear_gate_packed_sound
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (gate : Gate) (hgate : gate ∈ gates)
    (hair : NativeAirRows wire gates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out) =
      S31.Gadgets.Air.Qm31Ops.evaluate gate.op.airOp
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1)) := by
  have hmodel : S31.Gadgets.Air.Qm31Ops.accepts
      (S31.Gadgets.Air.Qm31Ops.encode gate.op.airOp)
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out)) := by
    simpa [S31.Gadgets.Air.Qm31Ops.accepts,
      S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq] using
      hair gate hgate
  exact (S31.Gadgets.Air.Qm31Ops.accepts_encoded gate.op.airOp _ _ _).mp hmodel

structure SevenPath where
  base2 : Nat
  base3 : Nat
  base4 : Nat
  base5 : Nat
  base6 : Nat
  base7 : Nat
  uSquare : Nat
  i : Nat
  iPlusOne : Nat
  uPlusIu : Nat
  ones : Nat
  broadcast7 : Nat
  deriving Repr

/-- Exact native finalization gates used by the seven-literal certificate.
The addresses may vary by source; gate membership, not a guessed numeric
address, owns each intermediate. -/
def SevenPath.owned (path : SevenPath) (gates : List Gate)
    (mulGates : List MulGate) : Prop :=
  (⟨.add, 1, 1, path.base2⟩ : Gate) ∈ gates ∧
  (⟨.add, path.base2, 1, path.base3⟩ : Gate) ∈ gates ∧
  (⟨.add, path.base3, 1, path.base4⟩ : Gate) ∈ gates ∧
  (⟨.add, path.base4, 1, path.base5⟩ : Gate) ∈ gates ∧
  (⟨.add, path.base5, 1, path.base6⟩ : Gate) ∈ gates ∧
  (⟨.add, path.base6, 1, path.base7⟩ : Gate) ∈ gates ∧
  (⟨.sub, path.uSquare, path.base2, path.i⟩ : Gate) ∈ gates ∧
  (⟨.add, path.i, 1, path.iPlusOne⟩ : Gate) ∈ gates ∧
  (⟨.add, path.iPlusOne, path.uPlusIu, path.ones⟩ : Gate) ∈ gates ∧
  (⟨2, 1, 2⟩ : MulGate) ∈ mulGates ∧
  (⟨2, 2, path.uSquare⟩ : MulGate) ∈ mulGates ∧
  (⟨path.iPlusOne, 2, path.uPlusIu⟩ : MulGate) ∈ mulGates ∧
  (⟨path.base7, path.ones, path.broadcast7⟩ : MulGate) ∈ mulGates

def SevenPath.linearGates (path : SevenPath) : List Gate :=
  [⟨.add, 1, 1, path.base2⟩,
   ⟨.add, path.base2, 1, path.base3⟩,
   ⟨.add, path.base3, 1, path.base4⟩,
   ⟨.add, path.base4, 1, path.base5⟩,
   ⟨.add, path.base5, 1, path.base6⟩,
   ⟨.add, path.base6, 1, path.base7⟩,
   ⟨.sub, path.uSquare, path.base2, path.i⟩,
   ⟨.add, path.i, 1, path.iPlusOne⟩,
   ⟨.add, path.iPlusOne, path.uPlusIu, path.ones⟩]

def SevenPath.mulGates (path : SevenPath) : List MulGate :=
  [⟨2, 1, 2⟩, ⟨2, 2, path.uSquare⟩,
   ⟨path.iPlusOne, 2, path.uPlusIu⟩,
   ⟨path.base7, path.ones, path.broadcast7⟩]

def SevenPath.checkOwned (path : SevenPath) (gates : List Gate)
    (mulGates : List MulGate) : Bool :=
  path.linearGates.all (fun gate => decide (gate ∈ gates)) &&
    path.mulGates.all (fun gate => decide (gate ∈ mulGates))

theorem SevenPath.checkOwned_sound (path : SevenPath) (gates : List Gate)
    (mulGates : List MulGate)
    (hcheck : path.checkOwned gates mulGates = true) :
    path.owned gates mulGates := by
  simp [SevenPath.checkOwned, SevenPath.linearGates,
    SevenPath.mulGates, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  unfold SevenPath.owned
  tauto

/-- The complete bounded Zig finalization path forces a broadcast seven in
all four physical coordinates, given the verifier-public `u` cell. -/
theorem seven_path_air_sound
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (mulGates : List MulGate) (path : SevenPath)
    (hpublicU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hpath : path.owned gates mulGates)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire path.broadcast7) =
      ⟨7, 7, 7, 7⟩ := by
  rcases hpath with
    ⟨h2, h3, h4, h5, h6, h7, hi, hi1, hones, h1, hu2, hui, hbroadcast⟩
  have hone := one_anchor_air_sound wire mulGates hpublicU h1 hmul
  have hbase2 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base2) =
      ⟨2, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, 1, 1, path.base2⟩ h2 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hone] using h
  have hbase3 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base3) =
      ⟨3, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.base2, 1, path.base3⟩ h3 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hbase2, hone] using h
  have hbase4 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base4) =
      ⟨4, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.base3, 1, path.base4⟩ h4 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hbase3, hone] using h
  have hbase5 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base5) =
      ⟨5, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.base4, 1, path.base5⟩ h5 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hbase4, hone] using h
  have hbase6 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base6) =
      ⟨6, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.base5, 1, path.base6⟩ h6 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hbase5, hone] using h
  have hbase7 : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.base7) =
      ⟨7, 0, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.base6, 1, path.base7⟩ h7 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hbase6, hone] using h
  have huSquare : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.uSquare) =
      ⟨2, 1, 0, 0⟩ := by
    have h := mul_gate_packed_sound wire mulGates
      ⟨2, 2, path.uSquare⟩ hu2 hmul
    simpa [hpublicU, S31.Gadgets.Packed.mul] using h
  have hI : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.i) =
      ⟨0, 1, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.sub, path.uSquare, path.base2, path.i⟩ hi hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Air.Qm31Ops.subtract, huSquare, hbase2] using h
  have hIPlusOne : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.iPlusOne) =
      ⟨1, 1, 0, 0⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.i, 1, path.iPlusOne⟩ hi1 hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hI, hone] using h
  have hUPlusIu : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.uPlusIu) =
      ⟨0, 0, 1, 1⟩ := by
    have h := mul_gate_packed_sound wire mulGates
      ⟨path.iPlusOne, 2, path.uPlusIu⟩ hui hmul
    simpa [hIPlusOne, hpublicU, S31.Gadgets.Packed.mul] using h
  have hOnes : S31.Gadgets.Air.Qm31Ops.packM31 (wire path.ones) =
      ⟨1, 1, 1, 1⟩ := by
    have h := linear_gate_packed_sound wire gates
      ⟨.add, path.iPlusOne, path.uPlusIu, path.ones⟩ hones hair
    simpa [GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, hIPlusOne, hUPlusIu] using h
  have h := mul_gate_packed_sound wire mulGates
    ⟨path.base7, path.ones, path.broadcast7⟩ hbroadcast hmul
  simpa [hbase7, hOnes, S31.Gadgets.Packed.mul] using h

theorem seven_path_quad_sound
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (mulGates : List MulGate) (path : SevenPath)
    (hpublicU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hpath : path.owned gates mulGates)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    wire path.broadcast7 = fun _ => RiscvRefinement.M31.reduce 7 := by
  have hpacked := seven_path_air_sound wire gates mulGates path
    hpublicU hpath hair hmul
  funext i
  apply S31.Field.toZMod_injective
  have hcoord := congrArg (fun q => S31.Gadgets.Packed.coord q i) hpacked
  fin_cases i <;>
    simpa [S31.Gadgets.Air.Qm31Ops.coord_packM31,
      S31.Gadgets.Packed.coord, S31.Field.toZMod_reduce] using hcoord

/-- A folded `zero + 7` source step can reuse the broadcast-seven cell only
when its input is the AIR-owned zero cell and the complete nonzero
finalization chain owns the result. No step-output value equality is assumed. -/
theorem seven_fold_evidence {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (mulGates : List MulGate)
    (addresses : List Nat) (values : List (Lanes n))
    (id lhs : Nat) (path : SevenPath)
    (hleft : addresses[lhs]? = some 0)
    (hout : addresses[id]? = some path.broadcast7)
    (hleftValue : values[lhs]? = some (active hn (wire 0)))
    (hid : id = values.length)
    (hzero : (⟨.add, 0, 0, 0⟩ : Gate) ∈ gates)
    (hpublicU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hpath : path.owned gates mulGates)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    StepEvidence hn wire gates addresses values (.constant id lhs 7 false)
      (active hn (wire path.broadcast7)) := by
  refine .constantValue values id lhs 7 false 0 path.broadcast7
    (by decide) hleft hout hleftValue ?_ hid
  have hzeroValue := zero_anchor_air_sound hn wire gates hzero hair
  have hsevenValue := seven_path_quad_sound wire gates mulGates path
    hpublicU hpath hair hmul
  funext i
  have hz : active hn (wire 0) i = 0 := congrFun hzeroValue i
  have hs : active hn (wire path.broadcast7) i =
      RiscvRefinement.M31.reduce 7 := by
    simpa [active] using congrFun (congrArg (active hn) hsevenValue) i
  simp [hz, hs]

structure MulProjection where
  gates : List MulGate
  outputs : List Nat

private def parseMulGate (count : Nat) (json : Json) : Parse MulGate := do
  fields json ["in0", "in1", "out"]
  let in0 ← nat (← field json "in0")
  let in1 ← nat (← field json "in1")
  let out ← nat (← field json "out")
  if in0 ≥ count || in1 ≥ count || out ≥ count then
    throw "native QM31 multiply address is out of range"
  return ⟨in0, in1, out⟩

/-- The full structural decoder checks the graph schema and direct gates;
this decoder projects the same JSON bytes' QM31 multiply and public output
rosters needed by the fixed-constant path. -/
def decodeMulProjection (bytes : String) : Parse MulProjection := do
  if bytes.utf8ByteSize > 8 * 1024 * 1024 then
    throw "native structural graph exceeds 8 MiB"
  let json ← Json.parse bytes
  let count ← nat (← field json "n_vars")
  if count == 0 || count > 262144 then
    throw "native variable count exceeds bounded profile"
  let gates ← array (parseMulGate count) (← field json "mul")
  let outputs ← array nat (← field json "output")
  if gates.length > 262144 || outputs.any (· ≥ count) then
    throw "native QM31 multiply/output roster exceeds bounded profile"
  return ⟨gates, outputs⟩

private def sevenPathFields : List String :=
  ["base2", "base3", "base4", "base5", "base6", "base7", "uSquare",
   "i", "iPlusOne", "uPlusIu", "ones", "broadcast7"]

def decodeSevenPath (bytes : String) : Parse SevenPath := do
  if bytes.utf8ByteSize > 4096 then
    throw "fixed-constant path exceeds 4096 bytes"
  let json ← Json.parse bytes
  fields json sevenPathFields
  return {
    base2 := ← nat (← field json "base2")
    base3 := ← nat (← field json "base3")
    base4 := ← nat (← field json "base4")
    base5 := ← nat (← field json "base5")
    base6 := ← nat (← field json "base6")
    base7 := ← nat (← field json "base7")
    uSquare := ← nat (← field json "uSquare")
    i := ← nat (← field json "i")
    iPlusOne := ← nat (← field json "iPlusOne")
    uPlusIu := ← nat (← field json "uPlusIu")
    ones := ← nat (← field json "ones")
    broadcast7 := ← nat (← field json "broadcast7")
  }

/-- A public-output roster entry and exact `u` word are required locally.
Their authentication to the accepted proof is a separate premise. -/
def checkPublicU (wire : Nat → StructuralNativeGateCertificate.Quad)
    (outputs : List Nat) : Bool :=
  decide (outputs.head? = some 2) &&
    decide (S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)

def checkSevenFoldStep {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (mulGates : List MulGate) (outputs : List Nat)
    (addresses : List Nat) (values : List (Lanes n))
    (path : SevenPath) (step : EffectStep) : Option (Lanes n) :=
  match step with
  | .constant id lhs 7 false =>
      if id = values.length ∧ addresses[lhs]? = some 0 ∧
          values[lhs]? = some (active hn (wire 0)) ∧
          addresses[id]? = some path.broadcast7 ∧
          (⟨.add, 0, 0, 0⟩ : Gate) ∈ gates ∧
          path.checkOwned gates mulGates = true ∧
          checkPublicU wire outputs = true then
        some (active hn (wire path.broadcast7))
      else none
  | _ => none

theorem checkSevenFoldStep_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (mulGates : List MulGate) (outputs : List Nat)
    (addresses : List Nat) (values : List (Lanes n))
    (path : SevenPath) (step : EffectStep) (output : Lanes n)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates)
    (hstep : checkSevenFoldStep hn wire gates mulGates outputs addresses
      values path step = some output) :
    StepEvidence hn wire gates addresses values step output := by
  cases step with
  | binary id lhs rhs op => simp [checkSevenFoldStep] at hstep
  | constant id lhs value multiply =>
      by_cases hv : value = 7
      · by_cases hm : multiply = false
        · subst value
          subst multiply
          simp only [checkSevenFoldStep] at hstep
          split_ifs at hstep with hvalid
          · rcases hvalid with
              ⟨hid, hleft, hleftValue, hout, hzero, hpath, hpublic⟩
            have houtput := Option.some.inj hstep
            subst output
            have hU : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) =
                ⟨0, 0, 1, 0⟩ := by
              simp only [checkPublicU, Bool.and_eq_true,
                decide_eq_true_eq] at hpublic
              exact hpublic.2
            exact seven_fold_evidence hn wire gates mulGates addresses values
              id lhs path hleft hout hleftValue hid hzero hU
              (path.checkOwned_sound gates mulGates hpath) hair hmul
        · cases multiply <;> simp_all [checkSevenFoldStep]
      · cases value <;> simp_all [checkSevenFoldStep]

/-- Preserve the previously proved binary, identity, and zero cases; use
the fixed-chain certificate only for an otherwise excluded seven fold. -/
def checkOwnedStepSeven {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (projection : MulProjection)
    (addresses : List Nat) (values : List (Lanes n))
    (path : SevenPath) (step : EffectStep) : Option (Lanes n) :=
  match checkOwnedStep hn wire gates addresses values step with
  | some output => some output
  | none => checkSevenFoldStep hn wire gates projection.gates
      projection.outputs addresses values path step

theorem checkOwnedStepSeven_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (projection : MulProjection)
    (addresses : List Nat) (values : List (Lanes n))
    (path : SevenPath) (step : EffectStep) (output : Lanes n)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire projection.gates)
    (hstep : checkOwnedStepSeven hn wire gates projection addresses
      values path step = some output) :
    StepEvidence hn wire gates addresses values step output := by
  unfold checkOwnedStepSeven at hstep
  cases hbase : checkOwnedStep hn wire gates addresses values step with
  | some base =>
      simp only [hbase, Option.some.injEq] at hstep
      subst output
      exact checkOwnedStep_air_sound hn wire gates addresses values step
        base hair hbase
  | none =>
      simp only [hbase] at hstep
      exact checkSevenFoldStep_air_sound hn wire gates projection.gates
        projection.outputs addresses values path step output hair hmul hstep

def checkOwnedStepsSeven {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (projection : MulProjection)
    (addresses : List Nat) (path : SevenPath) :
    List (Lanes n) → List EffectStep → Option (List (Lanes n))
  | values, [] => some values
  | values, step :: rest => do
      let output ← checkOwnedStepSeven hn wire gates projection addresses
        values path step
      checkOwnedStepsSeven hn wire gates projection addresses path
        (values ++ [output]) rest

theorem checkOwnedStepsSeven_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → StructuralNativeGateCertificate.Quad)
    (gates : List Gate) (projection : MulProjection)
    (addresses : List Nat) (path : SevenPath)
    (initial final : List (Lanes n)) (steps : List EffectStep)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire projection.gates)
    (hsteps : checkOwnedStepsSeven hn wire gates projection addresses path
      initial steps = some final) :
    NativeTrace hn wire gates addresses initial steps final := by
  induction steps generalizing initial with
  | nil =>
      simp only [checkOwnedStepsSeven, Option.some.injEq] at hsteps
      subst final
      exact .done initial
  | cons step rest ih =>
      simp only [checkOwnedStepsSeven] at hsteps
      cases hstep : checkOwnedStepSeven hn wire gates projection addresses
          initial path step with
      | none => simp [hstep] at hsteps
      | some output =>
          simp [hstep] at hsteps
          exact .next
            (checkOwnedStepSeven_air_sound hn wire gates projection
              addresses initial path step output hair hmul hstep)
            (ih (initial ++ [output]) hsteps)

/-- Arbitrary admitted source step lists compose after both projections of
the same exported graph bytes are checked. The compiled gate roster, public
`u` output cell, and AIR rows are still supplied proof premises. -/
theorem checked_fixed_seven_source_air_sound {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes pathBytes : String)
    (ssa : EmittedSSA) (meaning : Source) (certificate : Certificate)
    (graph : ExportedGraph) (projection : MulProjection) (path : SevenPath)
    (inputs : Nat → Lanes n) (claimed : Lanes n)
    (final : List (Lanes n))
    (hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hgraph : decodeExportedGraph graphBytes = .ok graph)
    (hprojection : decodeMulProjection graphBytes = .ok projection)
    (hpath : decodeSevenPath pathBytes = .ok path)
    (hnames : graph.sourceNames = ssa.names)
    (hlanes : ssa.lane_count = n)
    (hports : checkInputPorts hn graph.wire graph.addresses
      certificate.inputs inputs = true)
    (howned : checkOwnedStepsSeven hn graph.wire graph.gates projection
      graph.addresses path
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      certificate.steps = some final)
    (houtput : checkOutputPort hn graph.wire graph.addresses final
      certificate.output claimed = true)
    (hassert : checkAssertions final certificate.assertions = true)
    (hair : NativeAirRows graph.wire graph.gates)
    (hmul : NativeMulAirRows graph.wire projection.gates) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes inputs claimed ∧
      decodeExportedGraph graphBytes = .ok graph ∧
      decodeMulProjection graphBytes = .ok projection ∧
      decodeSevenPath pathBytes = .ok path ∧
      graph.sourceNames = ssa.names := by
  refine ⟨?_, hgraph, hprojection, hpath, hnames⟩
  obtain ⟨hparse, _, hmeaning, hssa⟩ :=
    GeneralLinearSSAEffectsSourceBytes.checked_source_parts sourceBytes
      certificateBytes ssa meaning certificate hsource
  refine ⟨ssa, meaning, hparse, hmeaning, ?_⟩
  exact checked_native_trace_sound hn ssa meaning certificate inputs claimed
    final graph.wire graph.gates graph.addresses hssa hlanes hports
    (checkOwnedStepsSeven_air_sound hn graph.wire graph.gates projection
      graph.addresses path
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      final certificate.steps hair hmul howned) houtput hassert

end S31.Functional.Correspondence.StructuralNativeFixedConstant
