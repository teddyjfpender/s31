import S31.Gadgets.FunctionalOutputs

/-!
Homogeneous fixed-length field arrays in the total functional core. Array
values are shape-indexed source values; each residual lane is a field
polynomial. Lambda application and `let` therefore add no relation operation.
This models the typed array subset, not Python parsing or production AIR
emission.
-/

namespace S31.Functional
open Graph

def arrayInputSource {n : Nat} (inputs : Fin n → M31) :
    Env Meaning [.array n] := .cons inputs .nil

def arrayInputResidual {n : Nat} :
    Env (Residual n) [.array n] := .cons (fun i => .input i) .nil

theorem array_inputs_related {n : Nat} (inputs : Fin n → M31) :
    EnvRelated inputs (arrayInputSource inputs) (arrayInputResidual (n := n)) := by
  exact ⟨(fun _ => rfl), trivial⟩

theorem array_program_correct {n m : Nat}
    (e : Expr [.array n] (.array m)) (inputs : Fin n → M31) :
    ∀ i : Fin m, (specialize e (arrayInputResidual (n := n)) i).eval inputs =
      denote e (arrayInputSource inputs) i := by
  exact specialize_correct inputs e _ _ (array_inputs_related inputs)

def arrayCode {n m : Nat} (e : Expr [.array n] (.array m)) :
    Code M31 FieldOp :=
  PolyList.code (List.ofFn (specialize e (arrayInputResidual (n := n))))

theorem arrayCode_valid {n m : Nat} (e : Expr [.array n] (.array m)) :
    (arrayCode e).WellFormedFor fieldArity n := by
  exact PolyList.code_valid _

/-- Every satisfying gate witness binds every array output lane to the
denotation of its source expression. Honest witnesses exist by the converse. -/
theorem arrayCode_accepts {n m : Nat} (e : Expr [.array n] (.array m))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (arrayCode e).strictAccepts fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = List.ofFn (denote e
        (arrayInputSource (fun i => inputs.getD i.val 0))) := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp only [hinputs, arrayCode_valid, true_and]
  rw [show (arrayCode e).eval fieldEval inputs =
    List.map (Poly.eval (fun i => inputs.getD i.val 0))
      (List.ofFn (specialize e (arrayInputResidual (n := n)))) from
    PolyList.code_eval _ inputs hinputs]
  rw [List.map_ofFn]
  have hvalue :
      List.ofFn (Poly.eval (fun i => inputs.getD i.val 0) ∘
        specialize e (arrayInputResidual (n := n))) =
      List.ofFn (denote e
        (arrayInputSource (fun i => inputs.getD i.val 0))) := by
    apply List.ofFn_inj.mpr
    funext i
    exact array_program_correct e (fun i => inputs.getD i.val 0) i
  rw [hvalue]

/-- Source analogue: `let saved = x in let double = fun y => y + saved
    in double saved`, with four field lanes. -/
def capturedArrayDouble : Expr [.array 4] (.array 4) :=
  .letValue (.var .here)
    (.letValue
      (.lambda (.arrayAdd (.var .here) (.var (.there .here))))
      (.apply (.var .here) (.var (.there .here))))

theorem capturedArrayDouble_zero_cost {n : Nat} (x : Fin 4 → Poly n) :
    specialize capturedArrayDouble (.cons x .nil) =
      (fun i => .add (x i) (x i)) := rfl

def capturedArrayDoubleCode : Code M31 FieldOp := arrayCode capturedArrayDouble

theorem capturedArrayDoubleCode_shape :
    capturedArrayDoubleCode =
      ⟨[.apply .add [0, 0], .apply .add [1, 1],
        .apply .add [2, 2], .apply .add [3, 3]], [4, 5, 6, 7]⟩ := rfl

theorem capturedArrayDoubleCode_accepts (a b c d : M31) (output : List M31) :
    capturedArrayDoubleCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [a, b, c, d] output ↔
      output = [a + a, b + b, c + c, d + d] := by
  simpa [capturedArrayDoubleCode, capturedArrayDouble,
    arrayInputSource, denote, Env.get] using
    (arrayCode_accepts capturedArrayDouble [a, b, c, d] output rfl)

/-- The field-array preimage transformation used before the production
functional Poseidon2 example: take the last two lanes, append the first two,
then add seven to every lane. The hash itself is outside this source core. -/
def rotateAndSalt : Expr [.array 4] (.array 4) :=
  .arrayAdd
    (.arrayConcat
      (.arrayDrop 2 (by decide) (.var .here))
      (.arrayTake 2 (by decide) (.var .here)))
    (.arraySplat (.literal (RiscvRefinement.M31.reduce 7)))

theorem rotateAndSaltCode_accepts (a b c d : M31) (output : List M31) :
    (arrayCode rotateAndSalt).strictAccepts Graph.fieldArity
      Gadgets.Hash.fieldPrimitive [a, b, c, d] output ↔
      output = [c + RiscvRefinement.M31.reduce 7,
        d + RiscvRefinement.M31.reduce 7,
        a + RiscvRefinement.M31.reduce 7,
        b + RiscvRefinement.M31.reduce 7] := by
  simpa [rotateAndSalt, arrayInputSource, denote, Env.get,
    arrayTakeFn, arrayDropFn, Fin.append] using
    (arrayCode_accepts rotateAndSalt [a, b, c, d] output rfl)

end S31.Functional
