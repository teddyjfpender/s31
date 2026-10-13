import S31.Gadgets.Functional.CompilerCorrespondence

/-!
A typed four-lane model of `release_nested4/functional.s31`. A factory
captures `x*x` and returns a function; `identity` receives that function,
while a second helper computes `x+x` as the returned function's argument.
Both nested applications specialize before relation construction.

The theorem below connects this source model to the executable normalized
arithmetic-node semantics and the packed QM31 operation-row equations. The
Python source parser, native column emitter, lookup argument and PCS/FRI
verifier remain separate obligations.
-/

namespace S31.Functional.NestedApplications

open S31.Functional
open S31.Functional.CompilerCorrespondence
open Graph

def factory : Expr [.array 4]
    (.arrow (.array 4) (.arrow (.array 4) (.array 4))) :=
  .lambda
    (.letValue
      (.arrayMul (.var .here) (.var .here))
      (.lambda (.arrayAdd (.var (.there .here)) (.var .here))))

def identity : Expr [.array 4]
    (.arrow (.arrow (.array 4) (.array 4))
      (.arrow (.array 4) (.array 4))) :=
  .lambda (.var .here)

def double : Expr [.array 4] (.arrow (.array 4) (.array 4)) :=
  .lambda (.arrayAdd (.var .here) (.var .here))

def nested : Expr [.array 4] (.array 4) :=
  .apply
    (.apply identity (.apply factory (.var .here)))
    (.apply double (.var .here))

def direct : Expr [.array 4] (.array 4) :=
  .arrayAdd
    (.arrayMul (.var .here) (.var .here))
    (.arrayAdd (.var .here) (.var .here))

/-- The factory, higher-order argument and both applications add no residual
arithmetic operation for any symbolic four-lane input. -/
theorem nested_zero_cost {n : Nat} (x : Fin 4 → Poly n) :
    specialize nested (.cons x .nil) =
      specialize direct (.cons x .nil) := rfl

theorem nested_same_graph : arrayCode nested = arrayCode direct := by
  exact congrArg (fun outputs => PolyList.code (List.ofFn outputs))
    (nested_zero_cost (fun i => Poly.input i))

def arithmetic : Arithmetic4 :=
  .add (.mul .input .input) (.add .input .input)

theorem direct_is_arithmetic : direct = directSource arithmetic := rfl

/-- Every satisfying packed row witness agrees with the typed source result,
and honest row witnesses exist. The equivalence also accounts for the strict
graph of residual arithmetic nodes. -/
theorem nested_graph_iff_air (inputs : List M31)
    (claimed : Fin 4 → M31) (hinputs : inputs.length = 4) :
    (arrayCode nested).strictAccepts Graph.fieldArity
      S31.Gadgets.Hash.fieldPrimitive inputs (List.ofFn claimed) ↔
    AirAccepts (fun i => inputs.getD i.val 0) arithmetic claimed := by
  rw [nested_same_graph, direct_is_arithmetic]
  rw [← bound_source_same_graph arithmetic]
  exact strict_graph_iff_air arithmetic inputs claimed hinputs

theorem nested_air_output (input claimed : Fin 4 → M31) :
    AirAccepts input arithmetic claimed ↔
      claimed = fun i => input i * input i + (input i + input i) := by
  rw [← normalized_iff_air, normalized_iff_source, bound_source_value]
  rfl

theorem nested_graph_output (inputs : List M31)
    (claimed : Fin 4 → M31) (hinputs : inputs.length = 4) :
    (arrayCode nested).strictAccepts Graph.fieldArity
      S31.Gadgets.Hash.fieldPrimitive inputs (List.ofFn claimed) ↔
    claimed = fun i =>
      inputs.getD i.val 0 * inputs.getD i.val 0 +
        (inputs.getD i.val 0 + inputs.getD i.val 0) := by
  exact (nested_graph_iff_air inputs claimed hinputs).trans
    (nested_air_output (fun i => inputs.getD i.val 0) claimed)

end S31.Functional.NestedApplications
