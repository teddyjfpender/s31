import S31.Semantics.Field

/-!
A typed, total core of S31's static functional stage. Function values exist
only during specialization; the residual language contains field expressions
and no function nodes. This model intentionally excludes partial library calls,
arrays, assertions and the Python parser.
-/

namespace S31.Functional

inductive Ty where
  | field
  | arrow (domain codomain : Ty)
deriving DecidableEq, Repr

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (u :: Γ) t

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ t → Expr Γ t
  | literal : M31 → Expr Γ .field
  | add : Expr Γ .field → Expr Γ .field → Expr Γ .field
  | mul : Expr Γ .field → Expr Γ .field → Expr Γ .field
  | letValue : Expr Γ a → Expr (a :: Γ) b → Expr Γ b
  | lambda : Expr (a :: Γ) b → Expr Γ (.arrow a b)
  | apply : Expr Γ (.arrow a b) → Expr Γ a → Expr Γ b

/-- The emitted field expression has no closure or function constructor. -/
inductive Poly (n : Nat) where
  | input : Fin n → Poly n
  | literal : M31 → Poly n
  | add : Poly n → Poly n → Poly n
  | mul : Poly n → Poly n → Poly n

def Poly.eval {n : Nat} (inputs : Fin n → M31) : Poly n → M31
  | .input i => inputs i
  | .literal x => x
  | .add a b => a.eval inputs + b.eval inputs
  | .mul a b => a.eval inputs * b.eval inputs

@[reducible] def Meaning : Ty → Type
  | .field => M31
  | .arrow a b => Meaning a → Meaning b

@[reducible] def Residual (n : Nat) : Ty → Type
  | .field => Poly n
  | .arrow a b => Residual n a → Residual n b

inductive Env (F : Ty → Type) : List Ty → Type where
  | nil : Env F []
  | cons : F t → Env F Γ → Env F (t :: Γ)

def Env.get {F : Ty → Type} : Env F Γ → Var Γ t → F t
  | .cons x _, .here => x
  | .cons _ xs, .there v => xs.get v

def denote : Expr Γ t → Env Meaning Γ → Meaning t
  | .var v, env => env.get v
  | .literal x, _ => x
  | .add a b, env => denote a env + denote b env
  | .mul a b, env => denote a env * denote b env
  | .letValue value body, env => denote body (.cons (denote value env) env)
  | .lambda body, env => fun value => denote body (.cons value env)
  | .apply fn arg, env => (denote fn env) (denote arg env)

/-- Static beta reduction and closure capture produce only a field polynomial. -/
def specialize {n : Nat} : Expr Γ t → Env (Residual n) Γ → Residual n t
  | .var v, env => env.get v
  | .literal x, _ => .literal x
  | .add a b, env => .add (specialize a env) (specialize b env)
  | .mul a b, env => .mul (specialize a env) (specialize b env)
  | .letValue value body, env => specialize body (.cons (specialize value env) env)
  | .lambda body, env => fun value => specialize body (.cons value env)
  | .apply fn arg, env => (specialize fn env) (specialize arg env)

/-- A source value and its specialized value agree at every related argument. -/
def Related {n : Nat} (inputs : Fin n → M31) :
    (t : Ty) → Meaning t → Residual n t → Prop
  | .field, value, poly => poly.eval inputs = value
  | .arrow a b, fn, closure =>
      ∀ value poly, Related inputs a value poly →
        Related inputs b (fn value) (closure poly)

def EnvRelated {n : Nat} (inputs : Fin n → M31) :
    {Γ : List Ty} → Env Meaning Γ → Env (Residual n) Γ → Prop
  | [], .nil, .nil => True
  | t :: _, .cons value rest, .cons poly residualRest =>
      Related inputs t value poly ∧ EnvRelated inputs rest residualRest

theorem Env.get_related {n : Nat} (inputs : Fin n → M31)
    (source : Env Meaning Γ) (residual : Env (Residual n) Γ)
    (h : EnvRelated inputs source residual) (v : Var Γ t) :
    Related inputs t (source.get v) (residual.get v) := by
  induction v with
  | here =>
      cases source with
      | cons value rest =>
          cases residual with
          | cons poly residualRest => exact h.1
  | there v ih =>
      cases source with
      | cons value rest =>
          cases residual with
          | cons poly residualRest => exact ih rest residualRest h.2

/-- Fundamental specialization theorem for all typed core expressions,
including free variables, lexical capture, function return and application. -/
theorem specialize_correct {n : Nat} (inputs : Fin n → M31)
    (e : Expr Γ t) (source : Env Meaning Γ) (residual : Env (Residual n) Γ)
    (h : EnvRelated inputs source residual) :
    Related inputs t (denote e source) (specialize e residual) := by
  induction e with
  | var v => exact Env.get_related inputs source residual h v
  | literal x => rfl
  | add a b iha ihb =>
      change (specialize a residual).eval inputs + (specialize b residual).eval inputs =
        denote a source + denote b source
      rw [iha source residual h, ihb source residual h]
  | mul a b iha ihb =>
      change (specialize a residual).eval inputs * (specialize b residual).eval inputs =
        denote a source * denote b source
      rw [iha source residual h, ihb source residual h]
  | letValue value body ihValue ihBody =>
      exact ihBody (.cons (denote value source) source)
        (.cons (specialize value residual) residual)
        ⟨ihValue source residual h, h⟩
  | lambda body ih =>
      intro value poly related
      exact ih (.cons value source) (.cons poly residual) ⟨related, h⟩
  | apply fn arg ihFn ihArg =>
      exact (ihFn source residual h) (denote arg source)
        (specialize arg residual) (ihArg source residual h)

/-- Inputs are related to the corresponding residual input wires. -/
def inputSource {n : Nat} (inputs : Fin n → M31) :
    (indices : List (Fin n)) → Env Meaning (indices.map fun _ => .field)
  | [] => .nil
  | i :: rest => .cons (inputs i) (inputSource inputs rest)

def inputResidual {n : Nat} :
    (indices : List (Fin n)) → Env (Residual n) (indices.map fun _ => .field)
  | [] => .nil
  | i :: rest => .cons (.input i) (inputResidual rest)

theorem inputs_related {n : Nat} (inputs : Fin n → M31)
    (indices : List (Fin n)) :
    EnvRelated inputs (inputSource inputs indices) (inputResidual indices) := by
  induction indices with
  | nil => trivial
  | cons i rest ih => exact ⟨rfl, ih⟩

/-- Every typed field program specializes to an equal field polynomial on
every assignment of its declared inputs. -/
theorem program_correct {n : Nat} (indices : List (Fin n))
    (e : Expr (indices.map fun _ => .field) .field)
    (inputs : Fin n → M31) :
    (specialize e (inputResidual indices)).eval inputs =
      denote e (inputSource inputs indices) := by
  exact specialize_correct inputs e _ _ (inputs_related inputs indices)

/-- An explicit local constraint relation for the residual arithmetic tree.
Every intermediate value is quantified by the inductive constructors. -/
inductive Poly.Accepts {n : Nat} (inputs : Fin n → M31) : Poly n → M31 → Prop where
  | input (i : Fin n) : Accepts inputs (.input i) (inputs i)
  | literal (x : M31) : Accepts inputs (.literal x) x
  | add {a b : Poly n} {x y z : M31} :
      Accepts inputs a x → Accepts inputs b y → z - (x + y) = 0 →
      Accepts inputs (.add a b) z
  | mul {a b : Poly n} {x y z : M31} :
      Accepts inputs a x → Accepts inputs b y → z - (x * y) = 0 →
      Accepts inputs (.mul a b) z

/-- Arbitrary satisfying intermediate witnesses have the computed value;
honest values satisfy the same local equations. -/
theorem Poly.accepts_sound_complete {n : Nat} (inputs : Fin n → M31)
    (poly : Poly n) (output : M31) :
    Accepts inputs poly output ↔ output = poly.eval inputs := by
  induction poly generalizing output with
  | input i =>
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; exact .input i
  | literal x =>
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; exact .literal x
  | add a b iha ihb =>
      constructor
      · intro h
        cases h with
        | add ha hb equation =>
            change output = a.eval inputs + b.eval inputs
            rw [← (iha _).mp ha, ← (ihb _).mp hb]
            exact (RiscvRefinement.M31.sub_eq_zero_iff _ _).mp equation
      · intro h
        subst output
        exact .add ((iha _).mpr rfl) ((ihb _).mpr rfl)
          ((RiscvRefinement.M31.sub_eq_zero_iff _ _).mpr rfl)
  | mul a b iha ihb =>
      constructor
      · intro h
        cases h with
        | mul ha hb equation =>
            change output = a.eval inputs * b.eval inputs
            rw [← (iha _).mp ha, ← (ihb _).mp hb]
            exact (RiscvRefinement.M31.sub_eq_zero_iff _ _).mp equation
      · intro h
        subst output
        exact .mul ((iha _).mpr rfl) ((ihb _).mpr rfl)
          ((RiscvRefinement.M31.sub_eq_zero_iff _ _).mpr rfl)

/-- A typed functional field program and its specialized local constraints
accept exactly the same output for every assignment. -/
theorem program_accepts_iff {n : Nat} (indices : List (Fin n))
    (e : Expr (indices.map fun _ => .field) .field)
    (inputs : Fin n → M31) (output : M31) :
    Poly.Accepts inputs (specialize e (inputResidual indices)) output ↔
      output = denote e (inputSource inputs indices) := by
  rw [Poly.accepts_sound_complete, program_correct]

/-- Applying a static lambda contributes no residual operation beyond its
body with the argument bound. -/
theorem specialize_beta {n : Nat} (body : Expr (a :: Γ) b)
    (arg : Expr Γ a) (env : Env (Residual n) Γ) :
    specialize (.apply (.lambda body) arg) env =
      specialize (.letValue arg body) env := rfl

/-- In source notation: `let saved = x in
      let f = fun(y : m31) -> m31 => y * y + saved in f(saved)`. -/
def capturedSquare : Expr [.field] .field :=
  .letValue (.var .here)
    (.letValue
      (.lambda (.add (.mul (.var .here) (.var .here))
        (.var (.there .here))))
      (.apply (.var .here) (.var (.there .here))))

theorem capturedSquare_zero_cost {n : Nat} (x : Poly n) :
    specialize capturedSquare (.cons x .nil) = .add (.mul x x) x := rfl

theorem capturedSquare_accepts (x output : M31) :
    Poly.Accepts (fun _ : Fin 1 => x)
      (specialize capturedSquare (inputResidual [0])) output ↔
      output = x * x + x := by
  simpa [capturedSquare, inputSource, inputResidual, denote] using
    (program_accepts_iff [0] capturedSquare (fun _ : Fin 1 => x) output)

end S31.Functional
