import S31.Gadgets.Functional.SSACertificate

/-!
An executable byte parser for the deliberately small direct-gate source
fragment. It accepts ASCII identifiers, ASCII whitespace, line comments,
one public four-lane M31 input and output, and one to sixteen canonical
binary `let` operations. It rejects unknown tokens, duplicate names,
forward reads, reversed commutative operands, and repeated operations.

The source denotation below is defined by this parser, so the theorem is
about actual input bytes rather than a separately supplied Lean source term.
The production Python and Zig parsers, native AIR emission, lookup argument,
and PCS remain separate correspondence obligations.
-/

namespace S31.Functional.SSATextBytes

open S31.Functional.SSACertificate

abbrev Token := List Nat

def token (s : String) : Token := s.toList.map Char.toNat

def isSpace (b : Nat) : Bool :=
  b == 9 || b == 10 || b == 11 || b == 12 || b == 13 || b == 32

def isLetter (b : Nat) : Bool :=
  decide (65 ≤ b ∧ b ≤ 90) || decide (97 ≤ b ∧ b ≤ 122)

def isDigit (b : Nat) : Bool := decide (48 ≤ b ∧ b ≤ 57)

def isNameStart (b : Nat) : Bool := isLetter b || b == 95
def isNameTail (b : Nat) : Bool := isNameStart b || isDigit b

def isName : Token → Bool
  | [] => false
  | first :: rest =>
      isNameStart first && rest.all isNameTail &&
        !(List.contains ([token "circuit", token "public", token "let", token "m31"])
          (first :: rest))

def span (predicate : Nat → Bool) : List Nat → Token × List Nat
  | [] => ([], [])
  | head :: tail =>
      if predicate head then
        let (accepted, remainder) := span predicate tail
        (head :: accepted, remainder)
      else ([], head :: tail)

/-- Fuel is bounded by the source byte count. Every recursive call consumes at
least one byte; the lexer never interprets non-ASCII bytes outside comments. -/
def lexFuel : Nat → List Nat → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, head :: tail =>
      if isSpace head then lexFuel fuel tail
      else if head == 47 then
        match tail with
        | 47 :: afterSlashes =>
            let (_, afterComment) := span (fun b => b != 10) afterSlashes
            lexFuel fuel afterComment
        | _ => none
      else if isNameStart head then do
        let (suffix, rest) := span isNameTail tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if isDigit head then do
        let (suffix, rest) := span isDigit tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if head == 45 then
        match tail with
        | 62 :: rest => do return [45, 62] :: (← lexFuel fuel rest)
        | _ => none
      else if head == 46 then
        match tail with
        | 42 :: rest => do return [46, 42] :: (← lexFuel fuel rest)
        | _ => none
      else if List.contains [40, 41, 91, 93, 59, 58, 123, 125, 61, 43] head then
        do return [head] :: (← lexFuel fuel tail)
      else none

def lex (bytes : List Nat) : Option (List Token) :=
  lexFuel (bytes.length + 1) bytes

def expect (wanted : Token) : List Token → Option (List Token)
  | found :: rest => if found == wanted then some rest else none
  | [] => none

def expectMany : List Token → List Token → Option (List Token)
  | [], remaining => some remaining
  | wanted :: more, remaining => do
      let rest ← expect wanted remaining
      expectMany more rest

def takeName : List Token → Option (Token × List Token)
  | name :: rest => if isName name then some (name, rest) else none
  | [] => none

def findName (wanted : Token) (names : List Token) : Option Nat :=
  go 0 names
where
  go (index : Nat) : List Token → Option Nat
    | [] => none
    | name :: rest => if name == wanted then some index else go (index + 1) rest

structure State where
  remaining : List Token
  names : List Token
  expressions : List (Bool × Nat × Nat)
  instructions : List Instruction

def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← takeName rest
  if state.names.contains name then none else
  let rest ← expect (token "=") rest
  let (left, rest) ← takeName rest
  let (multiply, rest) ← match rest with
    | operation :: tail =>
        if operation == token "+" then some (false, tail)
        else if operation == token ".*" then some (true, tail)
        else none
    | [] => none
  let (right, rest) ← takeName rest
  let rest ← expect (token ";") rest
  let lhs ← findName left state.names
  let rhs ← findName right state.names
  if lhs > rhs then none else
  let expression := (multiply, lhs, rhs)
  if state.expressions.contains expression then none else
  let instruction : Instruction :=
    { id := state.names.length, lhs, rhs, multiply }
  return {
    remaining := rest,
    names := state.names ++ [name],
    expressions := state.expressions ++ [expression],
    instructions := state.instructions ++ [instruction] }

def parseLetsFuel : Nat → State → Option State
  | 0, state =>
      if state.remaining.head? == some (token "let") then none else some state
  | fuel + 1, state =>
      if state.remaining.head? == some (token "let") then do
        let next ← parseLet state
        parseLetsFuel fuel next
      else some state

def termFor (certificate : Certificate) : Option Term := do
  let terms ← certificate.instructions.foldlM checkStep [.input]
  terms[certificate.output]?

/-- A successful parse carries a kernel-checkable proof that its SSA trace
reconstructs the term used as the source denotation. -/
structure Parsed where
  circuitName : Token
  inputName : Token
  outputName : Token
  wireNames : List Token
  certificate : Certificate
  meaning : Term
  checked : termFor certificate = some meaning

def parseBytes (bytes : List Nat) : Option Parsed := do
  if bytes.length > 16384 then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "circuit") tokens
  let (circuitName, rest) ← takeName rest
  let rest ← expectMany [token "(", token "public"] rest
  let (inputName, rest) ← takeName rest
  let rest ← expectMany [token ":", token "[", token "m31", token ";",
                          token "4", token "]", token ")", token "->",
                          token "public", token "[", token "m31", token ";",
                          token "4", token "]", token "{"] rest
  let state ← parseLetsFuel 16 {
    remaining := rest, names := [inputName], expressions := [], instructions := [] }
  if state.instructions.isEmpty then none else
  let (outputName, rest) ← takeName state.remaining
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let output ← findName outputName state.names
  if output == 0 then none else
  let certificate : Certificate := { instructions := state.instructions, output }
  match h : termFor certificate with
  | none => none
  | some meaning => some {
      circuitName, inputName, outputName, wireNames := state.names,
      certificate, meaning, checked := h }

def denotation (bytes : List Nat) (input : Lanes) : Option Lanes :=
  (parseBytes bytes).map (fun parsed => parsed.meaning.eval input)

/-- The certificate evaluator agrees with its reconstructed source term for
every input, including all shared `let` references. -/
theorem termFor_sound (certificate : Certificate) (meaning : Term)
    (input : Lanes) (h : termFor certificate = some meaning) :
    executeNormalized certificate input = some (meaning.eval input) := by
  rw [execute_normalized_eq_execute]
  unfold termFor at h
  cases hterms : certificate.instructions.foldlM checkStep [.input] with
  | none => simp [hterms] at h
  | some terms =>
      cases hout : terms[certificate.output]? with
      | none => simp [hterms, hout] at h
      | some term =>
          have hterm : term = meaning := by simpa [hterms, hout] using h
          have hrun : certificate.instructions.foldlM executeStep [input] =
              some (terms.map (Term.eval input)) := by
            simpa [hterms] using
              execute_folds_correct certificate.instructions [Term.input] input
          simp [execute, hrun, List.getElem?_map, hout, hterm]

/-- Successful parsing of actual bytes determines a normalized certificate
whose execution has exactly the byte language's defined four-lane meaning. -/
theorem parsed_bytes_normalized_sound (bytes : List Nat) (input : Lanes)
    (parsed : Parsed) (hparse : parseBytes bytes = some parsed) :
    executeNormalized parsed.certificate input = denotation bytes input := by
  rw [termFor_sound parsed.certificate parsed.meaning input parsed.checked]
  simp [denotation, hparse]

/-- A projection of the successful byte parse onto a concrete certificate is
enough to bind that certificate's executable semantics to the bytes. The
proof does not assume a separately generated Lean source term. -/
theorem parsed_certificate_sound (bytes : List Nat) (input : Lanes)
    (certificate : Certificate)
    (hcertificate : (parseBytes bytes).map Parsed.certificate =
      some certificate) :
    executeNormalized certificate input = denotation bytes input := by
  cases hparse : parseBytes bytes with
  | none => simp [hparse] at hcertificate
  | some parsed =>
      have hsame : parsed.certificate = certificate := by
        simpa [hparse] using hcertificate
      subst certificate
      exact parsed_bytes_normalized_sound bytes input parsed hparse

end S31.Functional.SSATextBytes
