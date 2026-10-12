import S31.Gadgets.Functional.Correspondence.CanonicalDagOptimization
import S31.Gadgets.Functional.SSAAliasTextBytes
import S31.Gadgets.Functional.SSANormalizedBytes
import S31.Gadgets.Functional.SSACanonicalIrBytes

/-!
Actual source-byte admission for the direct four-lane add/mul fragment with
zero-cost aliases, commutative operand reversal, and repeated expressions. The
existing `SSATextBytes` parser intentionally rejects reversed and repeated
expressions, so this parser keeps its
own arithmetic-let state while reusing the reviewed bounded lexer and token
grammar. It checks exact normalized JSON and compact canonical IR bytes and
then applies the checked optimizer semantics theorem.

The byte grammar here has one public input/output, 1..16 arithmetic lets,
and bounded alias lets. It does not admit constants, assertions, private inputs,
nested arithmetic expressions, or non-add/mul operations. Native Zig serializer and
SHA-256 correspondence remain separate obligations.
-/

namespace S31.Functional.Correspondence.OptimizedTextBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.Correspondence.CanonicalDagOptimization

structure ParseState where
  remaining : List Token
  /-- Producer names only; aliases do not occupy SSA node IDs. -/
  names : List Token
  /-- Every lexical binding, including aliases, resolves to a producer ID. -/
  bindings : List (Token × Nat)
  instructions : List Instruction

def parseLet (state : ParseState) : Option ParseState := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← SSAAliasTextBytes.takeAliasName rest
  if (SSAAliasTextBytes.findBinding name state.bindings).isSome then none else
  let rest ← expect (token "=") rest
  let (rhsTokens, rest) ← SSAAliasTextBytes.takeUntil (token ";") rest
  let rhs ← SSAAliasTextBytes.parseRhs rhsTokens
  match rhs with
  | .alias referenced =>
      let id ← SSAAliasTextBytes.findBinding referenced state.bindings
      return { state with
        remaining := rest,
        bindings := state.bindings ++ [(name, id)] }
  | .arithmetic multiply left right =>
      let lhs ← SSAAliasTextBytes.findBinding left state.bindings
      let rhs ← SSAAliasTextBytes.findBinding right state.bindings
      if state.instructions.length >= 16 || name.length > 128 then none else
      let id := state.names.length
      let instruction : Instruction := { id, lhs, rhs, multiply }
      return {
        remaining := rest,
        names := state.names ++ [name],
        bindings := state.bindings ++ [(name, id)],
        instructions := state.instructions ++ [instruction] }

def parseLetsFuel : Nat → ParseState → Option ParseState
  | 0, state =>
      if state.remaining.head? == some (token "let") then none else some state
  | fuel + 1, state =>
      if state.remaining.head? == some (token "let") then do
        let next ← parseLet state
        parseLetsFuel fuel next
      else some state

structure Parsed where
  circuitName : Token
  inputName : Token
  outputName : Token
  wireNames : List Token
  raw : Certificate
  compact : Certificate
  meaning : Term
  checkedRaw : termFor raw = some meaning
  checkedOptimization : optimizeChecked raw = some compact

def parseBytes (bytes : Token) : Option Parsed := do
  if bytes.length > 16384 then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "circuit") tokens
  let (circuitName, rest) ← SSAAliasTextBytes.takeAliasName rest
  if SSAAliasTextBytes.isPlainBuiltinCircuitName circuitName then none else
  let rest ← expectMany [token "(", token "public"] rest
  let (inputName, rest) ← SSAAliasTextBytes.takeAliasName rest
  if inputName.length > 128 then none else
  let rest ← expectMany [token ":", token "[", token "m31", token ";",
                          token "4", token "]", token ")", token "->",
                          token "public", token "[", token "m31", token ";",
                          token "4", token "]", token "{"] rest
  let state ← parseLetsFuel 256 {
    remaining := rest, names := [inputName],
    bindings := [(inputName, 0)], instructions := [] }
  if state.instructions.isEmpty then none else
  let (outputTokens, rest) ← SSAAliasTextBytes.takeUntil (token "}") state.remaining
  if !rest.isEmpty then none else
  let sourceOutput ← SSAAliasTextBytes.outputReference outputTokens
  let output ← SSAAliasTextBytes.findBinding sourceOutput state.bindings
  if output == 0 then none else
  let outputName ← state.names[output]?
  let raw : Certificate := { instructions := state.instructions, output }
  match hraw : termFor raw with
  | none => none
  | some meaning =>
      match hopt : optimizeChecked raw with
      | none => none
      | some compact => some {
          circuitName, inputName, outputName, wireNames := state.names,
          raw, compact, meaning,
          checkedRaw := hraw, checkedOptimization := hopt }

def denotation (bytes : Token) (input : Lanes) : Option Lanes :=
  (parseBytes bytes).map (fun parsed => parsed.meaning.eval input)

theorem parsed_bytes_sound (bytes : Token) (parsed : Parsed)
    (input : Lanes) (hparse : parseBytes bytes = some parsed) :
    executeNormalized parsed.compact input = denotation bytes input := by
  have hoptimizer := optimizeChecked_semantics parsed.raw parsed.compact
    input parsed.checkedOptimization
  have hraw := termFor_sound parsed.raw parsed.meaning input parsed.checkedRaw
  rw [hoptimizer] at hraw
  simpa [denotation, hparse] using hraw

/-- Exact pretty JSON relation bytes for this checked source grammar. -/
def encodeNormalized (parsed : Parsed) : Option Token := do
  let nodes ← parsed.raw.instructions.mapM
    (S31.Functional.SSANormalizedBytes.encodeNode parsed.wireNames)
  return token "{\n  \"assertions\": [],\n  \"inputs\": [\n    {\n      \"kind\": \"m31\",\n      \"length\": 4,\n      \"name\": \"" ++
    parsed.inputName ++
    token "\",\n      \"visibility\": \"public\"\n    }\n  ],\n  \"name\": \"" ++
    parsed.circuitName ++
    token "\",\n  \"nodes\": [\n" ++
    S31.Functional.SSANormalizedBytes.joinNodes nodes ++
    token "\n  ],\n  \"public_outputs\": [\n    \"" ++
    parsed.outputName ++
    token "\"\n  ],\n  \"version\": 1\n}\n"

/-- Exact legacy compact canonical IR bytes for the optimized DAG. -/
def encodeCanonical (parsed : Parsed) : Token :=
  token "{\"version\":1,\"nodes\":[" ++
  S31.Functional.SSACanonicalIrBytes.inputNode parsed.inputName ++
  token "," ++ S31.Functional.SSACanonicalIrBytes.joinNodes
    (parsed.compact.instructions.map
      S31.Functional.SSACanonicalIrBytes.instructionNode) ++
  token "],\"assertions\":[],\"public_outputs\":[{\"name\":\"" ++
  parsed.outputName ++ token "\",\"id\":" ++
  token (toString parsed.compact.output) ++ token "}]}"

/-- The three exact byte streams must identify the same accepted source and
optimized positional DAG. -/
def checkBytes (sourceBytes normalizedBytes canonicalBytes : Token) :
    Option Certificate := do
  let parsed ← parseBytes sourceBytes
  let expected ← encodeNormalized parsed
  if expected != normalizedBytes then none else
  if encodeCanonical parsed != canonicalBytes then none else
  some parsed.compact

theorem checked_bytes_sound
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (input : Lanes)
    (hcheck : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact) :
    ∃ parsed, parseBytes sourceBytes = some parsed ∧
      encodeNormalized parsed = some normalizedBytes ∧
      encodeCanonical parsed = canonicalBytes ∧
      compact = parsed.compact ∧
      executeNormalized compact input = denotation sourceBytes input := by
  unfold checkBytes at hcheck
  cases hparse : parseBytes sourceBytes with
  | none => simp [hparse] at hcheck
  | some parsed =>
      cases hnormalized : encodeNormalized parsed with
      | none => simp [hparse, hnormalized] at hcheck
      | some expected =>
          by_cases hnorm : expected = normalizedBytes
          · by_cases hcanon : encodeCanonical parsed = canonicalBytes
            · have hcompact : parsed.compact = compact := by
                simpa [hparse, hnormalized, hnorm, hcanon] using hcheck
              subst compact
              exact ⟨parsed, rfl, by simpa [hnorm] using hnormalized,
                hcanon, rfl, parsed_bytes_sound sourceBytes parsed input hparse⟩
            · simp [hparse, hnormalized, hnorm, hcanon] at hcheck
          · simp [hparse, hnormalized, hnorm] at hcheck

/-- A real source spelling outside the older canonical-only byte grammar:
`d` reverses the operands of `c` and reuses its compact node. -/
def reversedAndRepeatedBytes : Token := token
  "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let b = x .* x; let c = a + b; let d = b + a; d }"

set_option maxRecDepth 8192 in
theorem reversed_and_repeated_source_compacts :
    (parseBytes reversedAndRepeatedBytes).map (·.compact) =
      some compactExample := by decide

set_option maxRecDepth 8192 in
theorem canonical_only_parser_rejects_reversed_source :
    S31.Functional.SSATextBytes.parseBytes reversedAndRepeatedBytes = none := by decide

/-- Captured normalized JSON bytes from the production Python text frontend
for `reversedAndRepeatedBytes`; every source operation remains present. -/
def reversedAndRepeatedNormalized : Token := token
  "{\n  \"assertions\": [],\n  \"inputs\": [\n    {\n      \"kind\": \"m31\",\n      \"length\": 4,\n      \"name\": \"x\",\n      \"visibility\": \"public\"\n    }\n  ],\n  \"name\": \"reverse_share\",\n  \"nodes\": [\n    {\n      \"lhs\": \"x\",\n      \"name\": \"a\",\n      \"op\": \"add\",\n      \"rhs\": \"x\"\n    },\n    {\n      \"lhs\": \"x\",\n      \"name\": \"b\",\n      \"op\": \"mul\",\n      \"rhs\": \"x\"\n    },\n    {\n      \"lhs\": \"a\",\n      \"name\": \"c\",\n      \"op\": \"add\",\n      \"rhs\": \"b\"\n    },\n    {\n      \"lhs\": \"b\",\n      \"name\": \"d\",\n      \"op\": \"add\",\n      \"rhs\": \"a\"\n    }\n  ],\n  \"public_outputs\": [\n    \"d\"\n  ],\n  \"version\": 1\n}\n"

/-- Expected compact legacy IR bytes: three arithmetic nodes, with the
source's output name `d` mapped to canonical node 3. -/
def reversedAndRepeatedCanonical : Token := token
  "{\"version\":1,\"nodes\":[{\"tag\":\"input\",\"kind\":\"m31\",\"length\":4,\"lhs\":null,\"rhs\":null,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":\"x\",\"visibility\":\"public\"},{\"tag\":\"add\",\"kind\":\"m31\",\"length\":4,\"lhs\":0,\"rhs\":0,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null},{\"tag\":\"mul\",\"kind\":\"m31\",\"length\":4,\"lhs\":0,\"rhs\":0,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null},{\"tag\":\"add\",\"kind\":\"m31\",\"length\":4,\"lhs\":1,\"rhs\":2,\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":null,\"visibility\":null}],\"assertions\":[],\"public_outputs\":[{\"name\":\"d\",\"id\":3}]}"

theorem pinned_reversed_and_repeated_semantics (input : Lanes) :
    executeNormalized compactExample input =
      denotation reversedAndRepeatedBytes input := by
  cases hparse : parseBytes reversedAndRepeatedBytes with
  | none =>
      have h := reversed_and_repeated_source_compacts
      simp [hparse] at h
  | some parsed =>
      have hcompact : parsed.compact = compactExample := by
        simpa [hparse] using reversed_and_repeated_source_compacts
      rw [← hcompact]
      exact parsed_bytes_sound reversedAndRepeatedBytes parsed input hparse

/-- Alias lets and reference parentheses erase before normalization. The
producer names and operand names below are exactly those in the pinned
normalized JSON above; `returned` is absent from both JSON and canonical IR.
The reversed duplicate `d` is then merged into canonical producer `c`. -/
def aliasedReversedSource : Token := token
  "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let base = (x); let a = (base) + x; let keep = (a); let b = base .* x; let c = keep + b; let d = b + a; let returned = (d); returned }"

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem aliased_reversed_exact_bytes :
    checkBytes aliasedReversedSource reversedAndRepeatedNormalized
      reversedAndRepeatedCanonical = some compactExample := by decide

/-- A lexical alias neither adds an instruction nor changes the semantic
claim checked against the optimized direct-Gate AIR model. -/
theorem aliased_reversed_semantics (input : Lanes) :
    executeNormalized compactExample input =
      denotation aliasedReversedSource input := by
  obtain ⟨_, _, _, _, _, hsem⟩ :=
    checked_bytes_sound aliasedReversedSource reversedAndRepeatedNormalized
      reversedAndRepeatedCanonical compactExample input
      aliased_reversed_exact_bytes
  exact hsem

set_option maxRecDepth 8192 in
theorem optimized_forward_alias_rejected :
    parseBytes (token
      "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let copy = later; let later = x + x; later }") = none := by decide

set_option maxRecDepth 8192 in
theorem optimized_duplicate_alias_name_rejected :
    parseBytes (token
      "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let a = a; a }") = none := by decide

set_option maxRecDepth 8192 in
theorem optimized_alias_of_input_output_rejected :
    parseBytes (token
      "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let copy = x; copy }") = none := by decide

set_option maxRecDepth 8192 in
theorem optimized_malformed_alias_rejected :
    parseBytes (token
      "circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { let a = x + x; let copy = (a; copy }") = none := by decide

end S31.Functional.Correspondence.OptimizedTextBytes
