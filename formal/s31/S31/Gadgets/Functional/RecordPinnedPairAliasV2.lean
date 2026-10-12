import S31.Gadgets.Functional.RecordAbiV2

/-!
A deliberately narrow executable refinement fixture for the v2 record
boundary. The source uses a public scalar `x`, computes `square = x * x`, and
returns `Pair { square, again: square }`. The two named output leaves point to
one existing relation wire. This file fixes the source and canonical ABI
descriptor bytes and proves the typed boundary projection for this fixture.

The byte encoder below only handles these pinned ASCII identifiers. Its
agreement with the Python compiler's emitted descriptor is checked by an
external exact-byte test. It is not a general JSON serializer or a proof of
the production Zig validator, hash, AIR, PCS, or native proof verifier.
-/

namespace S31.Functional.RecordPinnedPairAliasV2

open RecordBoundary RecordAbiV2

def sourceBytes : String :=
  "struct Pair { square: [m31; 1], again: [m31; 1] }\n" ++
  "circuit pair(public x: [m31; 1]) -> public Pair {\n" ++
  "    let square = x .* x;\n" ++
  "    Pair { square: square, again: square }\n" ++
  "}\n"

def inputLeafBytes : String :=
  "{\"kind\":\"m31\",\"length\":1,\"path\":[{\"root\":\"x\"}],\"wire\":\"x\"}"

def squareWireName : String := "square"
def againWireName : String := "square"

def outputLeafBytes (field wire : String) : String :=
  "{\"kind\":\"m31\",\"length\":1,\"path\":[{\"root\":\"result\"},{\"field\":\"" ++
  field ++ "\"}],\"wire\":\"" ++ wire ++ "\"}"

def scalarTypeBytes : String := "{\"kind\":\"m31\",\"length\":1}"

def pairTypeBytes : String :=
  "{\"fields\":[{\"name\":\"square\",\"type\":" ++ scalarTypeBytes ++
  "},{\"name\":\"again\",\"type\":" ++ scalarTypeBytes ++
  "}],\"record\":\"Pair\"}"

/-- The exact canonical descriptor body hashed by the v2 ABI domain separator.
The production digest additionally hashes a terminal newline. -/
def abiBodyBytes : String :=
  "{\"inputs\":[{\"leaves\":[" ++ inputLeafBytes ++
  "],\"name\":\"x\",\"type\":" ++ scalarTypeBytes ++
  ",\"visibility\":\"public\"}],\"result\":{\"leaves\":[" ++
  outputLeafBytes "square" squareWireName ++ "," ++
  outputLeafBytes "again" againWireName ++
  "],\"name\":\"result\",\"type\":" ++ pairTypeBytes ++
  "},\"schema\":\"s31-public-record-boundary-v2\"}"

def abiBytes : String := abiBodyBytes ++ "\n"

/-- The source declaration fixes distinct nominal paths even though both
paths deliberately refer to the same output wire. -/
theorem fields_have_distinct_paths :
    twoFieldPath "result" "square" "again" (.left .here) ≠
      twoFieldPath "result" "square" "again" (.right .here) := by
  decide

def roots (x : Nat) : List (InputRoot (WordBlock Nat)) :=
  [⟨.leaf, .visible, block [x]⟩]

def wires (square : Nat) : Fin 1 → WordBlock Nat :=
  fun _ => block [square]

def resultRefs : List (Fin 1) := [0, 0]

def resolveOutputWire (name : String) : Option (Fin 1) :=
  if name == "square" then some 0 else none

/-- The two wire-name literals serialized into the descriptor resolve to the
two aliases used in the typed proof-word theorem. -/
theorem descriptor_wire_names_resolve_to_model :
    [resolveOutputWire squareWireName, resolveOutputWire againWireName] =
      resultRefs.map some := by
  decide

/-- Field naming does not add a second public output proof word. -/
theorem proof_words (x square : Nat) :
    typedPublicWords (roots x) (wires square) resultRefs = [x, square] := by
  simp [typedPublicWords, boundaryProofWords, roots, resultRefs,
    publicInputWords, concatBlocks, flatten, repeated_wire_one_proof_word,
    wires, block]

/-- The first-order native projection agrees with typed flattening. -/
theorem native_words (x square : Nat) :
    nativeProjectedWords (roots x) (wires square) resultRefs = [x, square] := by
  rw [← typedPublicWords_eq_nativeProjection]
  exact proof_words x square

theorem fits_eight_words (x square : Nat) :
    withinEightWords (roots x) (wires square) resultRefs := by
  simp [withinEightWords, proof_words]

/-- Both named claims must equal the one result wire, even though the proof
word appears only once. This models the native v2 alias check. -/
theorem both_alias_claims (square first again : Nat) :
    acceptsClaims (fun _ : Fin 1 => square) resultRefs [first, again] ↔
      first = square ∧ again = square := by
  simpa [resultRefs] using
    repeated_wire_claims_sound (fun _ : Fin 1 => square) (0 : Fin 1) first again

theorem honest_seven :
    acceptsClaims (fun _ : Fin 1 => 49) resultRefs [49, 49] := by
  simp [both_alias_claims]

theorem changed_second_claim_rejected :
    ¬ acceptsClaims (fun _ : Fin 1 => 49) resultRefs [49, 50] := by
  simp [both_alias_claims]

theorem changed_first_claim_rejected :
    ¬ acceptsClaims (fun _ : Fin 1 => 49) resultRefs [50, 49] := by
  simp [both_alias_claims]

theorem public_words_at_seven :
    nativeProjectedWords (roots 7) (wires 49) resultRefs = [7, 49] :=
  native_words 7 49

end S31.Functional.RecordPinnedPairAliasV2
