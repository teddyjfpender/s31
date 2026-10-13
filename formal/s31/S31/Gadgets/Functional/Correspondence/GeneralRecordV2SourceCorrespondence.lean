import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import S31.Gadgets.Functional.SSATextBytes

/-!
An exact-source translation validator for the bounded nominal M31 record-v2
fragment. This module lexes the source bytes independently, resolves fields
and earlier locals, and builds both the typed structural tree and the complete
normalized relation/record boundary. Neither expected object is read from a
compiler artifact. Canonical artifact bytes are compared only after this
source reconstruction.

The ABI sidecar's SHA-256 text is checked for syntax, not recomputed in Lean;
the package snapshot and Python verifier retain that byte-binding duty.
The arithmetic graph is an M31 scalar graph; native AIR and PCS custody are
separate obligations.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2SourceCorrespondence

open Lean
open S31.Functional.SSATextBytes (Token token expect expectMany isSpace isNameStart
  isNameTail span)
open GeneralLinearSSABytes (Parse pythonCanonical fields field string nat array digest
  exactString)

private def obj := Json.mkObj
private def str := Json.str
private def arr (items : List Json) : Json := toJson items
private def num (value : Nat) : Json := toJson value

private def nameText (name : Token) : String :=
  String.ofList (name.map Char.ofNat)

private def forbidden : List Token :=
  (List.map token ["use", "let", "in", "if", "then", "else", "match", "fun",
    "Fn", "fn", "struct", "enum", "circuit", "blinded", "public", "private",
    "assert_eq", "m31", "accumulate_chainwork", "blake2s_leaf",
    "blake2s_pair", "block_work", "chainwork_from_work", "chainwork_u256",
    "genesis_hash_mainnet", "header_bits", "header_time", "is_zero",
    "iterate", "lt_u32", "m31_from_u16", "merkle_path_blake2s",
    "merkle_path_poseidon2", "poseidon2_leaf", "poseidon2_pair", "pow_valid",
    "prev_hash", "select", "sha256d_header", "splat", "target_mainnet",
    "target_u256", "work_u256"])

private def reservedRecord : List Token :=
  List.map token ["UInt256", "Bytes32", "BlockHash", "Target", "Work",
    "ChainWork", "Bytes80", "Digest", "Poseidon2", "Blake2sReduced"]

private def takeIdent : List Token → Option (String × List Token)
  | name :: rest =>
      if name.isEmpty || !isNameStart name.head! ||
          !name.tail.all isNameTail || name.length > 128 ||
          forbidden.contains name || (nameText name).startsWith "_s31_abi_input_" then
        none
      else some (nameText name, rest)
  | [] => none

private def takeVisibility : List Token → Option (String × List Token)
  | head :: rest =>
      if head == token "public" then some ("public", rest)
      else if head == token "private" then some ("private", rest)
      else none
  | [] => none

private def lexFuel : Nat → List Nat → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, head :: tail =>
      if isSpace head then lexFuel fuel tail
      else if head == 47 then
        match tail with
        | 47 :: after => lexFuel fuel (span (fun b => b != 10) after).2
        | _ => none
      else if isNameStart head then do
        let (suffix, rest) := span isNameTail tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if S31.Functional.SSATextBytes.isDigit head then do
        let (suffix, rest) := span S31.Functional.SSATextBytes.isDigit tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if head == 45 then
        match tail with
        | 62 :: rest => return [45, 62] :: (← lexFuel fuel rest)
        | _ => none
      else if head == 46 then
        match tail with
        | 42 :: rest => return [46, 42] :: (← lexFuel fuel rest)
        | _ => return [46] :: (← lexFuel fuel tail)
      else if List.contains [40, 41, 44, 91, 93, 59, 58, 123, 125, 61, 43] head then
        return [head] :: (← lexFuel fuel tail)
      else none

private def leafType (remaining : List Token) : Option (List Token) :=
  expectMany [token "[", token "m31", token ";", token "1", token "]"] remaining

private def parseMoreFields : Nat → List String → List Token →
    Option (List String × List Token)
  | 0, _, _ => none
  | fuel + 1, found, remaining => do
      if remaining.head? == some (token ",") then
        let rest ← expect (token ",") remaining
        let (name, rest) ← takeIdent rest
        if found.contains name || found.length >= 4 then none else
        let rest ← expect (token ":") rest
        let rest ← leafType rest
        parseMoreFields fuel (found ++ [name]) rest
      else return (found, ← expect (token "}") remaining)

structure Root where
  name : String
  visibility : String
  deriving Repr

private def parseOneRoot (record circuit : String) (roots : List Root)
    (remaining : List Token) : Option (Root × List Token) := do
  let (visibility, rest) ← takeVisibility remaining
  let (name, rest) ← takeIdent rest
  if name == record || name == circuit || name == "result" ||
      roots.any (·.name == name) then none else
  let rest ← expect (token ":") rest
  let rest ← expect (token record) rest
  return (⟨name, visibility⟩, rest)

private def parseMoreRoots (record circuit : String) (roots : List Root)
    (remaining : List Token) : Option (List Root × List Token) := do
  if remaining.head? == some (token ",") then
    if roots.length >= 2 then none else
    let rest ← expect (token ",") remaining
    let (root, rest) ← parseOneRoot record circuit roots rest
    return (roots ++ [root], ← expect (token ")") rest)
  else return (roots, ← expect (token ")") remaining)

structure Operand where
  wire : String
  expr : Json

private def nameExpr (name : String) : Json :=
  obj [("kind", str "name"), ("name", str name)]

private def parseOperand (fields : List String) (roots : List Root)
    (locals : List String) (remaining : List Token) : Option (Operand × List Token) := do
  let (name, rest) ← takeIdent remaining
  if rest.head? == some (token ".") then
    let rootIndex ← (roots.map (·.name)).idxOf? name
    let rest ← expect (token ".") rest
    let (field, rest) ← takeIdent rest
    let fieldIndex ← fields.idxOf? field
    let wire := s!"_s31_abi_input_{rootIndex * fields.length + fieldIndex}"
    return (⟨wire, obj [("kind", str "project"), ("source", nameExpr name),
      ("field", str field)]⟩, rest)
  else if locals.contains name then
    return (⟨name, nameExpr name⟩, rest)
  else none

structure Arithmetic where
  name : String
  lhs : Operand
  rhs : Operand
  op : String

private def parseLets : Nat → String → String → List String → List Root → List Arithmetic →
    List Token → Option (List Arithmetic × List Token)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, record, circuit, fields, roots, nodes, remaining => do
      if remaining.head? != some (token "let") then return (nodes, remaining)
      if nodes.length >= 8 then none else
      let rest ← expect (token "let") remaining
      let (name, rest) ← takeIdent rest
      if nodes.any (·.name == name) || roots.any (·.name == name) ||
          name == "result" || name == record || name == circuit then none else
      let rest ← expect (token "=") rest
      let locals := nodes.map (·.name)
      let (lhs, rest) ← parseOperand fields roots locals rest
      let op :: rest := rest | none
      let operation := nameText op
      if operation != "+" && operation != ".*" then none else
      let (rhs, rest) ← parseOperand fields roots locals rest
      let rest ← expect (token ";") rest
      parseLets fuel record circuit fields roots
        (nodes ++ [⟨name, lhs, rhs, operation⟩]) rest

structure ResultField where
  name : String
  value : Operand

private def parseMoreResults : Nat → List String → List Root → List String →
    List ResultField → List Token → Option (List ResultField × List Token)
  | 0, _, _, _, _, _ => none
  | fuel + 1, fields, roots, locals, found, remaining => do
      if remaining.head? == some (token ",") then
        let rest ← expect (token ",") remaining
        let (field, rest) ← takeIdent rest
        if !fields.contains field || found.any (·.name == field) then none else
        let rest ← expect (token ":") rest
        let (value, rest) ← parseOperand fields roots locals rest
        parseMoreResults fuel fields roots locals (found ++ [⟨field, value⟩]) rest
      else return (found, ← expect (token "}") remaining)

structure Source where
  record : String
  fields : List String
  circuit : String
  roots : List Root
  nodes : List Arithmetic
  result : List ResultField

def parseSource (bytes : List Nat) : Option Source := do
  if bytes.length > 16384 || !bytes.all (· < 128) then none else
  let tokens ← lexFuel (bytes.length + 1) bytes
  if tokens.length > 512 then none else
  let rest ← expect (token "struct") tokens
  let (record, rest) ← takeIdent rest
  if !(record.toList.head?.getD 'a').isUpper ||
      reservedRecord.contains (token record) then none else
  let rest ← expect (token "{") rest
  let (firstField, rest) ← takeIdent rest
  let rest ← expect (token ":") rest
  let rest ← leafType rest
  let (fields, rest) ← parseMoreFields 4 [firstField] rest
  let rest ← expect (token "circuit") rest
  let (circuit, rest) ← takeIdent rest
  if circuit == record then none else
  let rest ← expect (token "(") rest
  let (firstRoot, rest) ← parseOneRoot record circuit [] rest
  let (roots, rest) ← parseMoreRoots record circuit [firstRoot] rest
  if !roots.any (·.visibility == "public") then none else
  let rest ← expectMany [token "->", token "public", token record, token "{"] rest
  let (nodes, rest) ← parseLets 9 record circuit fields roots [] rest
  if nodes.isEmpty then none else
  let rest ← expect (token record) rest
  let rest ← expect (token "{") rest
  let (firstResult, rest) ← takeIdent rest
  if !fields.contains firstResult then none else
  let rest ← expect (token ":") rest
  let (firstValue, rest) ← parseOperand fields roots (nodes.map (·.name)) rest
  let (result, rest) ← parseMoreResults 4 fields roots (nodes.map (·.name))
    [⟨firstResult, firstValue⟩] rest
  if result.length != fields.length then none else
  let rest := if rest.head? == some (token ";") then rest.tail else rest
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let outputs := fields.map fun field =>
    ((result.find? (·.name == field)).map (·.value.wire)).getD ""
  let distinct := outputs.eraseDups
  let publicCount := (roots.filter (·.visibility == "public")).length * fields.length
  if publicCount + distinct.length > 8 then none else
  return ⟨record, fields, circuit, roots, nodes, result⟩

private def recordType (source : Source) : Json :=
  obj [("record", str source.record),
    ("fields", arr (source.fields.map fun name => obj [("name", str name),
      ("type", obj [("kind", str "m31"), ("length", num 1)])]))]

private def wire (source : Source) (rootIndex fieldIndex : Nat) : String :=
  s!"_s31_abi_input_{rootIndex * source.fields.length + fieldIndex}"

private def leaf (root field wireName : String) : Json :=
  obj [("path", arr [obj [("root", str root)], obj [("field", str field)]]),
    ("kind", str "m31"), ("length", num 1), ("wire", str wireName)]

def boundary (source : Source) : Json :=
  let roots := (source.roots.zipIdx).map fun (root, rootIndex) =>
    obj [("name", str root.name), ("type", recordType source),
      ("visibility", str root.visibility),
      ("leaves", arr ((source.fields.zipIdx).map fun (field, fieldIndex) =>
        leaf root.name field (wire source rootIndex fieldIndex)))]
  let result := source.fields.map fun field =>
    let found := source.result.find? (·.name == field)
    leaf "result" field ((found.map (·.value.wire)).getD "")
  obj [("schema", str "s31-public-record-boundary-v2"),
    ("inputs", arr roots),
    ("result", obj [("name", str "result"), ("type", recordType source),
      ("leaves", arr result)])]

private def structuralProgram (source : Source) : Json :=
  let roots := (source.roots.zipIdx).map fun (root, rootIndex) =>
    obj [("name", str root.name), ("visibility", str root.visibility),
      ("fields", arr ((source.fields.zipIdx).map fun (field, fieldIndex) =>
        obj [("name", str field),
          ("wire", str (wire source rootIndex fieldIndex))]))]
  let steps := source.nodes.map fun node =>
    obj [("kind", str "let"), ("name", str node.name),
      ("expr", obj [("kind", str "binary"), ("op", str node.op),
        ("lhs", node.lhs.expr), ("rhs", node.rhs.expr)])]
  let result := obj [("kind", str "construct"), ("type", str "record"),
    ("name", str source.record),
    ("fields", arr (source.result.map fun entry =>
      obj [("label", str entry.name), ("value", entry.value.expr)]))]
  obj [("fragment", str "record-v2"), ("name", str source.circuit),
    ("record", str source.record), ("fields", toJson source.fields),
    ("inputs", arr roots), ("steps", arr steps), ("result", result)]

def relation (source : Source) : Json :=
  let inputs := ((source.roots.zipIdx).flatMap fun (root, rootIndex) =>
    (source.fields.zipIdx).map fun (_, fieldIndex) =>
      obj [("name", str (wire source rootIndex fieldIndex)),
        ("kind", str "m31"), ("length", num 1),
        ("visibility", str root.visibility)])
  let nodes := source.nodes.map fun node =>
    obj [("name", str node.name), ("op", str (if node.op == "+" then "add" else "mul")),
      ("lhs", str node.lhs.wire), ("rhs", str node.rhs.wire)]
  let outputs := (source.fields.map fun field =>
    ((source.result.find? (·.name == field)).map (·.value.wire)).getD "").eraseDups
  obj [("version", num 2), ("name", str source.circuit),
    ("inputs", arr inputs), ("nodes", arr nodes), ("assertions", arr []),
    ("public_outputs", toJson outputs), ("public_abi", boundary source)]

/-! A scalar M31 value model for the accepted source fragment. Each input
leaf is one field element. Record construction and projection only select
wire values; arithmetic allocates exactly one new M31 value. -/

def lookupValue (values : List (String × Nat)) (name : String) : Option Nat :=
  (values.find? (·.1 == name)).map Prod.snd

private def evalNode (values : List (String × Nat)) (node : Arithmetic) :
    Option (List (String × Nat)) := do
  let lhs ← lookupValue values node.lhs.wire
  let rhs ← lookupValue values node.rhs.wire
  let value := if node.op == "+" then (lhs + rhs) % S31.modulus
    else (lhs * rhs) % S31.modulus
  return (node.name, value) :: values

def inputWires (source : Source) : List String :=
  (source.roots.zipIdx).flatMap fun (_, rootIndex) =>
    (source.fields.zipIdx).map fun (_, fieldIndex) =>
      wire source rootIndex fieldIndex

def resultWires (source : Source) : List String :=
  source.fields.map fun field =>
    ((source.result.find? (·.name == field)).map (·.value.wire)).getD ""

/-- Evaluate the exact source-fragment record in declaration field order.
Aliases select one value twice, while the normalized relation lists each
distinct public output wire once. -/
def evaluate (source : Source) (inputWords : List Nat) : Option (List Nat) := do
  let wires := inputWires source
  if inputWords.length != wires.length ||
      !inputWords.all (· < S31.modulus) then none else
  let values ← source.nodes.foldlM evalNode (List.zip wires inputWords)
  resultWires source |>.mapM (lookupValue values)

theorem eval_node_output (values : List (String × Nat)) (node : Arithmetic)
    (next : List (String × Nat)) (h : evalNode values node = some next) :
    ∃ lhs rhs,
      lookupValue values node.lhs.wire = some lhs ∧
      lookupValue values node.rhs.wire = some rhs ∧
      lookupValue next node.name = some
        (if node.op == "+" then (lhs + rhs) % S31.modulus
         else (lhs * rhs) % S31.modulus) := by
  unfold evalNode at h
  cases hleft : lookupValue values node.lhs.wire with
  | none => simp [hleft] at h
  | some lhs =>
      cases hright : lookupValue values node.rhs.wire with
      | none => simp [hleft, hright] at h
      | some rhs =>
          have hnext : (node.name,
            if node.op == "+" then (lhs + rhs) % S31.modulus
            else (lhs * rhs) % S31.modulus) :: values = next := by
            simpa [hleft, hright] using h
          refine ⟨lhs, rhs, rfl, rfl, ?_⟩
          subst next
          simp [lookupValue]

/-- Equality of result references forces equality of their source values.
This is the alias rule required by the public record boundary. -/
theorem same_result_wire_same_value (source : Source)
    (values : List (String × Nat)) (first second : String)
    (halias : ((source.result.find? (·.name == first)).map (·.value.wire)) =
      ((source.result.find? (·.name == second)).map (·.value.wire))) :
    ((source.result.find? (·.name == first)).map
      (fun entry => lookupValue values entry.value.wire)) =
    ((source.result.find? (·.name == second)).map
      (fun entry => lookupValue values entry.value.wire)) := by
  cases h1 : source.result.find? (·.name == first) with
  | none =>
      cases h2 : source.result.find? (·.name == second) with
      | none => rfl
      | some _ => simp [h1, h2] at halias
  | some left =>
      cases h2 : source.result.find? (·.name == second) with
      | none => simp [h1, h2] at halias
      | some right =>
          simp [h1, h2] at halias ⊢
          simp [halias]

private def canonicalJson (bytes : String) (limit : Nat) : Parse Json := do
  if bytes.utf8ByteSize > limit then throw "record artifact exceeds byte bound"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical record artifact JSON"
  return json

structure Checked where
  source : Source
  tree : Json
  relation : Json
  boundary : Json

/-- Every admitted byte string has a source-derived typed tree, entire
normalized relation, and ordered record boundary. The sidecar digest is
syntactic here; exact SHA-256 recomputation is a separate package duty. -/
private def checkTree (source : Source) (treeBytes : String) : Parse Json := do
  let tree ← canonicalJson treeBytes 131072
  fields tree ["schema", "capability", "source_sha256", "relation_sha256",
    "public_abi_sha256", "lowering", "program"]
  exactString (← field tree "schema") "s31-typed-structural-derivation-v1"
  exactString (← field tree "capability")
    "exact-source-to-typed-erasure-and-value-only"
  digest (← field tree "source_sha256")
  digest (← field tree "relation_sha256")
  digest (← field tree "public_abi_sha256")
  exactString (← field tree "lowering") "direct-gate"
  if (← field tree "program") == structuralProgram source then
    return tree
  else
    throw "record structural tree differs from exact source"

private def checkRelation (source : Source) (relationBytes : String) : Parse Json :=
  match canonicalJson relationBytes 65536 with
  | .error error => .error error
  | .ok actualRelation =>
      if actualRelation == relation source then .ok actualRelation
      else .error "record relation differs from exact source"

private def checkAbi (source : Source) (abiBytes : String) : Parse Json := do
  let abi ← canonicalJson abiBytes 65536
  fields abi ["schema", "boundary", "boundary_sha256", "encoding"]
  exactString (← field abi "schema") "s31-public-abi-v2"
  exactString (← field abi "encoding")
    "canonical typed-only JSON statement with named paths and aliased M31/bit/u8/u16/u32 leaves"
  digest (← field abi "boundary_sha256")
  if (← field abi "boundary") == boundary source then
    return abi
  else
    throw "record public ABI boundary differs from exact source"

theorem checked_relation_json (source : Source) (bytes : String) (actual : Json)
    (h : checkRelation source bytes = .ok actual) :
    canonicalJson bytes 65536 = .ok actual ∧
    (actual == relation source) = true := by
  unfold checkRelation at h
  cases hjson : canonicalJson bytes 65536 with
  | error _ => simp [hjson] at h
  | ok parsed =>
      cases heq : (parsed == relation source) with
      | true =>
        have hactual : parsed = actual := by
          simpa [hjson, heq] using h
        exact ⟨by simpa [hactual] using hjson, by simpa [← hactual] using heq⟩
      | false => simp [hjson, heq] at h

private def checkParsed (source : Source) (treeBytes relationBytes abiBytes : String) :
    Parse (Json × Json × Json) :=
  match checkTree source treeBytes with
  | .error error => .error error
  | .ok tree => match checkRelation source relationBytes with
    | .error error => .error error
    | .ok actualRelation => match checkAbi source abiBytes with
      | .error error => .error error
      | .ok abi => .ok (tree, actualRelation, abi)

def check (sourceBytes : List Nat) (treeBytes relationBytes abiBytes : String) :
    Parse Checked :=
  match parseSource sourceBytes with
  | none => .error "source is outside bounded record-v2 grammar"
  | some source => match checkParsed source treeBytes relationBytes abiBytes with
    | .error error => .error error
    | .ok (tree, actualRelation, abi) =>
        .ok ⟨source, tree, actualRelation, (abi.getObjVal? "boundary").toOption.getD Json.null⟩

theorem checked_source (sourceBytes : List Nat) (treeBytes relationBytes abiBytes : String)
    (accepted : Checked)
    (h : check sourceBytes treeBytes relationBytes abiBytes = .ok accepted) :
    parseSource sourceBytes = some accepted.source := by
  unfold check at h
  cases hsource : parseSource sourceBytes with
  | none => simp [hsource] at h
  | some source =>
      cases hparsed : checkParsed source treeBytes relationBytes abiBytes with
      | error _ => simp [hsource, hparsed] at h
      | ok parts =>
          rcases parts with ⟨tree, actualRelation, abi⟩
          have heq : (⟨source, tree, actualRelation,
            (abi.getObjVal? "boundary").toOption.getD Json.null⟩ : Checked) =
              accepted := by
            simpa [hsource, hparsed] using h
          have hsourceEq : source = accepted.source :=
            congrArg Checked.source heq
          simpa [hsourceEq] using hsource

theorem checked_expected_graph (sourceBytes : List Nat)
    (treeBytes relationBytes abiBytes : String) (accepted : Checked)
    (h : check sourceBytes treeBytes relationBytes abiBytes = .ok accepted) :
    canonicalJson relationBytes 65536 = .ok accepted.relation ∧
    (accepted.relation == relation accepted.source) = true := by
  unfold check at h
  cases hsource : parseSource sourceBytes with
  | none => simp [hsource] at h
  | some source =>
      cases hparsed : checkParsed source treeBytes relationBytes abiBytes with
      | error _ => simp [hsource, hparsed] at h
      | ok parts =>
          rcases parts with ⟨tree, actualRelation, abi⟩
          have heq : (⟨source, tree, actualRelation,
            (abi.getObjVal? "boundary").toOption.getD Json.null⟩ : Checked) =
              accepted := by
            simpa [hsource, hparsed] using h
          have hrelation : checkRelation source relationBytes = .ok actualRelation := by
            unfold checkParsed at hparsed
            cases htree : checkTree source treeBytes with
            | error _ => simp [htree] at hparsed
            | ok parsedTree =>
                cases hrel : checkRelation source relationBytes with
                | error _ => simp [htree, hrel] at hparsed
                | ok parsedRelation =>
                    cases habi : checkAbi source abiBytes with
                    | error _ => simp [htree, hrel, habi] at hparsed
                    | ok parsedAbi =>
                        have hparts : (parsedTree, parsedRelation, parsedAbi) =
                            (tree, actualRelation, abi) := by
                          simpa [htree, hrel, habi] using hparsed
                        cases hparts
                        rfl
          have erasure := checked_relation_json source relationBytes
            actualRelation hrelation
          exact (congrArg Checked.relation heq).symm ▸
            (congrArg Checked.source heq).symm ▸ erasure

end S31.Functional.Correspondence.GeneralRecordV2SourceCorrespondence
