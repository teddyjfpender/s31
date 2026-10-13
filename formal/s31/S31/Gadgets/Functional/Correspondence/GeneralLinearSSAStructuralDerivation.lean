import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

/-!
An independent, bounded decoder and erasure checker for the M31 arm of
`typed-structural-derivation.json`. Its source of truth is the exact source
bytes parsed by Lean, not the Python-produced tree. A successful check joins
the tree's generic construct/project/helper rules to the same SSA and
normalized `Program` accepted by the effects package checker.

This validator does not cover the record-v2 arm, recompute SHA-256 fields,
prove the Python tree builder equivalent to this decoder, or authenticate
native AIR rows. The package pinning layer owns byte identity.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAStructuralDerivation

open Lean
open GeneralLinearSSAEffectsPackageCheck
open GeneralLinearSSAEffects
open GeneralLinearSSABytes (Parse fields field string nat array exactString
  pythonCanonical digest)

inductive Expr where
  | name (value : String)
  | literal (length value : Nat)
  | construct (fields : List (String × Expr))
  | project (source : Expr) (field : String)
  | binary (op : String) (lhs rhs : Expr)
  | apply (helper : String) (args : List Expr)
  deriving Repr

structure Input where
  name : String
  visibility : String
  length : Nat
  deriving Repr

structure Helper where
  name : String
  params : List String
  body : Expr
  deriving Repr

inductive Step where
  | letValue (name : String) (expr : Expr)
  | assertEq (lhs rhs : Expr)
  deriving Repr

structure Tree where
  name : String
  inputs : List Input
  helpers : List Helper
  steps : List Step
  result : Expr
  lowering : String
  deriving Repr

private def boundedName (json : Json) : Parse String := do
  let name ← string json
  if name.isEmpty || name.length > 128 then throw "invalid structural name"
  return name

private def parseExpr : Nat → Json → Parse Expr
  | 0, _ => throw "structural expression exceeds depth bound"
  | fuel + 1, json => do
      let kind ← string (← field json "kind")
      match kind with
      | "name" =>
          fields json ["kind", "name"]
          return .name (← boundedName (← field json "name"))
      | "literal" =>
          fields json ["kind", "length", "value"]
          return .literal (← nat (← field json "length"))
            (← nat (← field json "value"))
      | "construct" =>
          fields json ["kind", "type", "fields"]
          exactString (← field json "type") "tuple"
          let members ← array (fun item => do
            fields item ["label", "value"]
            let label ← boundedName (← field item "label")
            let value ← parseExpr fuel (← field item "value")
            return (label, value)) (← field json "fields")
          return .construct members
      | "project" =>
          fields json ["kind", "source", "field"]
          return .project (← parseExpr fuel (← field json "source"))
            (← boundedName (← field json "field"))
      | "binary" =>
          fields json ["kind", "op", "lhs", "rhs"]
          let op ← string (← field json "op")
          if op != "+" && op != "-" && op != ".*" then
            throw "unsupported structural binary operation"
          return .binary op (← parseExpr fuel (← field json "lhs"))
            (← parseExpr fuel (← field json "rhs"))
      | "apply" =>
          fields json ["kind", "helper", "args"]
          return .apply (← boundedName (← field json "helper"))
            (← array (parseExpr fuel) (← field json "args"))
      | _ => throw "unsupported structural expression"

private def parseInput (json : Json) : Parse Input := do
  fields json ["name", "kind", "length", "visibility"]
  exactString (← field json "kind") "m31"
  let name ← boundedName (← field json "name")
  let visibility ← string (← field json "visibility")
  let length ← nat (← field json "length")
  return { name, visibility, length }

private def parseHelper (json : Json) : Parse Helper := do
  fields json ["name", "params", "body"]
  let name ← boundedName (← field json "name")
  let params ← array boundedName (← field json "params")
  let body ← parseExpr 6 (← field json "body")
  return { name, params, body }

private def parseStep (json : Json) : Parse Step := do
  let kind ← string (← field json "kind")
  match kind with
  | "let" =>
      fields json ["kind", "name", "expr"]
      return .letValue (← boundedName (← field json "name"))
        (← parseExpr 6 (← field json "expr"))
  | "assert" =>
      fields json ["kind", "lhs", "rhs"]
      return .assertEq (← parseExpr 6 (← field json "lhs"))
        (← parseExpr 6 (← field json "rhs"))
  | _ => throw "unsupported structural step"

private def parseTree (json : Json) (lowering : String) : Parse Tree := do
  fields json ["fragment", "name", "inputs", "helpers", "steps", "result"]
  exactString (← field json "fragment") "m31-v1"
  let name ← boundedName (← field json "name")
  let inputs ← array parseInput (← field json "inputs")
  let helpers ← array parseHelper (← field json "helpers")
  let steps ← array parseStep (← field json "steps")
  let result ← parseExpr 6 (← field json "result")
  return { name, inputs, helpers, steps, result, lowering }

/-- Canonical JSON decoding and exact field-shape admission. The hashes are
checked for syntax here; the externally pinned package checker authenticates
their actual values. -/
def decodeTree (bytes : String) : Parse Tree := do
  if bytes.utf8ByteSize > 131072 then
    throw "structural certificate exceeds 131072 bytes"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical structural certificate JSON"
  fields json ["schema", "capability", "source_sha256", "relation_sha256",
    "public_abi_sha256", "lowering", "program"]
  exactString (← field json "schema") "s31-typed-structural-derivation-v1"
  exactString (← field json "capability")
    "exact-source-to-typed-erasure-and-value-only"
  digest (← field json "source_sha256")
  digest (← field json "relation_sha256")
  digest (← field json "public_abi_sha256")
  let lowering ← string (← field json "lowering")
  if lowering != "gate" && lowering != "direct-gate" then
    throw "unsupported structural lowering"
  parseTree (← field json "program") lowering

private inductive Value where
  | wire (id : Nat)
  | literal (value : Nat)
  | product (fields : List (String × Nat))
  | binary (op : String) (lhs rhs : Value)

/-- One field-elimination rule is used for tuple projections and helper
parameter binding. It never creates an SSA node. -/
def project (fields : List (String × Nat)) (label : String) : Option Nat :=
  (fields.find? (fun member => member.1 == label)).map Prod.snd

theorem project_exact (fields : List (String × Nat)) (label : String)
    (id : Nat) :
    project fields label = some id ↔
      (fields.find? (fun member => member.1 == label)).map Prod.snd = some id := by
  rfl

private def indexedFields : Nat → List Nat → List (String × Nat)
  | _, [] => []
  | index, id :: rest => (toString index, id) :: indexedFields (index + 1) rest

private def evaluate : Nat → Nat → List (String × Value) → List Helper →
    Expr → Option Value
  | 0, _, _, _, _ => none
  | fuel + 1, lanes, env, helpers, expr =>
      match expr with
      | .name name => (env.find? (fun entry => entry.1 == name)).map Prod.snd
      | .literal length value =>
          if length == lanes && value < S31.modulus then some (.literal value)
          else none
      | .construct fields => do
          if fields.length < 2 || fields.length > 4 then none else
          let members ← fields.foldlM (fun members (label, value) => do
            if label != toString members.length then none else
            match ← evaluate fuel lanes env helpers value with
            | .wire id => some (members ++ [(label, id)])
            | _ => none) []
          return .product members
      | .project source label => do
          match ← evaluate fuel lanes env helpers source with
          | .product fields => .wire <$> project fields label
          | _ => none
      | .binary op lhs rhs => do
          if op != "+" && op != "-" && op != ".*" then none else
          let left ← evaluate fuel lanes env helpers lhs
          let right ← evaluate fuel lanes env helpers rhs
          match left, right with
          | .wire _, .wire _ | .wire _, .literal _ | .literal _, .wire _ =>
              return .binary op left right
          | _, _ => none
      | .apply helperName args => do
          let helper ← helpers.find? (fun found => found.name == helperName)
          if args.length != helper.params.length then none else
          let values ← args.mapM (evaluate fuel lanes env helpers)
          let ids ← values.mapM (fun value => match value with
            | .wire id => some id
            | _ => none)
          let product := indexedFields 0 ids
          let bound ← (List.range helper.params.length).mapM (fun index => do
            let param ← helper.params[index]?
            let id ← project product (toString index)
            return (param, .wire id))
          match ← evaluate fuel lanes bound [] helper.body with
          | .binary op lhs rhs => return .binary op lhs rhs
          | _ => none

private def nodeFor (name : String) (id : Nat) (op : String)
    (lhs rhs : Value) : Option EmittedNode := do
  match lhs, rhs with
  | .wire left, .wire right =>
      let operation := if op == "+" then "add"
        else if op == "-" then "sub" else "mul"
      return { id, name, op := operation, lhs := left, rhs := some right, constant := none }
  | .wire left, .literal right =>
      let operation := if op == ".*" then "mul_const" else "add_const"
      let constant := if op == "-" then (S31.modulus - right) % S31.modulus
        else right
      return { id, name, op := operation, lhs := left, rhs := none, constant := some constant }
  | .literal left, .wire right =>
      if op == "-" then none else
      let operation := if op == ".*" then "mul_const" else "add_const"
      return { id, name, op := operation, lhs := right, rhs := none, constant := some left }
  | _, _ => none

private structure State where
  env : List (String × Value)
  nodes : List EmittedNode
  assertions : List (Nat × Nat)
  lets : Nat

private def deriveStep (lanes inputCount : Nat) (helpers : List Helper)
    (state : State) (step : Step) : Option State := do
  match step with
  | .letValue name expr =>
      if state.lets >= 32 || state.env.any (fun entry => entry.1 == name) ||
          helpers.any (fun helper => helper.name == name) then none else
      let value ← evaluate 7 lanes state.env helpers expr
      let (value, nodes) ← match value with
        | .binary op lhs rhs => do
            if state.nodes.length >= 16 then none else
            let id := inputCount + state.nodes.length
            let node ← nodeFor name id op lhs rhs
            some (.wire id, state.nodes ++ [node])
        | other => some (other, state.nodes)
      return { state with env := state.env ++ [(name, value)], nodes, lets := state.lets + 1 }
  | .assertEq lhs rhs =>
      if state.assertions.length >= 16 then none else
      let .wire left ← evaluate 7 lanes state.env helpers lhs | none
      let .wire right ← evaluate 7 lanes state.env helpers rhs | none
      let pair := (min left right, max left right)
      if state.assertions.any (fun (a, b) => (min a b, max a b) == pair) then
        none
      else
        return { state with assertions := state.assertions ++ [(left, right)] }

private def usedHelper : Step → Option String
  | .letValue _ (.apply name _) => some name
  | _ => none

/-- Independently replay the bounded typed tree into its complete indexed
M31 SSA. Construction, projection, aliases, and helper parameter binding are
zero-node steps; binary arithmetic allocates one ordered node. -/
def deriveSSA (tree : Tree) : Option EmittedSSA := do
  if tree.inputs.isEmpty || tree.inputs.length > 4 || tree.helpers.length > 8 ||
      tree.steps.length > 48 then none else
  let first ← tree.inputs.head?
  let lanes := first.length
  if lanes == 0 || lanes > 8 ||
      tree.inputs.any (fun input => input.length != lanes ||
        (input.visibility != "public" && input.visibility != "private")) then
    none
  else pure ()
  let helperNames := tree.helpers.map (·.name)
  if helperNames.eraseDups.length != helperNames.length ||
      helperNames.contains tree.name ||
      tree.helpers.any (fun helper => helper.params.isEmpty ||
        helper.params.length > 2 ||
        helper.params.eraseDups.length != helper.params.length ||
        helper.params.contains helper.name) then none else pure ()
  let inputNames := tree.inputs.map (·.name)
  if inputNames.eraseDups.length != inputNames.length ||
      inputNames.any helperNames.contains ||
      lanes * (1 + (tree.inputs.filter (·.visibility == "public")).length) > 8
      then none else pure ()
  let used := tree.steps.filterMap usedHelper
  if tree.helpers.any (fun helper => !used.contains helper.name) then none
    else pure ()
  let inputs := (tree.inputs.zipIdx).map (fun (input, id) =>
    ({ id, name := input.name, visibility := input.visibility } :
      GeneralLinearSSA.EmittedInput))
  let initial : State := { env := (tree.inputs.zipIdx).map (fun (input, id) =>
      (input.name, .wire id)), nodes := [], assertions := [], lets := 0 }
  let state ← tree.steps.foldlM (deriveStep lanes inputs.length tree.helpers)
    initial
  if state.nodes.isEmpty then none else
  let .wire output ← evaluate 7 lanes state.env tree.helpers tree.result | none
  return { lane_count := lanes, inputs, nodes := state.nodes, assertions := state.assertions, output }

structure Checked where
  tree : Tree
  source : CheckedSourceRelation

/-- This is the translation validator. It parses the structural artifact and
its source independently inside Lean, replays structural erasure, then
requires both routes to produce the same entire indexed graph. The existing
source/relation checker also compares that graph to the exact normalized JSON
wire shape and typed `Program`. -/
def checkRelation (sourceBytes : List Nat) (treeBytes certificateBytes
    relationBytes : String) : Parse Checked :=
  match decodeTree treeBytes with
  | .error error => .error error
  | .ok tree =>
      match deriveSSA tree with
      | none => .error "typed structural tree cannot erase to M31 SSA"
      | some structuralSSA =>
          match checkSourceRelationBytes sourceBytes certificateBytes relationBytes with
          | .error error => .error error
          | .ok checked =>
              if structuralSSA = checked.ssa then
                if tree.name = checked.program.name then
                  if GeneralLinearSSAEffectsSourceBytes.parseSourceHelperNames
                      sourceBytes = some (tree.helpers.map (·.name)) then
                    .ok ⟨tree, checked⟩
                  else .error "typed structural helper order differs from source"
                else .error "typed structural circuit name differs from normalized relation"
              else .error "typed structural erasure differs from exact source SSA"

/-- A successful exact-byte structural check removes the need to assume that
Python's typed-tree erasure produces the SSA checked from source bytes. This
theorem is conditional on the validator accepting; it is not a theorem about
the Python parser for all possible texts. -/
theorem checked_relation_parts (sourceBytes : List Nat)
    (treeBytes certificateBytes relationBytes : String)
    (tree : Tree) (checked : CheckedSourceRelation)
    (h : checkRelation sourceBytes treeBytes certificateBytes relationBytes =
      .ok ⟨tree, checked⟩) :
    decodeTree treeBytes = .ok tree ∧
    deriveSSA tree = some checked.ssa ∧
    checkSourceRelationBytes sourceBytes certificateBytes relationBytes =
      .ok checked ∧
    GeneralLinearSSAEffectsSourceBytes.parseSourceHelperNames sourceBytes =
      some (tree.helpers.map (·.name)) := by
  unfold checkRelation at h
  cases htree : decodeTree treeBytes with
  | error error => simp [htree] at h
  | ok parsedTree =>
      cases hderive : deriveSSA parsedTree with
      | none => simp [htree, hderive] at h
      | some structuralSSA =>
          cases hsource : checkSourceRelationBytes sourceBytes certificateBytes
              relationBytes with
          | error error => simp [htree, hderive, hsource] at h
          | ok parsedSource =>
              by_cases hssa : structuralSSA = parsedSource.ssa
              · by_cases hname : parsedTree.name = parsedSource.program.name
                · by_cases hhelper :
                    GeneralLinearSSAEffectsSourceBytes.parseSourceHelperNames
                      sourceBytes = some (parsedTree.helpers.map (·.name))
                  · have heq : (⟨parsedTree, parsedSource⟩ : Checked) =
                      ⟨tree, checked⟩ := by
                      simpa [htree, hderive, hsource, hssa, hname, hhelper] using h
                    have htreeEq : parsedTree = tree := congrArg Checked.tree heq
                    have hsourceEq : parsedSource = checked := congrArg Checked.source heq
                    subst tree
                    subst checked
                    simp [hderive, hssa, hhelper]
                  · simp [htree, hderive, hsource, hssa, hname, hhelper] at h
                · simp [htree, hderive, hsource, hssa, hname] at h
              · simp [htree, hderive, hsource, hssa] at h

theorem checked_relation_graph (sourceBytes : List Nat)
    (treeBytes certificateBytes relationBytes : String)
    (tree : Tree) (checked : CheckedSourceRelation)
    (h : checkRelation sourceBytes treeBytes certificateBytes relationBytes =
      .ok ⟨tree, checked⟩) :
    deriveSSA tree = some checked.ssa ∧
    GeneralLinearSSAEffectsSourceBytes.parseSource sourceBytes =
      some checked.ssa ∧
    GeneralLinearSSAPublicABI.parseRelation relationBytes = .ok checked.program ∧
    GeneralLinearSSAPublicABI.expectedEffectsNodes checked.ssa =
      some checked.program.nodes ∧
    GeneralLinearSSAPublicABI.expectedEffectsAssertions checked.ssa =
      some checked.program.assertions ∧
    GeneralLinearSSAEffectsSourceBytes.parseSourceHelperNames sourceBytes =
      some (tree.helpers.map (·.name)) := by
  obtain ⟨_, herasure, hsource, horder⟩ := checked_relation_parts
    sourceBytes treeBytes certificateBytes relationBytes tree checked h
  obtain ⟨_, hrelation, hparse, hnodes, hassertions, _, _, _⟩ :=
    checked_source_relation_graph sourceBytes certificateBytes relationBytes
      checked hsource
  exact ⟨herasure, hparse, hrelation, hnodes, hassertions, horder⟩

structure CheckedPackage where
  joined : Checked
  static : StaticPackage

/-- The package variant also checks the source-derived public ABI and ties
the structural artifact's lowering label to the exact accepted ABI encoding. -/
def checkPackage (sourceBytes : List Nat) (treeBytes certificateBytes
    relationBytes abiBytes : String) : Parse CheckedPackage :=
  match checkRelation sourceBytes treeBytes certificateBytes relationBytes with
  | .error error => .error error
  | .ok joined =>
      match checkStatic sourceBytes certificateBytes relationBytes abiBytes with
      | .error error => .error error
      | .ok static =>
          match GeneralLinearSSAPublicABI.parseDescriptor abiBytes with
          | .error error => .error error
          | .ok descriptor =>
              let expected := if joined.tree.lowering == "gate" then
                "eight little-endian u32 words; unused words are zero"
                else GeneralLinearSSAPublicABI.encoding
              if descriptor.encoding = expected then .ok ⟨joined, static⟩
              else .error "structural lowering and public ABI encoding differ"

end S31.Functional.Correspondence.GeneralLinearSSAStructuralDerivation
