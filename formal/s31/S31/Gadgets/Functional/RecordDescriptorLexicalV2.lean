import S31.Gadgets.Functional.RecordDescriptorValidationV2

/-!
Byte-exact lexical strengthening of the already parsed public record ABI v2
descriptor model. The production `record_abi.zig::name` accepts one through
128 UTF-8 bytes, with an ASCII letter or underscore first and only ASCII
letters, digits, or underscores thereafter. The executable checker below
applies that rule to input/result root names and every nominal/field name at
every depth. It composes with, but does not alter, `checkDescriptor`.

This does not prove that native JSON parsing yields `NamedLayout`, that leaf
paths bind relation wires, or that a native proof authenticates the descriptor.
-/

namespace S31.Functional.RecordDescriptorLexicalV2

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open S31.Functional.RecordDescriptorValidationV2

def asciiLetter (byte : UInt8) : Bool :=
  decide (65 ≤ byte.toNat ∧ byte.toNat ≤ 90) ||
    decide (97 ≤ byte.toNat ∧ byte.toNat ≤ 122)

def asciiDigit (byte : UInt8) : Bool :=
  decide (48 ≤ byte.toNat ∧ byte.toNat ≤ 57)

def initialByte (byte : UInt8) : Bool :=
  asciiLetter byte || decide (byte.toNat = 95)

def continuationByte (byte : UInt8) : Bool :=
  asciiLetter byte || asciiDigit byte || decide (byte.toNat = 95)

/-- Exactly the native `name` byte rule, including the 128-byte ceiling.
Using UTF-8 bytes rather than Unicode scalar values rejects non-ASCII names. -/
def checkNativeName (name : String) : Bool :=
  let bytes := name.toUTF8.data.toList
  decide (1 ≤ bytes.length) && decide (bytes.length ≤ 128) &&
    match bytes with
    | [] => false
    | first :: rest => initialByte first && rest.all continuationByte

def NativeNameGrammar (name : String) : Prop :=
  let bytes := name.toUTF8.data.toList
  1 ≤ bytes.length ∧ bytes.length ≤ 128 ∧
    match bytes with
    | [] => False
    | first :: rest =>
        initialByte first = true ∧
          ∀ byte ∈ rest, continuationByte byte = true

theorem checkNativeName_iff (name : String) :
    checkNativeName name = true ↔ NativeNameGrammar name := by
  simp only [checkNativeName, NativeNameGrammar, Bool.and_eq_true,
    decide_eq_true_eq]
  cases name.toUTF8.data.toList with
  | nil => simp
  | cons first rest => simp [List.all_eq_true]

/-- Preorder enumeration includes each nominal and each field name, then
recurses into record fields and tuple elements. -/
def layoutNames : NamedLayout → List String
  | .leaf _ _ => []
  | .record nominal arity fields child =>
      nominal :: ((List.finRange arity).flatMap fun i =>
        fields i :: layoutNames (child i))
  | .tuple arity child =>
      (List.finRange arity).flatMap fun i => layoutNames (child i)

def descriptorNames (descriptor : Descriptor) : List String :=
  (descriptor.inputs.flatMap fun root =>
    root.name :: layoutNames root.layout) ++
      (descriptor.result.name :: layoutNames descriptor.result.layout)

def checkLexicalDescriptor (descriptor : Descriptor) : Bool :=
  checkDescriptor descriptor &&
    (descriptorNames descriptor).all checkNativeName

theorem checkLexicalDescriptor_iff (descriptor : Descriptor) :
    checkLexicalDescriptor descriptor = true ↔
      ValidDescriptor descriptor ∧
        ∀ name ∈ descriptorNames descriptor, NativeNameGrammar name := by
  simp only [checkLexicalDescriptor, Bool.and_eq_true,
    checkDescriptor_iff, List.all_eq_true]
  constructor
  · intro ⟨shape, names⟩
    exact ⟨shape, fun name member =>
      (checkNativeName_iff name).mp (names name member)⟩
  · intro ⟨shape, names⟩
    exact ⟨shape, fun name member =>
      (checkNativeName_iff name).mpr (names name member)⟩

theorem checked_shape (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true) :
    ValidDescriptor descriptor :=
  (checkLexicalDescriptor_iff descriptor).mp accepted |>.1

theorem checked_name (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true)
    (name : String) (member : name ∈ descriptorNames descriptor) :
    NativeNameGrammar name :=
  (checkLexicalDescriptor_iff descriptor).mp accepted |>.2 name member

theorem checked_input_root_name (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true)
    (root : InputRoot) (member : root ∈ descriptor.inputs) :
    NativeNameGrammar root.name := by
  apply checked_name descriptor accepted
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  exact ⟨root, member, by simp⟩

theorem checked_input_layout_name (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true)
    (root : InputRoot) (member : root ∈ descriptor.inputs)
    (name : String) (nameMember : name ∈ layoutNames root.layout) :
    NativeNameGrammar name := by
  apply checked_name descriptor accepted
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  exact ⟨root, member, by simp [nameMember]⟩

theorem checked_result_root_name (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true) :
    NativeNameGrammar descriptor.result.name := by
  apply checked_name descriptor accepted
  simp [descriptorNames]

theorem checked_result_layout_name (descriptor : Descriptor)
    (accepted : checkLexicalDescriptor descriptor = true)
    (name : String) (member : name ∈ layoutNames descriptor.result.layout) :
    NativeNameGrammar name := by
  apply checked_name descriptor accepted
  simp [descriptorNames, member]

theorem record_nominal_listed (nominal : String) (arity : Nat)
    (fields : Fin arity → String) (child : Fin arity → NamedLayout) :
    nominal ∈ layoutNames (.record nominal arity fields child) := by
  simp [layoutNames]

theorem record_field_listed (nominal : String) (arity : Nat)
    (fields : Fin arity → String) (child : Fin arity → NamedLayout)
    (i : Fin arity) :
    fields i ∈ layoutNames (.record nominal arity fields child) := by
  simp only [layoutNames, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨i, List.mem_finRange i, by simp⟩

theorem record_child_names_listed (nominal : String) (arity : Nat)
    (fields : Fin arity → String) (child : Fin arity → NamedLayout)
    (i : Fin arity) (name : String)
    (member : name ∈ layoutNames (child i)) :
    name ∈ layoutNames (.record nominal arity fields child) := by
  simp only [layoutNames, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨i, List.mem_finRange i, Or.inr member⟩

theorem tuple_child_names_listed (arity : Nat)
    (child : Fin arity → NamedLayout) (i : Fin arity)
    (name : String) (member : name ∈ layoutNames (child i)) :
    name ∈ layoutNames (.tuple arity child) := by
  simp only [layoutNames, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, member⟩

theorem accepted_example :
    checkLexicalDescriptor exampleDescriptor = true := by decide

def badInputName : Descriptor :=
  { inputs := [{ name := "bad-name", visibility := .pub,
                 layout := pairType 1 }]
    result := { name := "result", layout := pairType 1 } }

theorem badInputName_shape_ok :
    checkDescriptor badInputName = true := by decide
theorem badInputName_rejected :
    checkLexicalDescriptor badInputName = false := by decide

def emptyNominalLayout : NamedLayout :=
  .record "" 1 (fun _ => "value") (fun _ => .leaf .m31 1)

def badNominalName : Descriptor :=
  { inputs := [], result := { name := "result", layout := emptyNominalLayout } }

theorem badNominalName_shape_ok :
    checkDescriptor badNominalName = true := by decide
theorem badNominalName_rejected :
    checkLexicalDescriptor badNominalName = false := by decide

def emptyFieldLayout : NamedLayout :=
  .record "R" 1 (fun _ => "") (fun _ => .leaf .m31 1)

def badFieldName : Descriptor :=
  { inputs := [], result := { name := "result", layout := emptyFieldLayout } }

theorem badFieldName_shape_ok :
    checkDescriptor badFieldName = true := by decide
theorem badFieldName_rejected :
    checkLexicalDescriptor badFieldName = false := by decide

def badNestedLayout : NamedLayout :=
  .record "Top" 1 (fun _ => "child") (fun _ =>
    .tuple 1 (fun _ =>
      .record "Nested" 1 (fun _ => "bad-name")
        (fun _ => .leaf .m31 1)))

def badNestedFieldName : Descriptor :=
  { inputs := [], result := { name := "result", layout := badNestedLayout } }

theorem badNestedFieldName_shape_ok :
    checkDescriptor badNestedFieldName = true := by decide
theorem badNestedFieldName_rejected :
    checkLexicalDescriptor badNestedFieldName = false := by decide

theorem underscore_and_digits_accepted :
    checkNativeName "_aZ09" = true := by decide
theorem leading_digit_rejected :
    checkNativeName "9a" = false := by decide
theorem non_ascii_rejected :
    checkNativeName "é" = false := by decide
theorem empty_rejected :
    checkNativeName "" = false := by decide
theorem max_bytes_accepted :
    checkNativeName ("a" ++ String.ofList (List.replicate 127 'x')) = true := by decide
theorem overlong_rejected :
    checkNativeName ("a" ++ String.ofList (List.replicate 128 'x')) = false := by decide

end S31.Functional.RecordDescriptorLexicalV2
