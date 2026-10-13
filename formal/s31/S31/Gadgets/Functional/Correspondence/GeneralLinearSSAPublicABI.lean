import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsBytes
import S31.Semantics.Json

/-!
Source-certificate-derived public ABI for the homogeneous M31 SSA profiles.
The checks consume exact canonical ABI and assignment JSON and exact 32-byte
little-endian public-word bytes. A modeled AIR witness is a separate premise;
native row/public-pin ownership and source-text identity are not derived here.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAPublicABI

open Lean
open GeneralLinearSSA (Lanes EmittedInput)
open GeneralLinearSSABytes (Parse fields field string nat array exactString pythonCanonical)

structure Field where
  name : String
  kind : String
  length : Nat
deriving DecidableEq, Repr

structure Descriptor where
  schema : String
  encoding : String
  public_inputs : List Field
  public_outputs : List Field
deriving DecidableEq, Repr

def encoding : String :=
  "eight canonical M31 words, encoded little-endian u32; unused words are zero"

private def parseField (json : Json) : Parse Field := do
  fields json ["name", "kind", "length"]
  return { name := ← string (← field json "name"),
           kind := ← string (← field json "kind"),
           length := ← nat (← field json "length") }

private def canonicalJson (bytes : String) : Parse Json := do
  if bytes.utf8ByteSize > 65536 then throw "JSON exceeds 65536 bytes"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical JSON bytes"
  return json

def parseDescriptor (bytes : String) : Parse Descriptor := do
  let json ← canonicalJson bytes
  fields json ["schema", "encoding", "public_inputs", "public_outputs"]
  return {
    schema := ← string (← field json "schema"),
    encoding := ← string (← field json "encoding"),
    public_inputs := ← array parseField (← field json "public_inputs"),
    public_outputs := ← array parseField (← field json "public_outputs") }

def expectedDescriptor (laneCount : Nat) (inputs : List EmittedInput)
    (outputName : String) : Descriptor :=
  { schema := "s31-public-abi-v1", encoding,
    public_inputs := (inputs.filter (·.visibility == "public")).map
      (fun input => ⟨input.name, "m31", laneCount⟩),
    public_outputs := [⟨outputName, "m31", laneCount⟩] }

def checkDescriptor (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String) : Parse Unit :=
  match parseDescriptor bytes with
  | .error error => .error error
  | .ok decoded =>
      if decoded = expectedDescriptor laneCount inputs outputName then .ok ()
      else .error "public ABI differs from source-derived SSA layout"

theorem checked_descriptor (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String)
    (hcheck : checkDescriptor bytes laneCount inputs outputName = .ok ()) :
    parseDescriptor bytes =
      .ok (expectedDescriptor laneCount inputs outputName) := by
  unfold checkDescriptor at hcheck
  cases hparse : parseDescriptor bytes with
  | error error => simp [hparse] at hcheck
  | ok found =>
      by_cases heq : found = expectedDescriptor laneCount inputs outputName
      · subst found
        rfl
      · simp [hparse, heq] at hcheck

def parseRelation (bytes : String) : Parse S31.Program := do
  S31.Json.program (← canonicalJson bytes)

def visibilityName : S31.Visibility → String
  | .public => "public"
  | .private => "private"

/-- The normalized program's declared inputs, shapes, visibilities, and
single selected output determine the same ABI layout as the certificate. -/
def RelationMatches (program : S31.Program) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String) : Prop :=
  program.version = 1 ∧
  program.inputs.map (fun input => (input.name, visibilityName input.visibility)) =
    inputs.map (fun input => (input.name, input.visibility)) ∧
  program.inputs.all (fun input => decide (input.shape = ⟨.m31, laneCount⟩)) = true ∧
  program.outputs = [outputName]

instance (program : S31.Program) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String) :
    Decidable (RelationMatches program laneCount inputs outputName) := by
  unfold RelationMatches
  infer_instance

def checkRelationLayout (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String) : Parse S31.Program :=
  match parseRelation bytes with
  | .error error => .error error
  | .ok program =>
      if RelationMatches program laneCount inputs outputName then
        match program.validate with
        | .error _ => .error "normalized relation failed typed validation"
        | .ok _ => .ok program
      else .error "normalized relation public ABI differs from certificate"

theorem checked_relation_layout (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String)
    (program : S31.Program)
    (hcheck : checkRelationLayout bytes laneCount inputs outputName =
      .ok program) :
    parseRelation bytes = .ok program ∧
      RelationMatches program laneCount inputs outputName ∧
      ∃ shapes, program.validate = .ok shapes := by
  unfold checkRelationLayout at hcheck
  cases hparse : parseRelation bytes with
  | error error => simp [hparse] at hcheck
  | ok parsed =>
      by_cases hmatch : RelationMatches parsed laneCount inputs outputName
      · cases hvalidate : parsed.validate with
        | error error => simp [hparse, hmatch, hvalidate] at hcheck
        | ok shapes =>
            have heq : parsed = program := by
              simpa [hparse, hmatch, hvalidate] using hcheck
            subst program
            exact ⟨rfl, hmatch, shapes, hvalidate⟩
      · simp [hparse, hmatch] at hcheck

def checkRelationSSA (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (names : List String)
    (output : Nat) : Parse S31.Program :=
  match names[output]? with
  | none => .error "selected output name missing"
  | some outputName => checkRelationLayout bytes laneCount inputs outputName

theorem checked_relation_ssa (bytes : String) (laneCount : Nat)
    (inputs : List EmittedInput) (names : List String)
    (output : Nat) (program : S31.Program)
    (hcheck : checkRelationSSA bytes laneCount inputs names output = .ok program) :
    ∃ outputName, names[output]? = some outputName ∧
      parseRelation bytes = .ok program ∧
      RelationMatches program laneCount inputs outputName := by
  unfold checkRelationSSA at hcheck
  cases hname : names[output]? with
  | none => simp [hname] at hcheck
  | some outputName =>
      have h := checked_relation_layout bytes laneCount inputs outputName
        program (by simpa [hname] using hcheck)
      exact ⟨outputName, rfl, h.1, h.2.1⟩

private def parseNamedWords (json : Json) (names : List String)
    (laneCount : Nat) : Parse (List (String × List Nat)) := do
  fields json names
  names.mapM fun name => do
    let words ← array nat (← field json name)
    if words.length != laneCount || !words.all (· < S31.modulus) then
      throw "noncanonical or wrong-width M31 assignment"
    return (name, words)

/-- The assignment's public and private name partitions and all lanes are
checked against the decoded certificate, with one named public output. -/
def checkAssignment {n : Nat} (bytes : String)
    (inputs : List EmittedInput) (outputName : String)
    (values : Nat → Lanes n) (claimed : Lanes n) : Parse Unit := do
  let json ← canonicalJson bytes
  fields json ["public_inputs", "private_inputs", "public_outputs"]
  let publicInputs := inputs.filter (·.visibility == "public")
  let privateInputs := inputs.filter (·.visibility == "private")
  let publicWords ← parseNamedWords (← field json "public_inputs")
    (publicInputs.map (·.name)) n
  let privateWords ← parseNamedWords (← field json "private_inputs")
    (privateInputs.map (·.name)) n
  let outputWords ← parseNamedWords (← field json "public_outputs")
    [outputName] n
  if publicWords != publicInputs.map (fun input =>
      (input.name, (List.ofFn (values input.id)).map (·.val))) ||
      privateWords != privateInputs.map (fun input =>
        (input.name, (List.ofFn (values input.id)).map (·.val))) ||
      outputWords != [(outputName, (List.ofFn claimed).map (·.val))] then
    throw "assignment differs from source-derived input/output words"
  return ()

def orderedPublicWords {n : Nat} (inputs : List EmittedInput)
    (values : Nat → Lanes n) (claimed : Lanes n) : List M31 :=
  let publicWords := (inputs.filter (·.visibility == "public")).flatMap
    (fun input => List.ofFn (values input.id))
  let words := publicWords ++ List.ofFn claimed
  words ++ List.replicate (8 - words.length) 0

/-- Changing only private input values cannot change the public-input part
of the statement. A different output claim still changes its output part. -/
theorem private_input_erasure {n : Nat} (inputs : List EmittedInput)
    (left right : Nat → Lanes n) (claimed : Lanes n)
    (hpublic : ∀ input ∈ inputs.filter (·.visibility == "public"),
      left input.id = right input.id) :
    orderedPublicWords inputs left claimed =
      orderedPublicWords inputs right claimed := by
  have hselected (selected : List EmittedInput)
      (h : ∀ input ∈ selected, left input.id = right input.id) :
      selected.flatMap (fun input => List.ofFn (left input.id)) =
        selected.flatMap (fun input => List.ofFn (right input.id)) := by
    induction selected with
    | nil => rfl
    | cons input rest ih =>
        have hhead := h input (by simp)
        have hrest : ∀ entry ∈ rest, left entry.id = right entry.id := by
          intro entry hmem
          exact h entry (by simp [hmem])
        simp [hhead, ih hrest]
  unfold orderedPublicWords
  rw [hselected _ hpublic]

def wordBytes (word : M31) : List Nat :=
  [word.val % 256, word.val / 256 % 256,
   word.val / 65536 % 256, word.val / 16777216 % 256]

def publicWordBytes (words : List M31) : List Nat :=
  words.flatMap wordBytes

def checkPublicWordBytes {n : Nat} (bytes : List Nat)
    (inputs : List EmittedInput) (values : Nat → Lanes n)
    (claimed : Lanes n) : Parse Unit :=
  let words := orderedPublicWords inputs values claimed
  if words.length = 8 ∧ bytes = publicWordBytes words then .ok ()
  else .error "public words differ from eight-word little-endian statement"

theorem checked_public_word_bytes {n : Nat} (bytes : List Nat)
    (inputs : List EmittedInput) (values : Nat → Lanes n)
    (claimed : Lanes n)
    (hcheck : checkPublicWordBytes bytes inputs values claimed = .ok ()) :
    (orderedPublicWords inputs values claimed).length = 8 ∧
      bytes = publicWordBytes (orderedPublicWords inputs values claimed) := by
  simp only [checkPublicWordBytes] at hcheck
  split at hcheck
  · exact ‹_ ∧ _›
  · cases hcheck

def checkBoundary {n : Nat} (abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (laneCount : Nat)
    (inputs : List EmittedInput) (outputName : String)
    (values : Nat → Lanes n) (claimed : Lanes n) : Parse Unit :=
  if laneCount = n ∧
      checkDescriptor abiBytes laneCount inputs outputName = .ok () ∧
      checkAssignment assignmentBytes inputs outputName values claimed = .ok () ∧
      checkPublicWordBytes rawPublicBytes inputs values claimed = .ok ()
  then .ok () else .error "public ABI, assignment, or words differ"

theorem checked_boundary_parts {n : Nat}
    (abiBytes assignmentBytes : String) (rawPublicBytes : List Nat)
    (laneCount : Nat) (inputs : List EmittedInput)
    (outputName : String) (values : Nat → Lanes n)
    (claimed : Lanes n)
    (hcheck : checkBoundary abiBytes assignmentBytes rawPublicBytes
      laneCount inputs outputName values claimed = .ok ()) :
    laneCount = n ∧
    checkDescriptor abiBytes laneCount inputs outputName = .ok () ∧
    checkAssignment assignmentBytes inputs outputName values claimed = .ok () ∧
    (orderedPublicWords inputs values claimed).length = 8 ∧
    rawPublicBytes =
      publicWordBytes (orderedPublicWords inputs values claimed) := by
  unfold checkBoundary at hcheck
  split at hcheck
  · obtain ⟨hlane, habi, hassign, hwords⟩ := ‹_ ∧ _›
    exact ⟨hlane, habi, hassign,
      (checked_public_word_bytes _ _ _ _ hwords).1,
      (checked_public_word_bytes _ _ _ _ hwords).2⟩
  · cases hcheck

/-- This check establishes the full ABI/assignment/word-byte equality for
one already admitted effects certificate and separately supplied source. -/
def checkEffects (certificateBytes abiBytes assignmentBytes : String)
    (wordBytes : List Nat) (source : GeneralLinearSSAEffects.Source)
    (values : Nat → Lanes n) (claimed : Lanes n) :
    Parse (GeneralLinearSSAEffects.EmittedSSA ×
      GeneralLinearSSAEffects.Certificate) :=
  match GeneralLinearSSAEffectsBytes.checkCertificate certificateBytes source with
  | .error error => .error error
  | .ok (ssa, certificate) =>
      match ssa.names[ssa.output]? with
      | none => .error "selected output name missing"
      | some outputName =>
          match checkBoundary abiBytes assignmentBytes wordBytes ssa.lane_count
              ssa.inputs outputName values claimed with
          | .error error => .error error
          | .ok () => .ok (ssa, certificate)

/-- Pure-profile wrapper uses the identical ABI and assignment byte gate. -/
def checkPure (certificateBytes abiBytes assignmentBytes : String)
    (wordBytes : List Nat) (source : GeneralLinearSSA.Term)
    (values : Nat → Lanes n) (claimed : Lanes n) :
    Parse (GeneralLinearSSA.EmittedSSA × GeneralLinearSSA.Certificate) :=
  match GeneralLinearSSABytes.checkCertificate certificateBytes source with
  | .error error => .error error
  | .ok (ssa, certificate) =>
      match ssa.names[ssa.output]? with
      | none => .error "selected output name missing"
      | some outputName =>
          match checkBoundary abiBytes assignmentBytes wordBytes ssa.lane_count
              ssa.inputs outputName values claimed with
          | .error error => .error error
          | .ok () => .ok (ssa, certificate)

theorem checked_effects_parts (certificateBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSAEffects.Source)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (hcheck : checkEffects certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate)) :
    GeneralLinearSSAEffectsBytes.checkCertificate certificateBytes source =
      .ok (ssa, certificate) ∧
    ∃ outputName, ssa.names[ssa.output]? = some outputName ∧
      checkBoundary abiBytes assignmentBytes rawPublicBytes
        ssa.lane_count ssa.inputs outputName values claimed = .ok () := by
  unfold checkEffects at hcheck
  cases hcertificate : GeneralLinearSSAEffectsBytes.checkCertificate
      certificateBytes source with
  | error error => simp [hcertificate] at hcheck
  | ok pair =>
      obtain ⟨parsed, found⟩ := pair
      cases hname : parsed.names[parsed.output]? with
      | none => simp [hcertificate, hname] at hcheck
      | some outputName =>
          cases hboundary : checkBoundary abiBytes assignmentBytes
              rawPublicBytes parsed.lane_count parsed.inputs outputName
              values claimed with
          | error error => simp [hcertificate, hname, hboundary] at hcheck
          | ok value =>
              cases value
              have heq : (parsed, found) = (ssa, certificate) := by
                simpa [hcertificate, hname, hboundary] using hcheck
              cases Prod.mk.inj heq with
              | intro hssa hcertificateEq =>
                  subst ssa
                  subst certificate
                  exact ⟨rfl, outputName, hname, hboundary⟩

theorem checked_pure_parts (certificateBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSA.Term)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (hcheck : checkPure certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate)) :
    GeneralLinearSSABytes.checkCertificate certificateBytes source =
      .ok (ssa, certificate) ∧
    ∃ outputName, ssa.names[ssa.output]? = some outputName ∧
      checkBoundary abiBytes assignmentBytes rawPublicBytes
        ssa.lane_count ssa.inputs outputName values claimed = .ok () := by
  unfold checkPure at hcheck
  cases hcertificate : GeneralLinearSSABytes.checkCertificate
      certificateBytes source with
  | error error => simp [hcertificate] at hcheck
  | ok pair =>
      obtain ⟨parsed, found⟩ := pair
      cases hname : parsed.names[parsed.output]? with
      | none => simp [hcertificate, hname] at hcheck
      | some outputName =>
          cases hboundary : checkBoundary abiBytes assignmentBytes
              rawPublicBytes parsed.lane_count parsed.inputs outputName
              values claimed with
          | error error => simp [hcertificate, hname, hboundary] at hcheck
          | ok value =>
              cases value
              have heq : (parsed, found) = (ssa, certificate) := by
                simpa [hcertificate, hname, hboundary] using hcheck
              cases Prod.mk.inj heq with
              | intro hssa hcertificateEq =>
                  subst ssa
                  subst certificate
                  exact ⟨rfl, outputName, hname, hboundary⟩

/-- Any accepted effects witness fixes the byte-exact public statement to
the source term's output after the public inputs in declaration order. The
private inputs occur in the checked assignment but contribute no public word. -/
theorem effects_air_public_abi_sound
    (certificateBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSAEffects.Source)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (final : List (Lanes n))
    (hcheck : checkEffects certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate))
    (hrows : GeneralLinearSSAEffects.AcceptsTrace
      (GeneralLinearSSAEffects.initialValues certificate.inputs values)
      certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : GeneralLinearSSAEffects.assertionsAir final
      certificate.assertions) :
    source.accepts values claimed ∧
    ∃ outputName,
      ssa.names[ssa.output]? = some outputName ∧
      ssa.lane_count = n ∧
      parseDescriptor abiBytes =
        .ok (expectedDescriptor ssa.lane_count ssa.inputs outputName) ∧
      checkAssignment assignmentBytes ssa.inputs outputName
        values claimed = .ok () ∧
      (orderedPublicWords ssa.inputs values claimed).length = 8 ∧
      rawPublicBytes = publicWordBytes
        (orderedPublicWords ssa.inputs values (source.output.eval values)) := by
  obtain ⟨hcert, outputName, hname, hboundary⟩ :=
    checked_effects_parts certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed ssa certificate hcheck
  obtain ⟨hlane, habi, hassignment, hlength, hbytes⟩ :=
    checked_boundary_parts abiBytes assignmentBytes rawPublicBytes
      ssa.lane_count ssa.inputs outputName values claimed hboundary
  have hsourceCheck : GeneralLinearSSAEffects.check certificate source = some () :=
    (GeneralLinearSSAEffects.checked_emitted_certificate ssa source certificate
      (GeneralLinearSSAEffectsBytes.checked_certificate_parts
        certificateBytes source ssa certificate hcert).2).2
  have hsource := GeneralLinearSSAEffects.checked_air_sound certificate
    source values claimed final hsourceCheck hrows houtput hassert
  refine ⟨hsource, outputName, hname, hlane,
    checked_descriptor abiBytes ssa.lane_count ssa.inputs outputName habi,
    hassignment, hlength, ?_⟩
  simpa [hsource.1] using hbytes

theorem pure_air_public_abi_sound
    (certificateBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSA.Term)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (final : List (Lanes n))
    (hcheck : checkPure certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate))
    (hrows : GeneralLinearSSA.AcceptsTrace
      (GeneralLinearSSA.initialValues certificate.inputs values)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval values ∧
    ∃ outputName,
      ssa.names[ssa.output]? = some outputName ∧
      ssa.lane_count = n ∧
      parseDescriptor abiBytes =
        .ok (expectedDescriptor ssa.lane_count ssa.inputs outputName) ∧
      checkAssignment assignmentBytes ssa.inputs outputName
        values claimed = .ok () ∧
      (orderedPublicWords ssa.inputs values claimed).length = 8 ∧
      rawPublicBytes = publicWordBytes
        (orderedPublicWords ssa.inputs values (source.eval values)) := by
  obtain ⟨hcert, outputName, hname, hboundary⟩ :=
    checked_pure_parts certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed ssa certificate hcheck
  obtain ⟨hlane, habi, hassignment, hlength, hbytes⟩ :=
    checked_boundary_parts abiBytes assignmentBytes rawPublicBytes
      ssa.lane_count ssa.inputs outputName values claimed hboundary
  have hsourceCheck : GeneralLinearSSA.check certificate source = some () :=
    (GeneralLinearSSA.checked_emitted_certificate ssa source certificate
      (GeneralLinearSSABytes.checked_certificate_parts
        certificateBytes source ssa certificate hcert).2).2
  have hsource := GeneralLinearSSA.checked_air_sound certificate
    source values claimed final hsourceCheck hrows houtput
  refine ⟨hsource, outputName, hname, hlane,
    checked_descriptor abiBytes ssa.lane_count ssa.inputs outputName habi,
    hassignment, hlength, ?_⟩
  simpa [hsource] using hbytes

/-- The normalized relation bytes independently bind every declared input's
visibility and width and the selected output name to the certificate ABI.
Arithmetic source-byte correspondence and native public-pin ownership remain
separate boundaries. -/
theorem effects_relation_public_abi_sound
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSAEffects.Source)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (program : S31.Program) (final : List (Lanes n))
    (hcheck : checkEffects certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate))
    (hrelation : checkRelationSSA relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output = .ok program)
    (hrows : GeneralLinearSSAEffects.AcceptsTrace
      (GeneralLinearSSAEffects.initialValues certificate.inputs values)
      certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : GeneralLinearSSAEffects.assertionsAir final
      certificate.assertions) :
    source.accepts values claimed ∧
    ∃ outputName,
      parseRelation relationBytes = .ok program ∧
      RelationMatches program ssa.lane_count ssa.inputs outputName ∧
      parseDescriptor abiBytes =
        .ok (expectedDescriptor ssa.lane_count ssa.inputs outputName) ∧
      rawPublicBytes = publicWordBytes
        (orderedPublicWords ssa.inputs values (source.output.eval values)) := by
  obtain ⟨hsource, abiOutput, habiName, _, habi, _, _, hwords⟩ :=
    effects_air_public_abi_sound certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed ssa certificate final
      hcheck hrows houtput hassert
  obtain ⟨relationOutput, hrelationName, hparsed, hmatch⟩ :=
    checked_relation_ssa relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output program hrelation
  have heq : relationOutput = abiOutput :=
    Option.some.inj (hrelationName.symm.trans habiName)
  subst relationOutput
  exact ⟨hsource, abiOutput, hparsed, hmatch, habi, hwords⟩

theorem pure_relation_public_abi_sound
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (source : GeneralLinearSSA.Term)
    (values : Nat → Lanes n) (claimed : Lanes n)
    (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (program : S31.Program) (final : List (Lanes n))
    (hcheck : checkPure certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed = .ok (ssa, certificate))
    (hrelation : checkRelationSSA relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output = .ok program)
    (hrows : GeneralLinearSSA.AcceptsTrace
      (GeneralLinearSSA.initialValues certificate.inputs values)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval values ∧
    ∃ outputName,
      parseRelation relationBytes = .ok program ∧
      RelationMatches program ssa.lane_count ssa.inputs outputName ∧
      parseDescriptor abiBytes =
        .ok (expectedDescriptor ssa.lane_count ssa.inputs outputName) ∧
      rawPublicBytes = publicWordBytes
        (orderedPublicWords ssa.inputs values (source.eval values)) := by
  obtain ⟨hsource, abiOutput, habiName, _, habi, _, _, hwords⟩ :=
    pure_air_public_abi_sound certificateBytes abiBytes assignmentBytes
      rawPublicBytes source values claimed ssa certificate final
      hcheck hrows houtput
  obtain ⟨relationOutput, hrelationName, hparsed, hmatch⟩ :=
    checked_relation_ssa relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output program hrelation
  have heq : relationOutput = abiOutput :=
    Option.some.inj (hrelationName.symm.trans habiName)
  subst relationOutput
  exact ⟨hsource, abiOutput, hparsed, hmatch, habi, hwords⟩

end S31.Functional.Correspondence.GeneralLinearSSAPublicABI
