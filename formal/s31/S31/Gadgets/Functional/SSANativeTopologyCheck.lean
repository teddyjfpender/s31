import S31.Gadgets.Functional.SSAAirRows

/-!
An executable structural checker for the bounded direct-gate SSA source
schedule. This models the part of `correspondence.py::check_gate_topology`
which pairs each checked add/pointwise-multiply instruction with exactly one
native gate, resolves its two input addresses, and requires a fresh output
address. Native gates are grouped by kind in the exported topology; the
Python checker supplies the ordered source-gate projection modeled here.

The checker is a Lean reference model. We do not prove that Python or Zig
implements it, that the preprocessed commitment authenticates the exported
topology, or that Gate lookups and PCS establish `AuthenticatedRows`. Those
are separate obligations. Under the explicit topology and authentication
premises, the accepted output has exactly the source meaning.
-/

namespace S31.Functional.SSANativeTopologyCheck

open S31.Functional.SSACertificate
open S31.Functional.SSAAirRows
open S31.Gadgets.Air.Qm31Ops

/-- The source-gate projection has `multiply = true` only for the native
`pointwise_mul` gate kind. `in0`, `in1`, and `out` are native variable IDs. -/
structure Gate where
  in0 : Nat
  in1 : Nat
  out : Nat
  multiply : Bool
deriving DecidableEq, Repr

/-- Exact local structural correspondence; all four conditions are checked
before the output address is added to the environment. -/
def Gate.matches (addresses : List Nat) (instruction : Instruction)
    (gate : Gate) : Prop :=
  instruction.id = addresses.length ∧
  addresses[instruction.lhs]? = some gate.in0 ∧
  addresses[instruction.rhs]? = some gate.in1 ∧
  gate.out ∉ addresses ∧
  gate.multiply = instruction.multiply

/-- `checkOne` is executable and fails closed on a nonfresh output, missing
operand, wrong operand address, wrong opcode, or wrong instruction ID. -/
def checkOne (addresses : List Nat) (instruction : Instruction)
    (gate : Gate) : Option (List Nat) :=
  if gate.matches addresses instruction then
    some (addresses ++ [gate.out])
  else none

theorem checkOne_iff (addresses : List Nat) (instruction : Instruction)
    (gate : Gate) (next : List Nat) :
    checkOne addresses instruction gate = some next ↔
      gate.matches addresses instruction ∧
        next = addresses ++ [gate.out] := by
  unfold checkOne
  by_cases h : gate.matches addresses instruction
  · simp [h]
  · simp [h]

/-- Consumes the entire instruction and gate lists in lockstep. An extra or
missing source gate is rejected. Padding, constant derivation, input packing,
output extraction, and column digests are checked by other Python clauses;
they are not modeled by this function. -/
def checkRows : List Nat → List Instruction → List Gate → Option (List Nat)
  | addresses, [], [] => some addresses
  | addresses, instruction :: instructions, gate :: gates => do
      let next ← checkOne addresses instruction gate
      checkRows next instructions gates
  | _, _, _ => none

/-- One executable admission decision for the Lean source fragment and its
projected native source-gate schedule. The production text parser and native
exporter are outside this Lean function. -/
def checkSourceRows (source : Source 1) (certificate : Certificate)
    (gates : List Gate) : Option (List Nat) := do
  let _ ← check source certificate
  checkRows [0] certificate.instructions gates

theorem checkSourceRows_implies_certificate (source : Source 1)
    (certificate : Certificate) (gates : List Gate)
    (finalAddresses : List Nat)
    (hcheck : checkSourceRows source certificate gates =
      some finalAddresses) :
    check source certificate = some () ∧
    checkRows [0] certificate.instructions gates =
      some finalAddresses := by
  unfold checkSourceRows at hcheck
  cases hcertificate : check source certificate with
  | none => simp [hcertificate] at hcheck
  | some unit =>
      cases unit
      constructor
      · exact hcertificate
      · simpa [hcertificate] using hcheck

/-- A native arithmetic row has the structural gate plus field witnesses.
Its values are separate from the value-free topology. -/
structure Row where
  gate : Gate
  in0 : Lanes
  in1 : Lanes
  output : Lanes

/-- The addressed Gate join must authenticate operand values against *all*
previous occurrences of the corresponding native address. The topology
checker guarantees that both operand addresses occur at their SSA indexes,
so these implications cannot be vacuous at the selected instructions. -/
def Row.authenticated (addresses : List Nat) (values : List Lanes)
    (row : Row) : Prop :=
  addresses.length = values.length ∧
  (∀ index, addresses[index]? = some row.gate.in0 →
    values[index]? = some row.in0) ∧
  (∀ index, addresses[index]? = some row.gate.in1 →
    values[index]? = some row.in1) ∧
  accepts (encode (s31Op row.gate.multiply))
    (packM31 row.in0) (packM31 row.in1) (packM31 row.output)

theorem matched_authenticated_air (addresses : List Nat)
    (values : List Lanes) (instruction : Instruction) (row : Row)
    (hmatch : row.gate.matches addresses instruction)
    (hauth : row.authenticated addresses values) :
    acceptsRow values instruction row.output := by
  obtain ⟨hid, hleftAddress, hrightAddress, _, hop⟩ := hmatch
  obtain ⟨hlen, hleftValue, hrightValue, hair⟩ := hauth
  refine ⟨row.in0, row.in1, by omega,
    hleftValue instruction.lhs hleftAddress,
    hrightValue instruction.rhs hrightAddress, ?_⟩
  rw [hop] at hair
  exact hair

/-- Authentication is staged at the native address level and does not refer
to the SSA instruction list. In a cryptographic execution, this is the
obligation of the Gate lookup, AIR and commitment, not a fact established by
the source checker. -/
inductive AuthenticatedRows : List Nat → List Lanes →
    List Row → List Nat → List Lanes → Prop where
  | done (addresses : List Nat) (values : List Lanes) :
      AuthenticatedRows addresses values [] addresses values
  | next {addresses finalAddresses : List Nat}
      {values finalValues : List Lanes}
      {row : Row} {rows : List Row}
      (hauth : row.authenticated addresses values)
      (htail : AuthenticatedRows (addresses ++ [row.gate.out])
        (values ++ [row.output]) rows finalAddresses finalValues) :
      AuthenticatedRows addresses values (row :: rows)
        finalAddresses finalValues

/-- This is the central refinement: a successful executable topology check
and an independently authenticated native row trace imply every local packed
AIR row in the checked SSA program, in exact instruction order. -/
theorem checked_rows_air {addresses finalAddresses : List Nat}
    {values finalValues : List Lanes}
    {instructions : List Instruction} {rows : List Row}
    (hcheck : checkRows addresses instructions (rows.map Row.gate) =
      some finalAddresses)
    (hauth : AuthenticatedRows addresses values rows
      finalAddresses finalValues) :
    AcceptsTrace values instructions finalValues := by
  induction hauth generalizing instructions with
  | done addresses values =>
      cases instructions with
      | nil => exact .done values
      | cons instruction rest => simp [checkRows] at hcheck
  | @next addresses finalAddresses values finalValues row rows hauth htail ih =>
      cases instructions with
      | nil => simp [checkRows] at hcheck
      | cons instruction rest =>
          simp only [List.map_cons, checkRows] at hcheck
          cases hstep : checkOne addresses instruction row.gate with
          | none => simp [hstep] at hcheck
          | some nextAddresses =>
              obtain ⟨hmatch, hnext⟩ :=
                (checkOne_iff addresses instruction row.gate nextAddresses).mp hstep
              subst nextAddresses
              have hrest :
                  checkRows (addresses ++ [row.gate.out]) rest
                    (rows.map Row.gate) = some finalAddresses := by
                simpa [hstep] using hcheck
              exact .next row.output
                (matched_authenticated_air addresses values instruction row
                  hmatch hauth)
                (ih hrest)

/-- Accepted topology has exactly one native source gate per instruction.
The source-gate projection is complete; no unmodeled source gate is admitted. -/
theorem checked_rows_length {addresses finalAddresses : List Nat}
    {instructions : List Instruction} {gates : List Gate}
    (hcheck : checkRows addresses instructions gates = some finalAddresses) :
    gates.length = instructions.length := by
  induction instructions generalizing addresses gates with
  | nil =>
      cases gates with
      | nil => rfl
      | cons gate rest => simp [checkRows] at hcheck
  | cons instruction instructions ih =>
      cases gates with
      | nil => simp [checkRows] at hcheck
      | cons gate rest =>
          simp only [checkRows] at hcheck
          cases hstep : checkOne addresses instruction gate with
          | none => simp [hstep] at hcheck
          | some next =>
              have hrest : checkRows next instructions rest =
                  some finalAddresses := by simpa [hstep] using hcheck
              simpa using congrArg Nat.succ (ih hrest)

/-- The fresh-producer check preserves uniqueness of every native address,
including the input address. -/
theorem checked_rows_nodup {addresses finalAddresses : List Nat}
    {instructions : List Instruction} {gates : List Gate}
    (hcheck : checkRows addresses instructions gates = some finalAddresses)
    (hinitial : addresses.Nodup) : finalAddresses.Nodup := by
  induction instructions generalizing addresses gates with
  | nil =>
      cases gates with
      | nil =>
          simp only [checkRows, Option.some.injEq] at hcheck
          subst finalAddresses
          exact hinitial
      | cons gate rest => simp [checkRows] at hcheck
  | cons instruction instructions ih =>
      cases gates with
      | nil => simp [checkRows] at hcheck
      | cons gate rest =>
          simp only [checkRows] at hcheck
          cases hstep : checkOne addresses instruction gate with
          | none => simp [hstep] at hcheck
          | some next =>
              obtain ⟨hmatch, hnext⟩ :=
                (checkOne_iff addresses instruction gate next).mp hstep
              subst next
              have hrest :
                  checkRows (addresses ++ [gate.out]) instructions rest =
                    some finalAddresses := by simpa [hstep] using hcheck
              have hnew : (addresses ++ [gate.out]).Nodup := by
                obtain ⟨_, _, _, hfresh, _⟩ := hmatch
                apply List.nodup_append.mpr
                refine ⟨hinitial, by simp, ?_⟩
                intro address haddress other hother heq
                simp only [List.mem_singleton] at hother
                have hotherAddress : other ∈ addresses := heq ▸ haddress
                exact hfresh (hother ▸ hotherAddress)
              exact ih hrest hnew

/-- Semantic soundness for the checked positional source fragment. -/
theorem checked_topology_source_sound (source : Source 1)
    (certificate : Certificate) (input claimed : Lanes)
    (rows : List Row) (finalAddresses : List Nat)
    (finalValues : List Lanes)
    (hcertificate : check source certificate = some ())
    (htopology : checkRows [0] certificate.instructions
      (rows.map Row.gate) = some finalAddresses)
    (hauth : AuthenticatedRows [0] [input] rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  have hair := checked_rows_air htopology hauth
  have hrun := accepted_trace_executes hair
  have hsource := checked_certificate_normalized_sound source certificate
    input hcertificate
  rw [execute_normalized_eq_execute] at hsource
  simp [execute, hrun, hclaim] at hsource
  exact hsource

/-- The composite executable check discharges both structural premises of
`checked_topology_source_sound`. Its remaining premise is the authenticated
value trace; it does not itself establish cryptographic authentication. -/
theorem checked_source_rows_sound (source : Source 1)
    (certificate : Certificate) (input claimed : Lanes)
    (rows : List Row) (finalAddresses : List Nat)
    (finalValues : List Lanes)
    (hchecked : checkSourceRows source certificate (rows.map Row.gate) =
      some finalAddresses)
    (hauth : AuthenticatedRows [0] [input] rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  obtain ⟨hcertificate, htopology⟩ :=
    checkSourceRows_implies_certificate source certificate
      (rows.map Row.gate) finalAddresses hchecked
  exact checked_topology_source_sound source certificate input claimed rows
    finalAddresses finalValues hcertificate htopology hauth hclaim

/-- A concrete two-step source projection may use nonconsecutive native
addresses; the checker relates positions to those addresses explicitly. -/
def sharedSquareGates : List Gate :=
  [{ in0 := 0, in1 := 0, out := 37, multiply := true },
   { in0 := 37, in1 := 37, out := 83, multiply := true }]

theorem shared_square_topology_accepted :
    checkRows [0] sharedSquareCertificate.instructions sharedSquareGates =
      some [0, 37, 83] := by decide

theorem shared_square_bad_topologies_rejected :
    checkRows [0] sharedSquareCertificate.instructions
      [{ in0 := 0, in1 := 0, out := 37, multiply := true },
       { in0 := 0, in1 := 37, out := 83, multiply := true }] = none ∧
    checkRows [0] sharedSquareCertificate.instructions
      [{ in0 := 0, in1 := 0, out := 37, multiply := true },
       { in0 := 37, in1 := 37, out := 37, multiply := true }] = none ∧
    checkRows [0] sharedSquareCertificate.instructions
      [{ in0 := 0, in1 := 0, out := 37, multiply := false },
       { in0 := 37, in1 := 37, out := 83, multiply := true }] = none ∧
    checkRows [0] sharedSquareCertificate.instructions
      [{ in0 := 0, in1 := 0, out := 37, multiply := true }] = none ∧
    checkRows [0] sharedSquareCertificate.instructions
      (sharedSquareGates ++
        [{ in0 := 83, in1 := 83, out := 89, multiply := true }]) = none := by
  decide

/-- Malformed instruction IDs and forward references are rejected both by
the source certificate checker and by the independent native schedule
checker. A structural native check alone is never treated as a source proof. -/
def wrongIdCertificate : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 3, lhs := 1, rhs := 1, multiply := true }],
    output := 3 }

def forwardOperandCertificate : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 2, lhs := 2, rhs := 1, multiply := true }],
    output := 2 }

theorem malformed_certificates_rejected :
    check sharedSquare wrongIdCertificate = none ∧
    checkRows [0] wrongIdCertificate.instructions sharedSquareGates = none ∧
    check sharedSquare forwardOperandCertificate = none ∧
    checkRows [0] forwardOperandCertificate.instructions sharedSquareGates =
      none := by decide

end S31.Functional.SSANativeTopologyCheck
