import Mathlib.Tactic

/-!
An abstract byte-input model for the proposed, *unselected* S31 BCS v2
profile. The Python prototype uses these seven domain bytes, one role byte,
an eight-byte little-endian payload length, and an eight-byte event number.
Theorems concern only input encoding. They do not refine Zig code, model
BLAKE2s as a random oracle, or establish STARK soundness.
-/

namespace S31.Gadgets.PcsFri.FramedBcsV2Encoding

def domain : List Nat := [83, 51, 49, 66, 67, 83, 50]

def u64le (n : Nat) : List Nat :=
  [n % 256, n / 256 % 256, n / 65536 % 256,
   n / 16777216 % 256, n / 4294967296 % 256,
   n / 1099511627776 % 256, n / 281474976710656 % 256,
   n / 72057594037927936 % 256]

theorem u64le_width (n : Nat) : (u64le n).length = 8 := rfl

/-- Under the checked u64 range, event numbers have unique byte encodings. -/
theorem u64le_injective_bounded (a b : Nat)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (equal : u64le a = u64le b) : a = b := by
  simp only [u64le, List.cons.injEq, and_true] at equal
  omega

def frame (role event : Nat) (payload : List Nat) : List Nat :=
  domain ++ [role] ++ u64le payload.length ++ u64le event ++ payload

theorem role_at_offset (role event : Nat) (payload : List Nat) :
    (frame role event payload)[7]? = some role := by
  simp [frame, domain]

/-- Distinct role bytes never feed the same message to the modeled hash,
regardless of event number or payload. -/
theorem different_roles_distinct_inputs
    (a b ea eb : Nat) (pa pb : List Nat) (different : a ≠ b) :
    frame a ea pa ≠ frame b eb pb := by
  intro equal
  have h := congrArg (fun bytes => bytes[7]?) equal
  change (frame a ea pa)[7]? = (frame b eb pb)[7]? at h
  rw [role_at_offset, role_at_offset] at h
  exact different (Option.some.inj h)

theorem payload_after_header (role event : Nat) (payload : List Nat) :
    (frame role event payload).drop 24 = payload := by
  simp [frame, domain, u64le]

/-- At one fixed event and role, the full byte frame retains the payload. -/
theorem fixed_role_event_payload_injective (role event : Nat)
    (left right : List Nat) (equal : frame role event left = frame role event right) :
    left = right := by
  have h := congrArg (List.drop 24) equal
  simpa [payload_after_header] using h

theorem event_bytes_after_prefix (role event : Nat) (payload : List Nat) :
    ((frame role event payload).drop 16).take 8 = u64le event := by
  simp [frame, domain, u64le]

/-- Event separation is conditional on distinct canonical u64 encodings.
The native implementation must reject event-counter wrap. -/
theorem different_event_encodings_distinct_inputs
    (role ea eb : Nat) (pa pb : List Nat)
    (different : u64le ea ≠ u64le eb) :
    frame role ea pa ≠ frame role eb pb := by
  intro equal
  have h := congrArg (fun bytes => (bytes.drop 16).take 8) equal
  change ((frame role ea pa).drop 16).take 8 =
    ((frame role eb pb).drop 16).take 8 at h
  rw [event_bytes_after_prefix, event_bytes_after_prefix] at h
  exact different h

theorem different_bounded_events_distinct_inputs
    (role ea eb : Nat) (pa pb : List Nat)
    (ha : ea < 2 ^ 64) (hb : eb < 2 ^ 64) (different : ea ≠ eb) :
    frame role ea pa ≠ frame role eb pb := by
  apply different_event_encodings_distinct_inputs
  intro equal
  exact different (u64le_injective_bounded ea eb ha hb equal)

theorem header_width (role event : Nat) (payload : List Nat) :
    (frame role event payload).length = 24 + payload.length := by
  simp [frame, domain, u64le]
  omega

end S31.Gadgets.PcsFri.FramedBcsV2Encoding
