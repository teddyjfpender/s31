import S31.Gadgets.PcsFri.PairedBatchXdm04Certificate

/-!
Exact XDM03 node-preimage framing used by the experimental XDM04 sparse wire.
The digest is abstract but constrained to 32 output bytes. The native Zig
`hashLeaf`, `hashUpper`, and `hashInserted` share these tags and row encoding;
the independent Python differential checker tests the concrete BLAKE2s and
transposed-index behavior. Neither source pins nor differential tests prove a
Zig operational semantics theorem or BLAKE2s collision resistance.
-/

namespace S31.Gadgets.PcsFri.PairedBatchXdm04Framing

open S31.Gadgets.PcsFri.PairedBatchSourceCustody
open S31.Gadgets.PcsFri.PairedBatchXdm04Certificate
open S31.Gadgets.PcsFri.PairedBatchXdm04Topology

abbrev Bytes := List UInt8

/-- An abstract 256-bit digest, to be instantiated with BLAKE2s only after
its concrete implementation and 32-byte output have been related to Zig. -/
structure Digest32 where
  run : Bytes → Bytes
  width : ∀ input, (run input).length = 32

def u16LE (n : Nat) : Bytes :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256)]

def u32LE (n : Nat) : Bytes :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256),
    UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]

/-- Native `hashValues`: a 16-bit little-endian column count followed by
each canonical M31 representative as a 32-bit little-endian word. XDM04
admits only nonempty rows of at most 64 columns. -/
def rowBytes (row : List Base) : Bytes :=
  u16LE row.length ++ row.flatMap (fun x => u32LE x.val)

theorem rowBytes_length (row : List Base) :
    (rowBytes row).length = 2 + 4 * row.length := by
  induction row with
  | nil => simp [rowBytes, u16LE]
  | cons head tail ih =>
      simp [rowBytes, u16LE, u32LE] at ih ⊢
      omega

def leafTag : Bytes := "S31XDL03".toUTF8.data.toList
def upperTag : Bytes := "S31XDU03".toUTF8.data.toList
def insertedTag : Bytes := "S31XDI03".toUTF8.data.toList

def leafPreimage (row : List Base) : Bytes := leafTag ++ rowBytes row
def upperPreimage (left right : Bytes) : Bytes := upperTag ++ left ++ right

/-- Inserted source nodes hash an *upper parent digest* before appending the
height's row. They do not append child hashes directly after `S31XDI03`. -/
def insertedPreimage (d : Digest32) (left right : Bytes) (row : List Base) : Bytes :=
  insertedTag ++ d.run (upperPreimage left right) ++ rowBytes row

theorem insertedPreimage_length (d : Digest32) (left right : Bytes)
    (row : List Base) :
    (insertedPreimage d left right row).length =
      insertedTag.length + 32 + 2 + 4 * row.length := by
  simp [insertedPreimage, rowBytes_length, d.width]
  omega

def framedLeaf (d : Digest32) (row : List Base) : Bytes :=
  d.run (leafPreimage row)

def framedUpper (d : Digest32) (pair : Bytes × Bytes) : Bytes :=
  d.run (upperPreimage pair.1 pair.2)

def framedInserted (d : Digest32) (pair : Bytes × Bytes)
    (row : List Base) : Bytes :=
  d.run (insertedPreimage d pair.1 pair.2 row)

/-- The generic certificate checker instantiated with the exact XDM03
preimage tags, canonical little-endian row framing, and nested inserted-node
hash. `checkOpening` also checks transposed-index path conversion. -/
def checkFramedOpening (d : Digest32) (cert : OpeningCertificate Bytes) : Bool :=
  checkOpening (framedLeaf d) (framedInserted d) (framedUpper d) cert

theorem checkFramedOpening_sound (d : Digest32)
    (cert : OpeningCertificate Bytes)
    (accepted : checkFramedOpening d cert = true) :
    acceptedMixedOpening (framedLeaf d) (framedInserted d) (framedUpper d)
      cert.root cert.level cert.binaryPosition cert.input cert.steps := by
  exact checkOpening_sound (framedLeaf d) (framedInserted d) (framedUpper d)
    cert accepted

theorem checkFramedOpening_native_replay (d : Digest32)
    (cert : OpeningCertificate Bytes)
    (accepted : checkFramedOpening d cert = true) :
    S31.Gadgets.PcsFri.PairedBatchXdm04Topology.nativeMixedRoot
      (framedUpper d) (framedInserted d) cert.level cert.nativeIndex
      (S31.Gadgets.PcsFri.PairedBatchXdm04Topology.taggedNodeHash
        (framedLeaf d) (framedInserted d) cert.input) cert.steps = cert.root := by
  exact checkOpening_native_replay (framedLeaf d) (framedInserted d)
    (framedUpper d) cert accepted

end S31.Gadgets.PcsFri.PairedBatchXdm04Framing
