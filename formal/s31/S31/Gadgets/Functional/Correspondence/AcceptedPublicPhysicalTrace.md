# Honest arithmetic trace for projected direct-Gate rows

`AcceptedPublicPhysicalTrace.lean` concatenates the source cells with all
fourteen public-input and eleven public-output cells. The source grammar
permits at most sixteen instructions, so the selected roster has at most
`16 + 14 + 11 = 41` cells in the 512-row trace.

For **every** admitted source byte stream and **every** input,
`checked_direct_projected_trace_exists` constructs one address-coherent wire
assignment and a decoded 512-row trace. All installed local arithmetic
polynomial roots vanish. The proof uses the interpreter-derived source
values, six honest pack intermediates, four scalar input copies, four raw
input identity rows, four output masks, three inverse-basis multiplies, and
four public output copies. It obtains the source output from the checked
source denotation. `checked_u8_direct_projected_trace_exists` exposes the
same result for literal `List UInt8` source and normalized bytes.

The rows outside the selected 41-or-fewer cells remain synthetic
zero-plus-zero additions. Thus the theorem does **not** claim that the
remaining fixed columns match the native constant and padding schedule. It
also does not prove ideal Gate event balance, lookup soundness, commitment
opening, PCS/FRI, or native verifier behavior. The independent full-row role
theorem classifies the 512 positions; exact constant-row values and a
production-fixed-column join are separate obligations.
