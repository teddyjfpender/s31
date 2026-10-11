# Selected fixed and main rows for honest direct-Gate programs

`AcceptedPublicFixedCells.lean` closes the modeled selected-row fixed-column
gap for arbitrary accepted direct-Gate source bytes and inputs.

`checked_direct_projected_physical_trace_exists` constructs a 512-row
decoded trace and proves, simultaneously:

- every installed local arithmetic root vanishes;
- every projected source, input, and output cell matches the exact fixed row,
  operation selectors, circuit addresses, and multiplicity; and
- the selected source wire equals the packed checked source result.

There are at most 41 such projected cells: up to 16 source operations plus
14 public-input and 11 public-output cells. The proof obtains distinctness
and row bounds from `direct_bytes_projected_roster`, source word bounds from
`checked_direct_source_cells_canonical`, and public word bounds from actual
checked execution. In particular, the selected output ID is shown to be an
index in the final SSA value list. No caller supplies a row count, field
bound, wire assignment, or arithmetic satisfaction premise. A `List UInt8`
corollary provides the literal-byte API.

The other 471-or-more rows are still synthetic zero-add rows. This theorem
does not assert that their fixed columns equal the native constant/padding
schedule. It does not establish Gate event balance, lookup soundness,
preprocessed commitment equality, PCS/FRI, or verifier behavior. A full
production correspondence proof must bind the native exported and committed
512-row roster to the checked model and construct/authenticate the remaining
constant and padding values.
