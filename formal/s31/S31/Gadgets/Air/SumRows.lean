import S31.Gadgets.Air.SimdChunks

/-!
Local AIR equations used by `relation_compiler.sumLanes`: an optional mask
for a short final packed word, the exact pairwise packed-addition schedule,
multiplication by the QM31 dual projection constant, and a pointwise
base-coordinate mask. Compiler emission, input packing and Gate lookup wiring
are separate obligations.
-/

namespace S31.Gadgets.Air.SumRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

def sumCoords (x : Quad) : F := x.a + x.b + x.c + x.d

theorem sumCoords_add (x y : Quad) :
    sumCoords (Packed.add x y) = sumCoords x + sumCoords y := by
  simp [sumCoords, Packed.add]
  ring

/-- A locally accepted packed addition preserves the sum of all four M31
coordinates for arbitrary trace output values. -/
theorem accepted_add_sum (x y output : Quad)
    (h : accepts (encode .add) x y output) :
    sumCoords output = sumCoords x + sumCoords y := by
  rw [(accepts_encoded .add x y output).mp h]
  exact sumCoords_add x y

def sumWords (words : List Quad) : F :=
  (words.map sumCoords).sum

/-- One pass of the compiler's left-to-right pairwise reduction. An odd
last word is carried unchanged; each pair has one accepted add row. -/
inductive PairRows : List Quad → List Quad → Prop where
  | nil : PairRows [] []
  | one (x : Quad) : PairRows [x] [x]
  | pair (x y output : Quad) {rest next : List Quad}
      (hrow : accepts (encode .add) x y output)
      (hrest : PairRows rest next) :
      PairRows (x :: y :: rest) (output :: next)

/-- No assignment of intermediate add rows can change the coordinate sum
through a pairwise reduction pass. -/
theorem pairRows_sum {before after : List Quad}
    (h : PairRows before after) :
    sumWords after = sumWords before := by
  induction h with
  | nil => rfl
  | one _ => rfl
  | pair x y output hrow hrest ih =>
      simp only [sumWords, List.map_cons, List.sum_cons] at ih ⊢
      rw [accepted_add_sum x y output hrow]
      rw [← ih]
      ring

def pairRound : List Quad → List Quad
  | [] => []
  | [x] => [x]
  | x :: y :: rest => Packed.add x y :: pairRound rest

theorem pairRound_rows : (words : List Quad) → PairRows words (pairRound words)
  | [] => .nil
  | [x] => .one x
  | x :: y :: rest =>
      .pair x y (Packed.add x y) (honest_row _ _ _)
        (pairRound_rows rest)

theorem pairRound_length_le : (words : List Quad) →
    (pairRound words).length ≤ words.length
  | [] => by simp [pairRound]
  | [x] => by simp [pairRound]
  | x :: y :: rest => by
      have h := pairRound_length_le rest
      simp only [pairRound, List.length_cons] at h ⊢
      omega

theorem pairRound_length_lt {words : List Quad}
    (h : 1 < words.length) :
    (pairRound words).length < words.length := by
  cases words with
  | nil => simp at h
  | cons x rest =>
      cases rest with
      | nil => simp at h
      | cons y tail =>
          have htail := pairRound_length_le tail
          simp only [pairRound, List.length_cons]
          omega

theorem pairRound_nonempty {words : List Quad}
    (h : words ≠ []) : pairRound words ≠ [] := by
  cases words with
  | nil => contradiction
  | cons x rest =>
      cases rest <;> simp [pairRound]

/-- Repeated pairwise passes until one packed word remains. -/
inductive ReduceRows : List Quad → Quad → Prop where
  | single (x : Quad) : ReduceRows [x] x
  | round {before after : List Quad} {output : Quad}
      (hsize : 1 < before.length)
      (hpass : PairRows before after)
      (hrest : ReduceRows after output) : ReduceRows before output

theorem reduceRows_sum {before : List Quad} {output : Quad}
    (h : ReduceRows before output) :
    sumCoords output = sumWords before := by
  induction h with
  | single x => simp [sumWords]
  | round _ hpass _ ih => exact ih.trans (pairRows_sum hpass)

/-- Every nonempty packed-word list has an honest witness for the compiler's
pairwise reduction schedule, including odd-width carry rounds. -/
theorem reduceRows_complete (words : List Quad) (hne : words ≠ []) :
    ∃ output : Quad, ReduceRows words output := by
  have go : ∀ length : Nat, ∀ xs : List Quad,
      xs.length = length → xs ≠ [] →
      ∃ output : Quad, ReduceRows xs output := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro xs hlength hxs
        cases xs with
        | nil => contradiction
        | cons x rest =>
            cases rest with
            | nil => exact ⟨x, .single x⟩
            | cons y tail =>
                let before : List Quad := x :: y :: tail
                let after := pairRound before
                have hsmaller : after.length < length := by
                  rw [← hlength]
                  exact pairRound_length_lt (by simp [before])
                have hafter : after ≠ [] :=
                  pairRound_nonempty (by simp [before])
                obtain ⟨output, hreduce⟩ :=
                  ih after.length hsmaller after rfl hafter
                exact ⟨output,
                  .round (by simp) (pairRound_rows before) hreduce⟩
  exact go words.length words rfl hne

def activeSum (active : Nat) (x : Quad) : F :=
  (if 0 < active then x.a else 0) +
    (if 1 < active then x.b else 0) +
    (if 2 < active then x.c else 0) +
    (if 3 < active then x.d else 0)

/-- The final-word mask makes every inactive coordinate contribute zero,
regardless of its unconstrained input value. -/
theorem accepted_mask_sum (active : Nat) (input output : Quad)
    (h : accepts (encode .pointwiseMul) input (mask active) output) :
    sumCoords output = activeSum active input := by
  rw [(accepts_encoded .pointwiseMul input (mask active) output).mp h]
  simp [sumCoords, activeSum, evaluate, Packed.pointwise, mask]

def sourceSum {n : Nat} (values : Fin n → S31.M31) : F :=
  (List.ofFn (fun i => S31.Field.toZMod (values i))).sum

/-- Source lanes in a short final word contribute exactly their canonical
M31 values. Inactive padding disappears from the masked sum. -/
theorem activeSum_pad4 {n : Nat} (hn : n ≤ 4)
    (values : Fin n → S31.M31) (tail : Fin 4 → S31.M31) :
    activeSum n (packM31 (SimdChunks.pad4 hn values tail)) =
      sourceSum values := by
  interval_cases n <;>
    simp [activeSum, sourceSum, packM31, SimdChunks.pad4,
      List.ofFn, List.sum, Fin.foldr, Fin.foldr.loop] <;> ring

theorem sumCoords_packM31 (values : Fin 4 → S31.M31) :
    sumCoords (packM31 values) = sourceSum values := by
  simp [sumCoords, sourceSum, packM31,
    List.ofFn, List.sum, Fin.foldr, Fin.foldr.loop]
  ring

def fieldSumList (values : List S31.M31) : F :=
  (values.map S31.Field.toZMod).sum

theorem fieldSumList_foldl (values : List S31.M31)
    (start : S31.M31) :
    S31.Field.toZMod (values.foldl (· + ·) start) =
      S31.Field.toZMod start + fieldSumList values := by
  induction values generalizing start with
  | nil => simp [fieldSumList]
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [fieldSumList, List.map_cons, List.sum_cons,
        S31.Field.toZMod_add]
      ring

theorem fieldSumList_eq_foldl (values : List S31.M31) :
    fieldSumList values =
      S31.Field.toZMod (values.foldl (· + ·) 0) := by
  have h := fieldSumList_foldl values 0
  simpa [S31.Field.toZMod_zero] using h.symm

/-- Full four-lane input words are already packed. A short final word is
masked by an accepted pointwise-multiply row before it joins the reduction.
Each lane of its unmasked input padding remains arbitrary. -/
inductive InputWords : List S31.M31 → List Quad → Prop where
  | nil : InputWords [] []
  | short {n : Nat} (hn : n < 4) (hpos : 0 < n)
      (values : Fin n → S31.M31) (tail : Fin 4 → S31.M31)
      (output : Quad)
      (hmask : accepts (encode .pointwiseMul)
        (packM31 (SimdChunks.pad4 (Nat.le_of_lt hn) values tail))
        (mask n) output) :
      InputWords (List.ofFn values) [output]
  | full (values : Fin 4 → S31.M31)
      {rest : List S31.M31} {words : List Quad}
      (hrest : InputWords rest words) :
      InputWords (List.ofFn values ++ rest) (packM31 values :: words)

/-- Every accepted input packing and final-word mask has exactly the sum
of the original canonical source lanes. -/
theorem inputWords_sum {values : List S31.M31} {words : List Quad}
    (h : InputWords values words) :
    sumWords words = fieldSumList values := by
  induction h with
  | nil => rfl
  | short hn _ values tail output hmask =>
      have hsum := accepted_mask_sum _ _ _ hmask
      rw [activeSum_pad4 (Nat.le_of_lt hn)] at hsum
      simpa [sumWords, fieldSumList, sourceSum] using hsum
  | full values hrest ih =>
      simp only [sumWords, List.map_cons, List.sum_cons,
        fieldSumList, List.map_append, List.sum_append]
      rw [sumCoords_packM31]
      simpa [sourceSum, fieldSumList] using congrArg
        (fun total : F => sourceSum values + total) ih

private theorem short_input_complete (values : List S31.M31)
    (hpos : 0 < values.length) (hlt : values.length < 4) :
    ∃ words : List Quad, InputWords values words := by
  let lanes : Fin values.length → S31.M31 := values.get
  let tail : Fin 4 → S31.M31 := fun _ => 0
  let output := evaluate .pointwiseMul
    (packM31 (SimdChunks.pad4 (Nat.le_of_lt hlt) lanes tail))
    (mask values.length)
  have hrow : accepts (encode .pointwiseMul)
      (packM31 (SimdChunks.pad4 (Nat.le_of_lt hlt) lanes tail))
      (mask values.length) output := honest_row _ _ _
  refine ⟨[output], ?_⟩
  simpa [lanes, List.ofFn_get] using
    InputWords.short hlt hpos lanes tail output hrow

/-- Every list of source M31 lanes has an honest packing witness, with one
masked final word only when the length is not divisible by four. -/
theorem inputWords_complete : (values : List S31.M31) →
    ∃ words : List Quad, InputWords values words
  | [] => ⟨[], .nil⟩
  | [a] => short_input_complete [a] (by simp) (by simp)
  | [a, b] => short_input_complete [a, b] (by simp) (by simp)
  | [a, b, c] => short_input_complete [a, b, c] (by simp) (by simp)
  | a :: b :: c :: d :: rest => by
      let first : List S31.M31 := [a, b, c, d]
      let lanes : Fin 4 → S31.M31 := first.get
      obtain ⟨words, hrest⟩ := inputWords_complete rest
      refine ⟨packM31 lanes :: words, ?_⟩
      simpa [first, lanes, List.ofFn_get] using InputWords.full lanes hrest

theorem inputWords_nonempty {values : List S31.M31}
    {words : List Quad} (h : InputWords values words)
    (hvalues : values ≠ []) : words ≠ [] := by
  cases h with
  | nil => contradiction
  | short => simp
  | full => simp

/-- The two projection rows extract precisely the sum of all four packed
coordinates into the base limb. Intermediate values are existential row
witnesses; no honest-value assumption is used in the soundness direction. -/
theorem projection_rows_iff (input output : Quad) :
    (∃ projected : Quad,
      accepts (encode .mul) input dual projected ∧
      accepts (encode .pointwiseMul) projected (base 1) output) ↔
    output = base (sumCoords input) := by
  constructor
  · rintro ⟨projected, hm, hp⟩
    have hm' := (accepts_encoded .mul input dual projected).mp hm
    have hp' := (accepts_encoded .pointwiseMul projected (base 1) output).mp hp
    rw [hm'] at hp'
    rw [hp']
    simpa [evaluate, sumCoords] using sum_projection input
  · intro hout
    let projected := evaluate .mul input dual
    refine ⟨projected, honest_row _ _ _, ?_⟩
    apply (accepts_encoded .pointwiseMul projected (base 1) output).mpr
    rw [hout]
    simpa [projected, evaluate, sumCoords] using (sum_projection input).symm

/-- The literal QM31 word emitted by Zig is the same dual projection
constant used in the row theorem. -/
theorem projection_literal_rows_iff (input output : Quad) :
    (∃ projected : Quad,
      accepts (encode .mul) input
        ⟨1, 2147483646, 858993459, 1717986917⟩ projected ∧
      accepts (encode .pointwiseMul) projected (base 1) output) ↔
    output = base (sumCoords input) := by
  simpa only [dual_literal] using projection_rows_iff input output

/-- The mask and projection rows for one short packed word accept a claimed
base-field sum exactly when it is the sum of its active source lanes. The
actual compiler returns the input directly when its length is one; this
template describes the row path used for larger reductions. -/
theorem short_word_sum_rows_iff {n : Nat} (hn : n ≤ 4)
    (values : Fin n → S31.M31) (tail : Fin 4 → S31.M31)
    (claimed : S31.M31) :
    (∃ masked projected output : Quad,
      accepts (encode .pointwiseMul)
        (packM31 (SimdChunks.pad4 hn values tail)) (mask n) masked ∧
      accepts (encode .mul) masked dual projected ∧
      accepts (encode .pointwiseMul) projected (base 1) output ∧
      output.a = S31.Field.toZMod claimed) ↔
    S31.Field.toZMod claimed = sourceSum values := by
  constructor
  · rintro ⟨masked, projected, output, hmask, hmul, hproject, hclaim⟩
    have hsum := accepted_mask_sum n
      (packM31 (SimdChunks.pad4 hn values tail)) masked hmask
    have hout := (projection_rows_iff masked output).mp
      ⟨projected, hmul, hproject⟩
    rw [hout] at hclaim
    change sumCoords masked = S31.Field.toZMod claimed at hclaim
    rw [hsum, activeSum_pad4] at hclaim
    exact hclaim.symm
  · intro h
    let input := packM31 (SimdChunks.pad4 hn values tail)
    let masked := evaluate .pointwiseMul input (mask n)
    have hmask : accepts (encode .pointwiseMul) input (mask n) masked :=
      honest_row _ _ _
    let output := base (sumCoords masked)
    obtain ⟨projected, hmul, hproject⟩ :=
      (projection_rows_iff masked output).mpr rfl
    refine ⟨masked, projected, output, hmask, hmul, hproject, ?_⟩
    have hsum := accepted_mask_sum n input masked hmask
    change sumCoords masked = S31.Field.toZMod claimed
    rw [hsum]
    simpa [input, activeSum_pad4] using h.symm

/-- The row relation for the nontrivial `sum_lanes` path. It includes the
final-word mask, the compiler's pairwise reduction schedule, and the two
QM31 projection rows. A one-lane source is an alias in Zig and is handled
separately from this row relation. -/
def sumLanesRows (values : List S31.M31) (claimed : S31.M31) : Prop :=
  ∃ words : List Quad, ∃ reduced projected output : Quad,
    InputWords values words ∧
    ReduceRows words reduced ∧
    accepts (encode .mul) reduced dual projected ∧
    accepts (encode .pointwiseMul) projected (base 1) output ∧
    output.a = S31.Field.toZMod claimed

/-- Arbitrary trace assignments satisfying every local row cannot change
the sum of the source's active M31 lanes. -/
theorem sumLanesRows_sound (values : List S31.M31)
    (claimed : S31.M31) (h : sumLanesRows values claimed) :
    S31.Field.toZMod claimed = fieldSumList values := by
  obtain ⟨words, reduced, projected, output,
    hinput, hreduce, hmul, hproject, hclaim⟩ := h
  have hsum := inputWords_sum hinput
  have hreduced := reduceRows_sum hreduce
  have houtput := (projection_rows_iff reduced output).mp
    ⟨projected, hmul, hproject⟩
  rw [houtput] at hclaim
  change sumCoords reduced = S31.Field.toZMod claimed at hclaim
  rw [hreduced, hsum] at hclaim
  exact hclaim.symm

/-- Any correct claim for a nonempty source array has honest mask,
pairwise-addition, and projection row witnesses. -/
theorem sumLanesRows_complete (values : List S31.M31)
    (claimed : S31.M31) (hne : values ≠ [])
    (hclaim : S31.Field.toZMod claimed = fieldSumList values) :
    sumLanesRows values claimed := by
  obtain ⟨words, hinput⟩ := inputWords_complete values
  have hwords := inputWords_nonempty hinput hne
  obtain ⟨reduced, hreduce⟩ := reduceRows_complete words hwords
  let output := base (sumCoords reduced)
  obtain ⟨projected, hmul, hproject⟩ :=
    (projection_rows_iff reduced output).mpr rfl
  refine ⟨words, reduced, projected, output,
    hinput, hreduce, hmul, hproject, ?_⟩
  change sumCoords reduced = S31.Field.toZMod claimed
  rw [reduceRows_sum hreduce, inputWords_sum hinput]
  exact hclaim.symm

/-- The nontrivial reduction path is sound and complete for every nonempty
array length, with arbitrary inactive padding in the last packed word. -/
theorem sumLanesRows_iff (values : List S31.M31)
    (claimed : S31.M31) (hne : values ≠ []) :
    sumLanesRows values claimed ↔
      S31.Field.toZMod claimed = fieldSumList values :=
  ⟨sumLanesRows_sound values claimed,
   sumLanesRows_complete values claimed hne⟩

def normalizedSumNode : S31.Node :=
  { name := "out", op := .sum_lanes, lhs := some "input" }

def normalizedSumEnv (values : List S31.M31) : S31.Env :=
  [("input", ⟨.m31, values⟩)]

theorem normalizedSumNode_shape (values : List S31.M31) :
    S31.inferNode ((normalizedSumEnv values).map
      (fun (name, value) => (name, value.shape))) normalizedSumNode =
      .ok ⟨.m31, 1⟩ := by
  have hkind : (S31.Kind.m31 == S31.Kind.m31) = true := rfl
  simp [normalizedSumNode, normalizedSumEnv, S31.inferNode,
    S31.Node.metadataValid, S31.Node.fields, S31.shapeOperand,
    S31.expectShape, S31.lookup, S31.Value.shape, S31.need,
    S31.require, Bind.bind, Except.bind, Except.map, hkind]
  rfl

theorem normalizedSumNode_eval (values : List S31.M31) :
    S31.evaluateNode (normalizedSumEnv values) normalizedSumNode =
      .ok ⟨.m31, [values.foldl (· + ·) 0]⟩ := by
  unfold S31.evaluateNode
  rw [normalizedSumNode_shape]
  have hshape : ((⟨.m31, 1⟩ : S31.Shape) == ⟨.m31, 1⟩) = true := by decide
  simp [normalizedSumNode, normalizedSumEnv, S31.valueOperand,
    S31.lookup, S31.Value.shape, S31.Value.valid,
    S31.require, Bind.bind, Except.bind]
  rfl

/-- The entire masked packing, pairwise reduction and projection row
relation accepts exactly the executable normalized `sum_lanes` result for
every nonempty input array. -/
theorem sumLanesRows_iff_evaluateNode (values : List S31.M31)
    (claimed : S31.M31) (hne : values ≠ []) :
    sumLanesRows values claimed ↔
      S31.evaluateNode (normalizedSumEnv values) normalizedSumNode =
        .ok ⟨.m31, [claimed]⟩ := by
  rw [sumLanesRows_iff values claimed hne,
    fieldSumList_eq_foldl, normalizedSumNode_eval]
  constructor
  · intro h
    have hc := S31.Field.toZMod_injective h
    simp [hc]
  · intro h
    have hwords : [values.foldl (· + ·) 0] = [claimed] :=
      congrArg S31.Value.words (Except.ok.inj h)
    have hc := (List.cons.inj hwords).1
    exact congrArg S31.Field.toZMod hc.symm

/-- The compiler aliases a one-lane input without emitting reduction rows.
Longer inputs use the masked pairwise reduction relation above. -/
def compiledSumLanesRows (values : List S31.M31)
    (claimed : S31.M31) : Prop :=
  if values.length = 1 then values = [claimed]
  else sumLanesRows values claimed

theorem compiledSumLanesRows_iff_evaluateNode
    (values : List S31.M31) (claimed : S31.M31)
    (hne : values ≠ []) :
    compiledSumLanesRows values claimed ↔
      S31.evaluateNode (normalizedSumEnv values) normalizedSumNode =
        .ok ⟨.m31, [claimed]⟩ := by
  cases values with
  | nil => contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          rw [normalizedSumNode_eval]
          simp [compiledSumLanesRows]
      | cons second tail =>
          have hlength : (first :: second :: tail).length ≠ 1 := by simp
          simp only [compiledSumLanesRows, if_neg hlength]
          exact sumLanesRows_iff_evaluateNode _ _ (by simp)

def fiveLaneExample : List S31.M31 :=
  [RiscvRefinement.M31.reduce 3, RiscvRefinement.M31.reduce 5,
   RiscvRefinement.M31.reduce 7, RiscvRefinement.M31.reduce 11,
   RiscvRefinement.M31.reduce 13]

theorem five_lane_honest :
    compiledSumLanesRows fiveLaneExample
      (RiscvRefinement.M31.reduce 39) := by
  change sumLanesRows fiveLaneExample (RiscvRefinement.M31.reduce 39)
  apply sumLanesRows_complete
  · decide
  · decide

theorem five_lane_forged_rejected :
    ¬ compiledSumLanesRows fiveLaneExample
        (RiscvRefinement.M31.reduce 40) := by
  intro h
  change sumLanesRows fiveLaneExample (RiscvRefinement.M31.reduce 40) at h
  have hsum := sumLanesRows_sound _ _ h
  exact (by decide : ¬ S31.Field.toZMod (RiscvRefinement.M31.reduce 40) =
    fieldSumList fiveLaneExample) hsum

end S31.Gadgets.Air.SumRows
