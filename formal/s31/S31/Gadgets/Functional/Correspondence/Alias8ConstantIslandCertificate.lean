import S31.Gadgets.Functional.Correspondence.NativeConstantIslandCertificate
import S31.Gadgets.Functional.Correspondence.GeneratedAlias8NativeFixture
import S31.Gadgets.Functional.Correspondence.GeneratedMutationRows

/-! Exact finite nonvacuity check for the case07 native constant island.
The 479 exported cells and coherent values are diagnostic fixture data.
This proves modeled local arithmetic, not PCS opening correspondence. -/

namespace S31.Functional.Correspondence.Alias8ConstantIslandCertificate

open S31.Gadgets.Packed
open S31.Functional.SSAAirColumnCells
open S31.Functional.Correspondence.GeneratedMutationRows
open S31.Functional.Correspondence.NativeConstantIslandCertificate

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def constantCells : List ColumnCell := GeneratedAlias8NativeFixture.constantCells
def nativeValues : List Quad := GeneratedAlias8NativeFixture.nativeValues

theorem constant_cells_count : constantCells.length = 479 :=
  GeneratedAlias8NativeFixture.constant_cells_length
theorem value_table_count : nativeValues.length = 512 :=
  GeneratedAlias8NativeFixture.native_values_length

private def cellPass (cell : ColumnCell) : Bool :=
  decide (ConstantCellSound case07Certificate nativeValues cell)

private theorem all_chunked (xs : List ColumnCell) (p : ColumnCell → Bool)
    (hfirst : (xs.take 16).all p = true)
    (hrest : (xs.drop 16).all p = true) :
    xs.all p = true := by
  have h : xs.take 16 ++ xs.drop 16 = xs := List.take_append_drop 16 xs
  rw [← h, List.all_append]
  rw [hfirst, hrest]
  rfl

private theorem cells_all_464 :
    (constantCells.drop 464).all cellPass = true := by
  decide

private theorem cells_all_448 :
    (constantCells.drop 448).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 448) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_464

private theorem cells_all_432 :
    (constantCells.drop 432).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 432) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_448

private theorem cells_all_416 :
    (constantCells.drop 416).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 416) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_432

private theorem cells_all_400 :
    (constantCells.drop 400).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 400) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_416

private theorem cells_all_384 :
    (constantCells.drop 384).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 384) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_400

private theorem cells_all_368 :
    (constantCells.drop 368).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 368) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_384

private theorem cells_all_352 :
    (constantCells.drop 352).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 352) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_368

private theorem cells_all_336 :
    (constantCells.drop 336).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 336) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_352

private theorem cells_all_320 :
    (constantCells.drop 320).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 320) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_336

private theorem cells_all_304 :
    (constantCells.drop 304).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 304) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_320

private theorem cells_all_288 :
    (constantCells.drop 288).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 288) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_304

private theorem cells_all_272 :
    (constantCells.drop 272).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 272) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_288

private theorem cells_all_256 :
    (constantCells.drop 256).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 256) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_272

private theorem cells_all_240 :
    (constantCells.drop 240).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 240) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_256

private theorem cells_all_224 :
    (constantCells.drop 224).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 224) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_240

private theorem cells_all_208 :
    (constantCells.drop 208).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 208) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_224

private theorem cells_all_192 :
    (constantCells.drop 192).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 192) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_208

private theorem cells_all_176 :
    (constantCells.drop 176).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 176) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_192

private theorem cells_all_160 :
    (constantCells.drop 160).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 160) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_176

private theorem cells_all_144 :
    (constantCells.drop 144).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 144) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_160

private theorem cells_all_128 :
    (constantCells.drop 128).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 128) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_144

private theorem cells_all_112 :
    (constantCells.drop 112).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 112) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_128

private theorem cells_all_96 :
    (constantCells.drop 96).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 96) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_112

private theorem cells_all_80 :
    (constantCells.drop 80).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 80) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_96

private theorem cells_all_64 :
    (constantCells.drop 64).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 64) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_80

private theorem cells_all_48 :
    (constantCells.drop 48).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 48) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_64

private theorem cells_all_32 :
    (constantCells.drop 32).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 32) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_48

private theorem cells_all_16 :
    (constantCells.drop 16).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 16) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_32

private theorem cells_all_0 :
    (constantCells.drop 0).all cellPass = true := by
  apply all_chunked (xs := constantCells.drop 0) (p := cellPass)
  · decide
  · simpa [List.drop_drop, Nat.add_comm] using cells_all_16

private theorem cells_all : constantCells.all cellPass = true := by
  simpa using cells_all_0

private theorem rows_correct :
    constantCells.map ColumnCell.traceRow =
      constantPositions case07Certificate := by decide

private theorem outputs_nodup : (constantCells.map ColumnCell.out).Nodup := by
  decide

private theorem seed_values : SeedValues case07Certificate nativeValues := by
  decide

private theorem seed_producers :
    (seedProducerAddresses case07Certificate).all
      (fun address => decide (address ∈ constantCells.map ColumnCell.out)) = true := by
  decide

/-- Every case07 native constant/padding cell passes the executable role,
canonical-address, seed, and nine-root arithmetic certificate. -/
theorem alias8_constant_check :
    check case07Certificate constantCells nativeValues = true := by
  have hvalid : Valid case07Certificate constantCells nativeValues :=
    ⟨rows_correct, cells_all, outputs_nodup, seed_values, seed_producers⟩
  exact decide_eq_true hvalid

end S31.Functional.Correspondence.Alias8ConstantIslandCertificate
