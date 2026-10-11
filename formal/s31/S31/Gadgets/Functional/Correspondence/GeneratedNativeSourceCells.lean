import S31.Gadgets.Functional.Correspondence.GeneratedMutationRows
import S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows

/-!
Native `inspect-topology` source-row cells for four checked direct-Gate
programs. The generator checks the complete sealed topology and
compares each captured eight-column row with an independently parsed
positional DAG. These literal cell values are then checked against
Lean's exact source-byte parser and modeled physical row projection.
Proof acceptance and PCS authentication are not inferred here.
-/

namespace S31.Functional.Correspondence.GeneratedNativeSourceCells

open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAAliasTextBytes
open S31.Functional.Correspondence.GeneratedMutationRows
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.SourceDeterminedDirectRows

-- Stwo engine gitlink: fde847ea374ade2ae07ef5b3a42ba07e15655b64
-- Native exporter source SHA-256: cfad27778fe15f052492e461f74229b4c6a5b7bfde661b4817be629e6c008e6e
-- Relation lowering source SHA-256: 7a1c8047468eef045e56eff786ec31c49a980f387f2e824bf94dbe481445bd6c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

-- 00:direct; source SHA-256: 501cb43a6a9bbbb5dc7b2f6823904bd2ca7ab4b49b0e91256e516569d1b25c78
-- Normalized JSON SHA-256: ceb73709951b292b529de8acb1e406d51f35770277a87c54579fa84d464547e9
-- Native exporter binary SHA-256: b35e10bc4a78af682566cbb8091b2b40387dcc2b7b0f653d1aac5702c67b1588
-- Native full fixed-column SHA-256: 2cd5f1f13a18d4fc353d81800722d0645a696853bfa84f22a84ccd5504c7f1f3
-- Native preprocessed root: a471bbffd8633107e132098ab26f672af50e00dd34601cc431910284caf295d0
def case00NativeCells : List ColumnCell := [
  {traceRow := 503, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 22, in1 := 22, out := 23, mults := 4},
]
theorem case00_source_to_native_cells :
    checkAliasCanonical case00Bytes case00NormalizedBytes
      case00CanonicalBytes = some case00Certificate ∧
    case00NativeCells =
      expectedCells case00Certificate (compiledAddRows case00Certificate) := by
  constructor
  · exact case00CanonicalChecks.1
  · decide

-- 07:aliases; source SHA-256: ce48022e44d29e6252ea497a6db79f05b52def51bfccd3790beb69b2e7ce68df
-- Normalized JSON SHA-256: 2012ca4ec0abd00740f143548bafda1436025faad3f73ae7fcf224c094d370c4
-- Native exporter binary SHA-256: ba3e57858d212ca4be0d1463fdbc260479cbf2d2b25169914bf5e7492f630197
-- Native full fixed-column SHA-256: 0789309140783ee672a829b442c5782489c729804851a94e0b267f73dad74b52
-- Native preprocessed root: 791ada776d80d9b30c5b0217cae11135c67658e1822296564efe3e591cb62ef8
def case07NativeCells : List ColumnCell := [
  {traceRow := 3, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 22, out := 23, mults := 2},
  {traceRow := 4, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 23, out := 24, mults := 2},
  {traceRow := 501, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 24, in1 := 24, out := 25, mults := 5},
  {traceRow := 5, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 25, in1 := 25, out := 26, mults := 6},
  {traceRow := 6, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 25, out := 27, mults := 1},
  {traceRow := 7, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 26, in1 := 27, out := 28, mults := 0},
  {traceRow := 502, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 25, in1 := 25, out := 29, mults := 0},
  {traceRow := 503, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 23, in1 := 26, out := 30, mults := 0},
]
theorem case07_source_to_native_cells :
    checkAliasCanonical case07Bytes case07NormalizedBytes
      case07CanonicalBytes = some case07Certificate ∧
    case07NativeCells =
      expectedCells case07Certificate (compiledAddRows case07Certificate) := by
  constructor
  · exact case07CanonicalChecks.1
  · decide

-- 14:direct; source SHA-256: 0bdbffaab7517baca6c65d95882896f4471935dd9481f29ad93eece34aaa5c77
-- Normalized JSON SHA-256: 1361eec6b99f11427517e3f5a932186c20b279b9bfce1ae73fa5c4ebf98199cb
-- Native exporter binary SHA-256: 4f38fa4333667f76dfc74d9fb8673b3d09fd9a694ec9d3f79f1326b069c1aec5
-- Native full fixed-column SHA-256: 3661ba5dc0977313ba155f9ec56e0958cddf148a7470b03badc3ea4bb45472d6
-- Native preprocessed root: 4b3e99310e4b074a8184875dddb4f96c262e9f55fbed5199f4c0bf527cf38323
def case14NativeCells : List ColumnCell := [
  {traceRow := 496, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 22, in1 := 22, out := 23, mults := 7},
  {traceRow := 3, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 23, out := 24, mults := 3},
  {traceRow := 497, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 22, in1 := 24, out := 25, mults := 5},
  {traceRow := 4, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 23, in1 := 25, out := 26, mults := 3},
  {traceRow := 498, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 24, in1 := 26, out := 27, mults := 2},
  {traceRow := 499, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 23, in1 := 23, out := 28, mults := 2},
  {traceRow := 500, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 25, in1 := 28, out := 29, mults := 1},
  {traceRow := 5, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 25, in1 := 25, out := 30, mults := 0},
  {traceRow := 6, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 25, out := 31, mults := 1},
  {traceRow := 7, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 23, in1 := 23, out := 32, mults := 1},
  {traceRow := 501, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 28, in1 := 32, out := 33, mults := 0},
  {traceRow := 502, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 23, in1 := 27, out := 34, mults := 0},
  {traceRow := 8, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 26, in1 := 26, out := 35, mults := 0},
  {traceRow := 503, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 27, in1 := 29, out := 36, mults := 0},
  {traceRow := 9, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 24, in1 := 31, out := 37, mults := 4},
]
theorem case14_source_to_native_cells :
    checkAliasCanonical case14Bytes case14NormalizedBytes
      case14CanonicalBytes = some case14Certificate ∧
    case14NativeCells =
      expectedCells case14Certificate (compiledAddRows case14Certificate) := by
  constructor
  · exact case14CanonicalChecks.1
  · decide

-- 15:comments; source SHA-256: 5e10f20690686bf4c4552cb580f2cc7802fd353e23117569e5b868443d9efbaf
-- Normalized JSON SHA-256: b1d54bd5351e7af7ec26b1c2b20bf6fea0870162fa5817c7ec9e6536d81112d1
-- Native exporter binary SHA-256: f9e080da5561106c61ed9ebb8b0ed19bf913c1dc648bbacd69c2362280b98615
-- Native full fixed-column SHA-256: 551da763f7b741f730bfeec37ac09bc8b077394c1594e7a98ac2b2b81c3e4bc6
-- Native preprocessed root: ea35a9cd72113d3617e344570047f1ae96d5cb3a726c8dfce9cd58095ae201df
def case16NativeCells : List ColumnCell := [
  {traceRow := 3, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 22, out := 23, mults := 5},
  {traceRow := 4, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 23, in1 := 23, out := 24, mults := 5},
  {traceRow := 5, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 23, in1 := 24, out := 25, mults := 2},
  {traceRow := 498, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 22, in1 := 23, out := 26, mults := 6},
  {traceRow := 6, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 24, in1 := 24, out := 27, mults := 2},
  {traceRow := 7, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 26, out := 28, mults := 1},
  {traceRow := 499, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 24, in1 := 24, out := 29, mults := 2},
  {traceRow := 8, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 27, out := 30, mults := 4},
  {traceRow := 500, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 26, in1 := 26, out := 31, mults := 1},
  {traceRow := 9, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 23, in1 := 26, out := 32, mults := 1},
  {traceRow := 501, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 26, in1 := 29, out := 33, mults := 2},
  {traceRow := 10, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 25, in1 := 29, out := 34, mults := 0},
  {traceRow := 502, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 26, in1 := 33, out := 35, mults := 0},
  {traceRow := 11, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 28, in1 := 31, out := 36, mults := 0},
  {traceRow := 503, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1, in0 := 32, in1 := 33, out := 37, mults := 0},
  {traceRow := 12, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 25, in1 := 27, out := 38, mults := 0},
]
theorem case16_source_to_native_cells :
    checkAliasCanonical case16Bytes case16NormalizedBytes
      case16CanonicalBytes = some case16Certificate ∧
    case16NativeCells =
      expectedCells case16Certificate (compiledAddRows case16Certificate) := by
  constructor
  · exact case16CanonicalChecks.1
  · decide

end S31.Functional.Correspondence.GeneratedNativeSourceCells
