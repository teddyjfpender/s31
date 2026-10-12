import S31.Gadgets.Air.DirectGateEvaluatorCells

/-!
The nine direct Gate arithmetic constraints as polynomials over any
commutative ring. In the native verifier, trace-column reads at the OODS
point are QM31 values, although the committed columns are M31 polynomials.
This model deliberately has no interaction cells, challenges, or PCS claim.
-/

namespace S31.Gadgets.Air.DirectGatePolynomial

open S31.Gadgets.Packed

structure ArithmeticCells (K : Type*) where
  localFixed : Fin 8 → K
  main : Fin 12 → K

/-- The captured AIR's local fixed read order is
`[add, mul, pointwise, sub, in0Addr, in1Addr, outAddr, mult]`. -/
def modeledArithmetic {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) : List K :=
  let addFlag := cells.localFixed 0
  let subFlag := cells.localFixed 3
  let mulFlag := cells.localFixed 1
  let pointwiseFlag := cells.localFixed 2
  let x₀ := cells.main 0
  let x₁ := cells.main 1
  let x₂ := cells.main 2
  let x₃ := cells.main 3
  let y₀ := cells.main 4
  let y₁ := cells.main 5
  let y₂ := cells.main 6
  let y₃ := cells.main 7
  let product₀ := x₀ * y₀ - x₁ * y₁ + 2 * (x₂ * y₂ - x₃ * y₃) -
    x₂ * y₃ - x₃ * y₂
  let product₁ := x₀ * y₁ + x₁ * y₀ + 2 * (x₂ * y₃ + x₃ * y₂) +
    x₂ * y₂ - x₃ * y₃
  let product₂ := x₀ * y₂ - x₁ * y₃ + x₂ * y₀ - x₃ * y₁
  let product₃ := x₀ * y₃ + x₁ * y₂ + x₂ * y₁ + x₃ * y₀
  [addFlag + subFlag + mulFlag + pointwiseFlag - 1,
   addFlag * (addFlag - 1),
   subFlag * (subFlag - 1),
   mulFlag * (mulFlag - 1),
   pointwiseFlag * (pointwiseFlag - 1),
   cells.main 8 - (product₀ * mulFlag + (x₀ + y₀) * addFlag +
     (x₀ - y₀) * subFlag + x₀ * y₀ * pointwiseFlag),
   cells.main 9 - (product₁ * mulFlag + (x₁ + y₁) * addFlag +
     (x₁ - y₁) * subFlag + x₁ * y₁ * pointwiseFlag),
   cells.main 10 - (product₂ * mulFlag + (x₂ + y₂) * addFlag +
     (x₂ - y₂) * subFlag + x₂ * y₂ * pointwiseFlag),
   cells.main 11 - (product₃ * mulFlag + (x₃ + y₃) * addFlag +
     (x₃ - y₃) * subFlag + x₃ * y₃ * pointwiseFlag)]

def fromM31Cells (cells : DirectGateEvaluatorCells.Cells) : ArithmeticCells F :=
  ⟨cells.localFixed, cells.main⟩

/-- The generic polynomial model specializes to the already proved M31
`DirectGateEvaluatorCells.arithmetic` model, with no row restriction. -/
theorem modeled_m31_eq_pure (cells : DirectGateEvaluatorCells.Cells) :
    modeledArithmetic (fromM31Cells cells) =
      DirectGateEvaluatorCells.arithmetic cells := by
  simp [modeledArithmetic, fromM31Cells,
    DirectGateEvaluatorCells.arithmetic,
    DirectGateEvaluatorCells.decodedRow,
    DirectGateEvaluatorCells.semanticFixed,
    S31.Gadgets.Air.NativeQm31Air.residuals,
    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal]

end S31.Gadgets.Air.DirectGatePolynomial
