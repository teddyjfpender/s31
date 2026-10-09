import S31.Gadgets.Arithmetic
import S31.Gadgets.Air.Qm31Ops
import S31.Gadgets.Air.QuadField
import S31.Gadgets.Air.SimdChunks
import S31.Gadgets.Air.FunctionalBridge
import S31.Gadgets.Air.SelectRows
import S31.Gadgets.Air.BooleanRows
import S31.Gadgets.Air.BitRows
import S31.Gadgets.Air.ZeroRows
import S31.Gadgets.Air.InverseRows
import S31.Gadgets.Air.UnpackRows
import S31.Gadgets.Air.SumRows
import S31.Gadgets.Air.MixRows
import S31.Gadgets.Air.GateLookup
import S31.Gadgets.Bindings
import S31.Gadgets.BuilderValidity
import S31.Gadgets.CompactTarget
import S31.Gadgets.HashEncoding
import S31.Gadgets.HashBuilder
import S31.Gadgets.Functional.Graph
import S31.Gadgets.Functional.Outputs
import S31.Gadgets.Functional.Arrays
import S31.Gadgets.Functional.ArrayNodes
import S31.Gadgets.Functional.ArithmeticNodes
import S31.Gadgets.Functional.Assertions
import S31.Gadgets.Functional.Conditional
import S31.Gadgets.Functional.ArrayConditional
import S31.Gadgets.Functional.Effects
import S31.Gadgets.U16Selection
import S31.Gadgets.Packed

/-! Local constraint relations, with arbitrary-witness soundness and honest
witness completeness. All range and representation premises are explicit. -/
