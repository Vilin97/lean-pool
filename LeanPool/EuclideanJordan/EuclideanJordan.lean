/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.Block
import LeanPool.EuclideanJordan.EuclideanJordan.Bridge
import LeanPool.EuclideanJordan.EuclideanJordan.Class
import LeanPool.EuclideanJordan.EuclideanJordan.Connection
import LeanPool.EuclideanJordan.EuclideanJordan.FormallyReal
import LeanPool.EuclideanJordan.EuclideanJordan.Frame
import LeanPool.EuclideanJordan.EuclideanJordan.FrameExists
import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirce
import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirceMul
import LeanPool.EuclideanJordan.EuclideanJordan.HermitianBilin
import LeanPool.EuclideanJordan.EuclideanJordan.HermitianCarrier
import LeanPool.EuclideanJordan.EuclideanJordan.Order
import LeanPool.EuclideanJordan.EuclideanJordan.OrderAuto
import LeanPool.EuclideanJordan.EuclideanJordan.OrderUnitSpace
import LeanPool.EuclideanJordan.EuclideanJordan.Orthogonal
import LeanPool.EuclideanJordan.EuclideanJordan.Pattern
import LeanPool.EuclideanJordan.EuclideanJordan.Peirce
import LeanPool.EuclideanJordan.EuclideanJordan.PeirceMul
import LeanPool.EuclideanJordan.EuclideanJordan.PeirceSubalgebra
import LeanPool.EuclideanJordan.EuclideanJordan.Power
import LeanPool.EuclideanJordan.EuclideanJordan.PowerAssoc
import LeanPool.EuclideanJordan.EuclideanJordan.Rank
import LeanPool.EuclideanJordan.EuclideanJordan.Spectral
import LeanPool.EuclideanJordan.EuclideanJordan.Subalgebra
import LeanPool.EuclideanJordan.EuclideanJordan.TraceForm
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.ContinuousLinearMap
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Basic
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.CFC
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Inner
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Jordan
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.NonSingular
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Order
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Proj
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Reindex
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Trace
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.IsMaximalSelfAdjoint
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Isometry
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.LinearEquiv
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Matrix
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Misc
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic.Commutes
import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic.Commutes.Attribute
import LeanPool.EuclideanJordan.EuclideanJordan.Witness

/-!
# Euclidean Jordan algebras in Lean 4

Root import for the library. See `README.md` for the headline results.
-/
