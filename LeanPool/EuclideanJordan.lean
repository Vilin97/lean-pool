/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/

module

public import LeanPool.EuclideanJordan.EuclideanJordan
public import LeanPool.EuclideanJordan.EuclideanJordan.Block
public import LeanPool.EuclideanJordan.EuclideanJordan.Bridge
public import LeanPool.EuclideanJordan.EuclideanJordan.Class
public import LeanPool.EuclideanJordan.EuclideanJordan.Connection
public import LeanPool.EuclideanJordan.EuclideanJordan.FormallyReal
public import LeanPool.EuclideanJordan.EuclideanJordan.Frame
public import LeanPool.EuclideanJordan.EuclideanJordan.FrameExists
public import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirce
public import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirceMul
public import LeanPool.EuclideanJordan.EuclideanJordan.HermitianBilin
public import LeanPool.EuclideanJordan.EuclideanJordan.HermitianCarrier
public import LeanPool.EuclideanJordan.EuclideanJordan.Order
public import LeanPool.EuclideanJordan.EuclideanJordan.OrderAuto
public import LeanPool.EuclideanJordan.EuclideanJordan.OrderUnitSpace
public import LeanPool.EuclideanJordan.EuclideanJordan.Orthogonal
public import LeanPool.EuclideanJordan.EuclideanJordan.Pattern
public import LeanPool.EuclideanJordan.EuclideanJordan.Peirce
public import LeanPool.EuclideanJordan.EuclideanJordan.PeirceMul
public import LeanPool.EuclideanJordan.EuclideanJordan.PeirceSubalgebra
public import LeanPool.EuclideanJordan.EuclideanJordan.Power
public import LeanPool.EuclideanJordan.EuclideanJordan.PowerAssoc
public import LeanPool.EuclideanJordan.EuclideanJordan.Rank
public import LeanPool.EuclideanJordan.EuclideanJordan.Spectral
public import LeanPool.EuclideanJordan.EuclideanJordan.Subalgebra
public import LeanPool.EuclideanJordan.EuclideanJordan.TraceForm
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.ContinuousLinearMap
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Basic
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.CFC
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Inner
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Jordan
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.NonSingular
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Order
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Proj
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Reindex
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Trace
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.IsMaximalSelfAdjoint
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Isometry
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.LinearEquiv
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Matrix
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Misc
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic.Commutes
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic.Commutes.Attribute
public import LeanPool.EuclideanJordan.EuclideanJordan.Witness
public import LeanPool.EuclideanJordan.FramePeirceSolution
public import LeanPool.EuclideanJordan.KoecherSolution
public import LeanPool.EuclideanJordan.SpectralSolution
public import LeanPool.EuclideanJordan.StructureSolution
public import LeanPool.EuclideanJordan.TraceFormSolution


/-!
# Euclidean Jordan algebras and the frame Peirce decomposition

Source: url:https://github.com/ehrlich-b/euclidean-jordan
Authors: Bryan Ehrlich
Status: verified
Main declarations: `EuclideanJordan.frameBlock_isInternal`
Tags: nonassociative-algebra
MSC: 17C20, 17C27, 17C37, 17C65, 17A15, 46L70
-/

@[expose] public section
