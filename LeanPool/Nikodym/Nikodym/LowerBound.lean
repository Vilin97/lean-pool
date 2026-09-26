/-
Copyright (c) 2026 The Nikodym contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Hans Yu, Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Assembly
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChange
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChangePrime
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ComponentDegree
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Degree
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Dimension
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.DimensionExtra
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.FreeFiber
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedLemmas
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedNorm
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HilbertPolynomial
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Homogenization
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HypersurfaceDegree
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LocalParameters
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.NormalizationSetting
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.PolyAsymptotics
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ProperCut
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Transfer
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra
public import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.BinomialGap
public import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.Multiplicity
public import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.WeightedSelection
public import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic
public import LeanPool.Nikodym.Nikodym.LowerBound.CarrierBound
public import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Components
public import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Curves
public import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Points
public import LeanPool.Nikodym.Nikodym.LowerBound.Counting
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.CRT
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Jets
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.OmittedConditions
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Reduction
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.DegreeUpper
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Gap
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Normalized
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Shadow
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.StandardMonomials
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert
public import LeanPool.Nikodym.Nikodym.LowerBound.InterpolationCut
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.LowerBound
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Jets
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Vanishing
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines
public import LeanPool.Nikodym.Nikodym.LowerBound.Main
public import LeanPool.Nikodym.Nikodym.LowerBound.PolynomialSpaces
public import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily

/-! Supporting modules for The sharp finite-field Nikodym exponent. -/

