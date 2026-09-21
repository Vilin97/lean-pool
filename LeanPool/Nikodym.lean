/-
Copyright (c) 2026 Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Hans Yu, Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Hans Yu, Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Construction.Arith
import LeanPool.Nikodym.Nikodym.Construction.Count
import LeanPool.Nikodym.Nikodym.Construction.Digits
import LeanPool.Nikodym.Nikodym.Construction.Fibers
import LeanPool.Nikodym.Nikodym.Construction.Main
import LeanPool.Nikodym.Nikodym.Construction.Parameters
import LeanPool.Nikodym.Nikodym.Construction.ProductCriterion
import LeanPool.Nikodym.Nikodym.Construction.Scaffold
import LeanPool.Nikodym.Nikodym.Construction.Tangent
import LeanPool.Nikodym.Nikodym.Construction
import LeanPool.Nikodym.Nikodym.Definition
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Assembly
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChange
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.BaseChangePrime
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ComponentDegree
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Degree
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Dimension
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.DimensionExtra
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.FreeFiber
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedLemmas
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedNorm
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HilbertPolynomial
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Homogenization
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HypersurfaceDegree
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LocalParameters
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.NormalizationSetting
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.PolyAsymptotics
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ProperCut
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Transfer
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.BinomialGap
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.Multiplicity
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.WeightedSelection
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic
import LeanPool.Nikodym.Nikodym.LowerBound.CarrierBound
import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Components
import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Curves
import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Points
import LeanPool.Nikodym.Nikodym.LowerBound.Counting
import LeanPool.Nikodym.Nikodym.LowerBound.Grid.CRT
import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Jets
import LeanPool.Nikodym.Nikodym.LowerBound.Grid.OmittedConditions
import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Reduction
import LeanPool.Nikodym.Nikodym.LowerBound.Grid
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.DegreeUpper
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Gap
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Normalized
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Shadow
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.StandardMonomials
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert
import LeanPool.Nikodym.Nikodym.LowerBound.InterpolationCut
import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs
import LeanPool.Nikodym.Nikodym.LowerBound.Jets.LowerBound
import LeanPool.Nikodym.Nikodym.LowerBound.Jets
import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic
import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Jets
import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Vanishing
import LeanPool.Nikodym.Nikodym.LowerBound.Lines
import LeanPool.Nikodym.Nikodym.LowerBound.Main
import LeanPool.Nikodym.Nikodym.LowerBound.PolynomialSpaces
import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily
import LeanPool.Nikodym.Nikodym.LowerBound
import LeanPool.Nikodym.Nikodym.Main
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Basis
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Kummer
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Legendre
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Norm
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Order
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Scaffold
import LeanPool.Nikodym.Nikodym.MultiQuadratic
import LeanPool.Nikodym.Nikodym
import LeanPool.Nikodym.Solution

/-!
# The sharp finite-field Nikodym exponent

Source: url:https://github.com/shengtongzhang-alt/nikodym
Authors: Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Hans Yu, Shengtong Zhang
Status: verified
Main declarations: `Nikodym.card_ge_pow_sub`, `Nikodym.exists_isNikodym_card_le`
Tags: combinatorics, finite-fields, nikodym-sets
MSC: 05B25, 11T99
-/
