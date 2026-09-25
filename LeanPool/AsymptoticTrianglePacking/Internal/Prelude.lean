/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Finset.Functor
public import Mathlib.Data.List.GetD
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic

/-!
# Shared Mathlib prelude for the extracted asymptotic triangle-packing modules

Common imports for the modules in this package. Individual modules may import additional
Mathlib files for their own proofs.
-/
