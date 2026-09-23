/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.Floor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Tactic

/-!
# Shared Mathlib prelude for the extracted asymptotic triangle-packing modules

Common imports for the modules in this package. Individual modules may import additional
Mathlib files for their own proofs.
-/
