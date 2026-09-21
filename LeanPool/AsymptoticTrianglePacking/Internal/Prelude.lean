/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# Shared Mathlib prelude for the `LeanPool.AsymptoticTrianglePacking.Internal`/`BKLO` libraries

Every module of this package used to open with a blanket `import Mathlib`, which costs about
12 s of module-loading per file — roughly 40 % of the whole build.  This module imports exactly
the part of Mathlib that the two libraries actually use: the union, over all 577 modules, of the
Mathlib modules defining the constants that occur in their proof terms (an antichain of 26
modules, closure 4956 of Mathlib's 9981), together with `Mathlib.Tactic` for the tactic
front-ends.  Files now open with `import LeanPool.AsymptoticTrianglePacking.Internal.Prelude` instead of `import Mathlib`.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Tactic
