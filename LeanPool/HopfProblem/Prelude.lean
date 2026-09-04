/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.Star
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.WhitneyEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.Topology.Sheaves.EtaleSpace
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Hopf problem: prelude

Supporting definitions and proofs for this stage of the six-sphere construction.
-/
