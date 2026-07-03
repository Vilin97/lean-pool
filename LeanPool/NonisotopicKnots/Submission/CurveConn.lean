/-
Copyright (c) 2026 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

import LeanPool.NonisotopicKnots.Submission.CurveCompl

/-!
# The complement of a `C¹` curve in `ℝ³` is path-connected

Completes the connectivity step left open in `Submission.CurveCompl`: from
`Submission.CurveCompl.badset_measure_zero` (the set of "bad" perturbation vectors has measure
zero) we pick a good vector `v`, and the bump-perturbed segment joins any two points of the
complement.
-/

open scoped Topology
open MeasureTheory

namespace Submission.CurveConn

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-
For `x, y ∉ range f`, there is a path from `x` to `y` lying in the complement of `range f`.
-/
theorem joinedIn_compl_curve (f : ℝ → R3) (hf : ContDiff ℝ 1 f) {x y : R3}
    (hx : x ∉ Set.range f) (hy : y ∉ Set.range f) :
    JoinedIn (Set.range f)ᶜ x y := by
  -- Let B := {v : R3 | ∃ r ∈ Set.Ioo (0:ℝ) 1, ∃ t, f t = (1 - r) • x + r • y + (r * (1 - r)) • v} be the bad set.
  set B := { v : R3 | ∃ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 ∧ ∃ t : ℝ, f t = (1 - r) • x + r • y + (r * (1 - r)) • v } with hB_def;
  have hB : MeasureTheory.volume B = 0 := by
    convert Submission.CurveCompl.badset_measure_zero f hf x y using 1;
  have hB_ne_univ : B ≠ Set.univ := by
    aesop;
  obtain ⟨v, hv⟩ : ∃ v, v ∉ B := by
    exact Set.nonempty_compl.2 hB_ne_univ;
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ fun t => ( 1 - t.val ) • x + t.val • y + ( t.val * ( 1 - t.val ) ) • v, _ ⟩;
  all_goals norm_num;
  fun_prop;
  intro a ha₁ ha₂ t ht; contrapose! hv; use a; cases eq_or_lt_of_le ha₁ <;> cases eq_or_lt_of_le ha₂ <;> aesop;

/-
The complement of the range of a `C¹` curve `f : ℝ → ℝ³` is path-connected.
-/
theorem compl_curve_isPathConnected (f : ℝ → R3) (hf : ContDiff ℝ 1 f) :
    IsPathConnected (Set.range f)ᶜ := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : R3, x₀ ∉ Set.range f := by
    have := Submission.CurveCompl.range_measure_zero f hf;
    exact not_forall.mp fun h => by rw [ show Set.range f = Set.univ from Set.eq_univ_of_forall h ] at this; norm_num at this;
  refine' ⟨ x₀, hx₀, _ ⟩;
  exact fun y hy => joinedIn_compl_curve f hf hx₀ hy

end Submission.CurveConn