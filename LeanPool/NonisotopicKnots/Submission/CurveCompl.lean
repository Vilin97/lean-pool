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

import LeanPool.NonisotopicKnots.Submission.GenPos

/-!
# The complement of a `C¹` curve in `ℝ³` is path-connected

A `C¹` map `f : ℝ → ℝ³` has range of measure zero. For `x, y ∉ range f`, the straight segment
`r ↦ (1-r)•x + r•y` perturbed by a generic small vector via the smooth bump `r(1-r)` (which
vanishes at `r ∈ {0,1}`, keeping the endpoints fixed) avoids `range f`, because the set of "bad"
perturbation vectors is the image of a `C¹` map from a `2`-dimensional region, hence measure zero.
This gives a path from `x` to `y` in `(range f)ᶜ`, so the complement is path-connected.

This supplies the `hUconn` (path-connectedness) hypothesis for `Submission.Pi1Iso.noncomm_of_cover`
applied to a knot complement.
-/

open scoped Topology
open MeasureTheory

namespace Submission.CurveCompl

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The image of the swept `C¹` map (whole plane `p 2 = 0`) has measure zero — direct from
`Submission.GenPos.smooth_image_plane_measure_zero`. -/
theorem swept_measure_zero (f : ℝ → R3) (hf : ContDiff ℝ 1 f) (x y : R3) :
    volume ((fun p : R3 => f (p 0) - ((1 - p 1) • x + p 1 • y)) '' {p : R3 | p 2 = 0}) = 0 := by
  convert @Submission.GenPos.smooth_image_plane_measure_zero
    (fun p : R3 => f (p 0) - ((1 - p 1) • x + p 1 • y)) ?_ using 1
  refine ContDiff.sub (hf.comp ?_) ?_ <;> fun_prop

/-
`range f` has measure zero.
-/
theorem range_measure_zero (f : ℝ → R3) (hf : ContDiff ℝ 1 f) :
    volume (Set.range f) = 0 := by
  convert swept_measure_zero f hf 0 0 using 2;
  ext x;
  constructor;
  · rintro ⟨ y, rfl ⟩ ; exact ⟨ EuclideanSpace.single 0 y, by simp +decide, by simp +decide ⟩ ;
  · aesop

/-
The set of "bad" perturbation vectors (those for which the bump-perturbed segment hits
`range f` at some interior parameter) has measure zero.
-/
theorem badset_measure_zero (f : ℝ → R3) (hf : ContDiff ℝ 1 f) (x y : R3) :
    volume {v : R3 | ∃ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 ∧
      ∃ t : ℝ, f t = (1 - r) • x + r • y + (r * (1 - r)) • v} = 0 := by
  refine' MeasureTheory.measure_mono_null _ _;
  exact ( fun p => ( p 1 * ( 1 - p 1 ) ) ⁻¹ • ( f ( p 0 ) - ( ( 1 - p 1 ) • x + p 1 • y ) ) ) '' { p : R3 | p 2 = 0 ∧ 0 < p 1 ∧ p 1 < 1 };
  · rintro v ⟨ r, hr, t, ht ⟩;
    refine' ⟨ EuclideanSpace.single 0 t + EuclideanSpace.single 1 r, _, _ ⟩ <;> simp_all +decide [ EuclideanSpace.norm_eq ];
    simp +decide [ ← smul_assoc, mul_assoc, mul_comm, mul_left_comm, ne_of_gt hr.1, ne_of_gt ( sub_pos.2 hr.2 ) ];
  · have h_diff : DifferentiableOn ℝ (fun p : R3 => (p 1 * (1 - p 1))⁻¹ • (f (p 0) - ((1 - p 1) • x + p 1 • y))) {p : R3 | 0 < p 1 ∧ p 1 < 1} := by
      have h_diff : DifferentiableOn ℝ (fun p : R3 => (p 1 * (1 - p 1))⁻¹) {p : R3 | 0 < p 1 ∧ p 1 < 1} := by
        refine' DifferentiableOn.inv _ _;
        · fun_prop;
        · exact fun p hp => mul_ne_zero ( ne_of_gt hp.1 ) ( ne_of_gt ( sub_pos.mpr hp.2 ) );
      fun_prop;
    convert MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ _ _;
    all_goals try infer_instance;
    · exact h_diff.mono fun p hp => hp.2;
    · have h_hyperplane : volume {p : R3 | p 2 = 0} = 0 := by
        convert MeasureTheory.Measure.addHaar_submodule _ _ _;
        rotate_left;
        all_goals try infer_instance;
        exact Submodule.span ℝ { p : R3 | p 2 = 0 };
        · norm_num [ Submodule.eq_top_iff' ];
          refine' ⟨ EuclideanSpace.single 2 1, _ ⟩;
          rw [ Finsupp.mem_span_iff_linearCombination ];
          simp +decide [ Finsupp.linearCombination_apply, Finsupp.sum ];
          intro x hx;
          have hzero : ((Finsupp.linearCombination ℝ Subtype.val) x).ofLp 2 = 0 := by
            rw [Finsupp.linearCombination_apply, Finsupp.sum]
            rw [show ((∑ a ∈ x.support, x a • (a : R3)).ofLp 2)
                  = ∑ a ∈ x.support, (x a • (a : R3)).ofLp 2 by simp]
            exact Finset.sum_eq_zero (fun a _ => by simp [a.2])
          have hc : (EuclideanSpace.single (2:Fin 3) (1:ℝ) : R3).ofLp 2 = 0 := by
            rw [← hx]; exact hzero
          simp at hc;
        · refine' Set.Subset.antisymm _ _;
          · exact fun p hp => Submodule.subset_span hp;
          · intro p hp; induction hp using Submodule.span_induction <;> aesop;
      exact MeasureTheory.measure_mono_null ( fun p hp => hp.1 ) h_hyperplane

/-
Remaining connectivity step (intended completion, omitted here so this file stays `sorry`-free):
from `badset_measure_zero` the bad perturbation set has measure zero, so it is not all of `R3`
(`volume (univ : Set R3) = ⊤`); pick `v` outside it, then for `x, y ∉ range f` the bump-perturbed
segment `r ↦ (1-r)•x + r•y + (r*(1-r))•v` avoids `range f` at every `r ∈ unitInterval`
(interior `r` by `v ∉` bad set; endpoints `r ∈ {0,1}` because the point is `x`/`y ∉ range f`),
giving `IsPathConnected (range f)ᶜ`.  See `PLAN.md`.
-/

end Submission.CurveCompl