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

import LeanPool.NonisotopicKnots.Submission.VanKampen

/-!
# 2-D Lebesgue subdivision of a square homotopy — scaffolding for van Kampen injectivity

This file develops the 2-dimensional grid-subdivision infrastructure needed for the injectivity
("amalgamation") half of the van Kampen theorem
(`Submission.VanKampenInj.loop_null_in_U_of_null_in_X`).

The 1-D file `Submission.VanKampen` subdivides a *loop* `I → X` along an open cover `{U, V}`.
Here we subdivide a *square map* `I × I → X`: there is `N` and a uniform grid of mesh `1/N`
such that every closed grid cell `[i/N,(i+1)/N] × [j/N,(j+1)/N]` is mapped by the square entirely
into `U` or entirely into `V`.

The key Mathlib input is `lebesgue_number_lemma_of_metric` applied to the compact square
`I × I` with the open cover `{F⁻¹U, F⁻¹V}`.
-/

open scoped Topology unitInterval

namespace Submission.VanKampen2D

/-- A point of the closed unit square given by clamped real coordinates. -/
noncomputable def sqPt (a b : ℝ) : (↑unitInterval × ↑unitInterval : Type) :=
  (Set.projIcc 0 1 (by norm_num) a, Set.projIcc 0 1 (by norm_num) b)

/-
**2-D Lebesgue grid subdivision.**
For a continuous map `F` of the closed unit square into `X`, and an open cover `X = U ∪ V`, there
is a grid resolution `N ≥ 1` such that every grid cell of mesh `1/N` is mapped by `F` entirely
into `U` or entirely into `V`.  More precisely there is a labelling `W : ℕ → ℕ → Set X` with each
`W i j ∈ {U, V}` and `F (a, b) ∈ W i j` whenever `(a, b)` lies in the closed cell
`[i/N,(i+1)/N] × [j/N,(j+1)/N]` (clamped into the square).
-/
theorem grid_subdivision {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ)
    (F : C(↑unitInterval × ↑unitInterval, X)) :
    ∃ (N : ℕ) (W : ℕ → ℕ → Set X), 1 ≤ N ∧
      (∀ i j, W i j = U ∨ W i j = V) ∧
      (∀ (i j : ℕ) (a b : ℝ),
        a ∈ Set.Icc ((i : ℝ) / N) ((i + 1 : ℝ) / N) →
        b ∈ Set.Icc ((j : ℝ) / N) ((j + 1 : ℝ) / N) →
        F (sqPt a b) ∈ W i j) := by
  -- By the Lebesgue number lemma, there exists a δ > 0 such that every ball of radius δ in I × I is contained in either F⁻¹' U or F⁻¹' V.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ p : unitInterval × unitInterval, ∃ c ∈ [U, V], Metric.ball p δ ⊆ F ⁻¹' c := by
    have := @lebesgue_number_lemma_of_metric;
    convert this ( isCompact_univ : IsCompact ( Set.univ : Set ( unitInterval × unitInterval ) ) ) ( fun i : Bool => ?_ ) ( ?_ ) using 1;
    rotate_left;
    use fun i => if i then F ⁻¹' U else F ⁻¹' V;
    · split_ifs <;> [ exact F.continuous.isOpen_preimage _ hUo; exact F.continuous.isOpen_preimage _ hVo ];
    · simp_all +decide [ Set.ext_iff ];
      exact fun a ha ha' b hb hb' => Or.symm ( hcov _ );
    · simp +decide [ Set.ext_iff ];
      grind;
  -- Choose N such that 2 / N < δ.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ 2 / (N : ℝ) < δ := by
    exact ⟨ ⌊δ⁻¹ * 2⌋₊ + 1, Nat.succ_pos _, by rw [ div_lt_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( δ⁻¹ * 2 ), mul_inv_cancel₀ hδ_pos.ne' ] ⟩;
  refine' ⟨ N, fun i j => Classical.choose ( hδ ( sqPt ( ( i + 1 / 2 ) / N ) ( ( j + 1 / 2 ) / N ) ) ), hN.1, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  · grind;
  · intro i j a b ha hb ha' hb'
    have h_dist : dist (sqPt a b) (sqPt ((i + 1 / 2) / N) ((j + 1 / 2) / N)) ≤ 2 / (N : ℝ) := by
      refine' max_le _ _ <;> norm_num [ sqPt ] at *;
      · refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩ <;> norm_num [ Set.projIcc ] at *;
        · grind +locals;
        · grind +qlia;
      · refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩ <;> norm_num [ Set.projIcc ] at *;
        · grind;
        · grind +revert;
    grind +suggestions

/-
**Square map ⟹ set-constrained null-homotopy.**
A continuous square map `F : I × I → X` with `F(0,·) = γ`, `F(1,·) = x₀` (top constant) and
`F(·,0) = F(·,1) = x₀` (both sides constant) packages into a `Path.Homotopy γ (Path.refl x₀)`.
If moreover `F` lands in a set `S`, the resulting homotopy has image in `S`.

This reduces the van Kampen injectivity keystone to *constructing* such a square map landing in
`U`.
-/
theorem homotopy_in_set_of_square {X : Type*} [TopologicalSpace X] {x₀ : X} (γ : Path x₀ x₀)
    (F : C(↑unitInterval × ↑unitInterval, X))
    (hbot : ∀ s, F (0, s) = γ s) (htop : ∀ s, F (1, s) = x₀)
    (hleft : ∀ t, F (t, 0) = x₀) (hright : ∀ t, F (t, 1) = x₀)
    {S : Set X} (hS : ∀ p, F p ∈ S) :
    ∃ H : Path.Homotopy γ (Path.refl x₀), ∀ p, H p ∈ S := by
  refine' ⟨ _, _ ⟩;
  refine' { toContinuousMap := F, .. };
  all_goals simp_all +decide [ Path.refl_apply ];
  exact hS

end Submission.VanKampen2D