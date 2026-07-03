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

import LeanPool.NonisotopicKnots.Submission.CuspKnot
import LeanPool.NonisotopicKnots.Submission.SphereBridge

/-!
# Parametrization of the cusp on the weighted sphere

Every point of the weighted sphere `WS` lying on the cusp `{4p³ + 27q² = 0}` is `Lcurve θ` for
some `θ`. Together with `Lcurve_mem_WS` this identifies the cusp slice of `WS` with the image of
`Lcurve`.
-/

namespace Submission.CuspParam

open Submission.CuspKnot Submission.CuspGeom Submission.SphereBridge Complex

/-
The defining cube value of the first Clifford parameter.
-/
lemma aa_cube : aa ^ 3 = -27 / 31 := by
  linarith [ cusp_eq, wn_eq ]

/-
The defining square value of the second Clifford parameter.
-/
lemma bb_sq : bb ^ 2 = 4 / 31 := by
  grind +suggestions

/-
Every cusp point of the weighted sphere is on the curve `Lcurve`.
-/
theorem cusp_param (p : ℂ × ℂ) (hWS : WN p = 1) (hcusp : 4 * p.1 ^ 3 + 27 * p.2 ^ 2 = 0) :
    ∃ θ : ℝ, Lcurve θ = p := by
  -- Let $s := -3 * p.2 / (2 * p.1)$. Then $s \neq 0$ and $p = (-3s^2, 2s^3)$.
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ≠ 0 ∧ p.1 = -3 * s^2 ∧ p.2 = 2 * s^3 := by
    by_cases h1 : p.1 = 0;
    · unfold WN at hWS; aesop;
    · -- Let $s := -3 * p.2 / (2 * p.1)$. Then $s \neq 0$ and $p = (-3s^2, 2s^3)$ by definition.
      use -3 * p.2 / (2 * p.1);
      grind +splitImp;
  -- Using `aa_cube` and `bb_sq`, we have `aa = -3 * ‖s‖^2` and `bb = 2 * ‖s‖^3`.
  have haa : aa = -3 * ‖s‖^2 := by
    have haa : aa^3 = (-3 * ‖s‖^2)^3 := by
      have h_norm_s : ‖s‖^6 = 1 / 31 := by
        unfold WN at hWS; simp_all +decide [ Complex.norm_exp ] ; ring;
        linarith;
      grind +suggestions;
    by_contra h_contra;
    exact h_contra ( by nlinarith [ sq_nonneg ( aa + ( -3 * ‖s‖ ^ 2 ) ), mul_self_pos.2 ( sub_ne_zero_of_ne h_contra ) ] )
  have hbb : bb = 2 * ‖s‖^3 := by
    have hbb : bb^2 = 4 * ‖s‖^6 := by
      grind +suggestions;
    nlinarith [ show 0 < bb by exact bb_pos, show 0 ≤ ‖s‖ ^ 3 by positivity ];
  use Complex.arg s;
  ext <;> simp_all +decide [ Lcurve ];
  · conv_rhs => rw [ ← Complex.norm_mul_exp_arg_mul_I s ] ; ring;
    rw [ ← Complex.exp_nat_mul ] ; ring;
  · conv_rhs => rw [ ← Complex.norm_mul_exp_arg_mul_I s ] ; ring;
    rw [ ← Complex.exp_nat_mul ] ; ring

end Submission.CuspParam