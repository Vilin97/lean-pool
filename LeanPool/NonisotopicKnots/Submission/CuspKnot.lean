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

import LeanPool.NonisotopicKnots.Submission.SphereBridge
import LeanPool.NonisotopicKnots.Submission.CuspGeom

/-!
# The smooth cusp knot `K₂`

The right-handed trefoil realized as the link of the cusp singularity `4p³ + 27q² = 0`, on the
weighted sphere `WS = {‖p‖³ + ‖q‖² = 1} ⊆ ℂ²`, pushed to `ℝ³` by the sphere bridge
`Submission.SphereBridge.wsPunctToR3`.

The link curve on `WS` is the `(2,3)`-torus curve `L θ = (a·e^{2iθ}, b·e^{3iθ})` with real
`a < 0 < b`, `4a³ + 27b² = 0` (so it lies on the cusp) and `-a³ + b² = 1` (so `WN (L θ) = 1`).
-/

namespace Submission.CuspKnot

open scoped Topology
open Metric Submission.SphereBridge Submission.CuspGeom Complex

noncomputable section

/-
The Clifford parameters of the cusp link curve.
-/
lemma exists_ab : ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ 4 * a ^ 3 + 27 * b ^ 2 = 0 ∧ -a ^ 3 + b ^ 2 = 1 := by
  -- Set $a = -\left(\frac{27}{31}\right)^{1/3}$ and $b = \frac{2}{\sqrt{31}}$.
  use -(27 / 31 : ℝ) ^ (1 / 3 : ℝ), 2 / Real.sqrt 31;
  ring_nf; norm_num;
  exact ⟨ by positivity, by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num, by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ⟩

/-- First Clifford parameter (`< 0`). -/
def aa : ℝ := exists_ab.choose
/-- Second Clifford parameter (`> 0`). -/
def bb : ℝ := exists_ab.choose_spec.choose

lemma aa_neg : aa < 0 := exists_ab.choose_spec.choose_spec.1
lemma bb_pos : 0 < bb := exists_ab.choose_spec.choose_spec.2.1
lemma cusp_eq : 4 * aa ^ 3 + 27 * bb ^ 2 = 0 := exists_ab.choose_spec.choose_spec.2.2.1
lemma wn_eq : -aa ^ 3 + bb ^ 2 = 1 := exists_ab.choose_spec.choose_spec.2.2.2

/-- The cusp link curve on the weighted sphere `WS`. -/
def Lcurve (θ : ℝ) : ℂ × ℂ :=
  (Complex.ofReal aa * Complex.exp (2 * θ * Complex.I),
    Complex.ofReal bb * Complex.exp (3 * θ * Complex.I))

lemma Lcurve_mem_WS (θ : ℝ) : Lcurve θ ∈ WS := by
  unfold Lcurve WS;
  convert wn_eq using 1;
  unfold WN; norm_num [ Complex.norm_exp, Complex.norm_exp ] ;
  rw [ abs_of_neg aa_neg ] ; ring

end

end Submission.CuspKnot