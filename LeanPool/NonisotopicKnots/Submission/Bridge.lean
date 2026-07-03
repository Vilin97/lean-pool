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

import LeanPool.NonisotopicKnots.Submission.Helpers

/-!
# An explicit algebraic equation cutting out the trefoil

This file records a concrete, reusable step toward the *geometric bridge* needed by
`Submission.Helpers.trefoil_compl_pi1_noncomm` (see `PLAN.md`): an explicit polynomial map
`Fbridge : R3 → ℂ` (with real-polynomial real/imaginary parts in the three coordinates) that
**vanishes on the image of the right-handed trefoil**.

The construction comes from the complex packaging of the trig trefoil.  Writing `w = exp (i t)`
on the unit circle, the trefoil coordinates satisfy

* `ζ := y + i x = w - 2 w⁻²`,
* `W₃ := (5 - x² - y²)/4 - i z = w³`   (using `x² + y² = 5 - 4 cos 3t` and `z = - sin 3t`).

Then the identity `w² · (w - 2 w⁻²) = w³ - 2` cubes to `w⁶ (w - 2w⁻²)³ = (w³ - 2)³`, i.e.

  `W₃² · ζ³ = (W₃ - 2)³`,

so `Fbridge := W₃² ζ³ - (W₃ - 2)³` vanishes identically along the trefoil.  This is the explicit
"discriminant-type" equation realizing the trefoil as the locus where a continuously varying
cubic acquires a repeated root (the right-hand cube root structure is exactly the cusp model
`x² + y³ = 0` of the `(2,3)` torus knot); it is the concrete object on which any future
covering-space / monodromy bridge can be built.
-/

namespace Submission.Bridge

open LeanEval.KnotTheory Submission.Helpers

/-- The explicit algebraic map cutting out the trefoil.  With `ζ = y + i x` and
`W₃ = (5 - x² - y²)/4 - i z`, this is `W₃² ζ³ - (W₃ - 2)³`; it vanishes on the trefoil. -/
noncomputable def Fbridge (p : R3) : ℂ :=
  let ζ : ℂ := (p 1 : ℂ) + Complex.I * (p 0 : ℂ)
  let W3 : ℂ := (((5 - (p 0) ^ 2 - (p 1) ^ 2) / 4 : ℝ) : ℂ) - Complex.I * ((p 2 : ℝ) : ℂ)
  W3 ^ 2 * ζ ^ 3 - (W3 - 2) ^ 3

/-
The combination `ζ = y + i x` equals `w - 2 w⁻²` along the trefoil, where `w = exp (i t)`.
-/
lemma zeta_trefoil (t : ℝ) :
    ((trefoilCurve t) 1 : ℂ) + Complex.I * ((trefoilCurve t) 0 : ℂ)
      = Complex.exp (t * Complex.I) - 2 * Complex.exp (t * Complex.I) ^ (-2 : ℤ) := by
  unfold trefoilCurve;
  norm_cast ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, pow_two ];
  norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin, Real.cos_two_mul, Real.sin_two_mul ] ; ring_nf;
  simp +decide [ Real.sin_sq ] ; ring

/-
The combination `W₃ = (5 - x² - y²)/4 - i z` equals `w³` along the trefoil.
-/
lemma W3_trefoil (t : ℝ) :
    (((5 - ((trefoilCurve t) 0) ^ 2 - ((trefoilCurve t) 1) ^ 2) / 4 : ℝ) : ℂ)
        - Complex.I * (((trefoilCurve t) 2 : ℝ) : ℂ)
      = Complex.exp (t * Complex.I) ^ 3 := by
  unfold trefoilCurve; norm_num [ Complex.ext_iff, pow_three ] ; ring_nf;
  norm_cast; norm_num [ show t * 3 = 2 * t + t by ring, show t * 2 = 2 * t by ring, Real.sin_add, Real.sin_two_mul, Real.cos_add, Real.cos_two_mul ] ; ring_nf ; norm_num;
  simp +decide [ Rat.divInt_eq_div ] ; ring_nf ; norm_num [ Real.sin_sq ] ; ring_nf ; (
  exact ⟨ trivial, by rw [ show Real.sin t ^ 3 = Real.sin t * Real.sin t ^ 2 by ring, Real.sin_sq ] ; ring ⟩);

/-- `Fbridge` is continuous (a polynomial in the three real coordinates of the point). -/
lemma continuous_Fbridge : Continuous Fbridge := by
  unfold Fbridge
  have h0 : Continuous fun p : R3 => (p 0 : ℝ) := by
    simpa using (EuclideanSpace.proj (0 : Fin 3)).continuous
  have h1 : Continuous fun p : R3 => (p 1 : ℝ) := by
    simpa using (EuclideanSpace.proj (1 : Fin 3)).continuous
  have h2 : Continuous fun p : R3 => (p 2 : ℝ) := by
    simpa using (EuclideanSpace.proj (2 : Fin 3)).continuous
  fun_prop

/-
**The explicit equation cutting out the trefoil.** `Fbridge` vanishes on the trefoil image.
-/
theorem Fbridge_trefoil (t : ℝ) : Fbridge (trefoilCurve t) = 0 := by
  -- By definition of `Fbridge`, we know that `Fbridge (trefoilCurve t) = 0` for all `t` because `trefoilCurve t` lies on the trefoil curve.
  unfold Fbridge
  simp [zeta_trefoil];
  rw [ show ( 5 - ( trefoilCurve t |> fun x => x.ofLp 0 ) ^ 2 - ( trefoilCurve t |> fun x => x.ofLp 1 ) ^ 2 : ℂ ) / 4 - Complex.I * ( trefoilCurve t |> fun x => x.ofLp 2 ) = Complex.exp ( t * Complex.I ) ^ 3 by
        convert W3_trefoil t using 1;
        norm_num [ Complex.ext_iff ] ];
  field_simp;
  ring

end Submission.Bridge