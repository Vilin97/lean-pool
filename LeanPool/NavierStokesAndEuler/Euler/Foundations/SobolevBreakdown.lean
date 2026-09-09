/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.BreakdownCriterion

@[expose] public section

noncomputable section

namespace EulerSobolevBreakdown

open EulerSmoothLimit EulerSobolev EulerSmoothSobolev EulerEnergyBootstrap
open Filter Set MeasureTheory
open scoped ContDiff Topology

/-- The final comparison argument, with an actual physical H³ norm. A quadratic
energy estimate and vanishing initial error rule out divergent origin gradients
against a smooth reference solution on a compact time interval. -/
theorem no_gradient_escape_from_sobolev_energy
    (u : ℝ → Space → Space) (U : ℕ → ℝ → Space → Space)
    (X X' : ℕ → ℝ → ℝ) (ε times : ℕ → ℝ) (C S : ℝ)
    (hC : 0 < C) (hS : 0 ≤ S) (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (nhds 0))
    (hu : ∀ t ∈ Icc 0 S, ContDiff ℝ ∞ (u t))
    (hU : ∀ n t, t ∈ Icc 0 S → ContDiff ℝ ∞ (U n t))
    (hL2 : ∀ n t, t ∈ Icc 0 S → ∀ j ≤ 3,
      MemLp (iteratedFDeriv ℝ j (fun x => U n t x - u t x)) 2 volume)
    (hmajor : ∀ n t, t ∈ Icc 0 S →
      realTensorSobolevNorm 3 3 (fun x => U n t x - u t x) ≤ X n t)
    (hcont : ∀ n, ContinuousOn (X n) (Icc 0 S))
    (hinit : ∀ n, X n 0 ≤ ε n)
    (hder : ∀ n t, t ∈ Ico 0 S → HasDerivAt (X n) (X' n t) t)
    (hineq : ∀ n t, t ∈ Ico 0 S → X' n t ≤ C * (X n t + (X n t) ^ 2))
    (href : ContinuousOn (fun t => fderiv ℝ (u t) 0) (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S) :
    ¬ Tendsto (fun n => ‖fderiv ℝ (U n (times n)) 0‖) atTop atTop := by
  let A : ℝ := 9 * smoothEmbeddingConstant
  let errors : ℕ → ℝ := fun n => A * (2 * ε n * Real.exp (3 * C * S))
  have hA : 0 ≤ A := mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg
  have hlim : Tendsto (fun n => 2 * ε n * Real.exp (3 * C * S)) atTop (nhds 0) := by
    simpa using (hεlim.const_mul 2).mul_const (Real.exp (3 * C * S))
  have helim : Tendsto errors atTop (nhds 0) := by
    simpa [errors] using hlim.const_mul A
  have hsmall : ∀ᶠ n in atTop, 2 * ε n * Real.exp (3 * C * S) ≤ 1 / 2 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply EulerBreakdownCriterion.no_escape_near_compact_trajectory
    (fun t => fderiv ℝ (u t) 0) (fun n => fderiv ℝ (U n (times n)) 0)
    times errors S href ht helim
  filter_upwards [hsmall] with n hn
  have hX := quadratic_stability (X n) (X' n) C (ε n) S hC (hε n) hS hn
    (hcont n) (hinit n) (hder n) (hineq n) (times n) (ht n)
  have hs : ContDiff ℝ ∞ (fun x => U n (times n) x - u (times n) x) :=
    (hU n (times n) (ht n)).sub (hu (times n) (ht n))
  have hsob := real_smooth_fderiv_le_H3 3 _ hs (hL2 n (times n) (ht n)) 0
  have hdiff : fderiv ℝ (fun x => U n (times n) x - u (times n) x) 0 =
      fderiv ℝ (U n (times n)) 0 - fderiv ℝ (u (times n)) 0 :=
    (((hU n (times n) (ht n)).differentiable (by simp) 0).hasFDerivAt.sub
      ((hu (times n) (ht n)).differentiable (by simp) 0).hasFDerivAt).fderiv
  rw [hdiff] at hsob
  exact hsob.trans (mul_le_mul_of_nonneg_left
    ((hmajor n (times n) (ht n)).trans hX) hA)

end EulerSobolevBreakdown
