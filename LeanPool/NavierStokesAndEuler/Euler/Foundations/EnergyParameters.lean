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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.EnergyBootstrap

@[expose] public section

noncomputable section

namespace EulerEnergyParameters

open Real EulerGevreyCutoff

theorem exponential_error_small (z : ℝ) (hz : 256 ≤ z) :
    exp (-z) ≤ 1 / (8 * z ^ 3) := by
  have hz0 : 0 < z := by linarith
  have h := factorial_decay 4 z hz0.le
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  apply (le_div_iff₀ (show 0 < 8 * z ^ 3 by positivity)).2
  have hm := mul_le_mul_of_nonneg_right (show (192 : ℝ) ≤ z by linarith)
    (show 0 ≤ z ^ 3 * exp (-z) by positivity)
  nlinarith

theorem radius_budget (z C B ρ₀ S : ℝ) (hz : 256 ≤ z)
    (_hC : 0 ≤ C) (hCz : C ≤ z) (hB : 0 ≤ B) (hBz : B ≤ 1 / (8 * z ^ 3))
    (hρ : 1 / z ^ 2 ≤ ρ₀) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    2 * C * (B + exp (-z)) * S ≤ ρ₀ / 2 := by
  have hz0 : 0 < z := by linarith
  have he := exponential_error_small z hz
  calc
    _ ≤ 2 * z * (1 / (8 * z ^ 3) + 1 / (8 * z ^ 3)) * 1 := by gcongr
    _ = (1 / z ^ 2) / 2 := by field_simp; ring
    _ ≤ ρ₀ / 2 := by linarith

theorem residual_beats_amplification (z C S L : ℝ) (hz : 256 ≤ z)
    (hC : 0 ≤ C) (hCz : C ≤ z) (_hS : 0 ≤ S) (hS1 : S ≤ 1) (hL : 1 ≤ L) :
    2 * exp (-(7 / 10) * z ^ 2 * L) * exp (3 * C * S) ≤ exp (-z) / 2 := by
  have hz0 : 0 < z := by linarith
  have hCS : C * S ≤ z := (mul_le_mul_of_nonneg_left hS1 hC).trans (by simpa using hCz)
  have hLz := mul_le_mul_of_nonneg_left hL (show 0 ≤ (7 / 10 : ℝ) * z ^ 2 by positivity)
  have hlog : -(7 / 10) * z ^ 2 * L + 3 * C * S ≤ -2 * z := by nlinarith
  have hprod : exp (-(7 / 10) * z ^ 2 * L) * exp (3 * C * S) ≤ exp (-2 * z) := by
    rw [← exp_add]
    exact exp_le_exp.mpr hlog
  have he : exp (-z) ≤ 1 / 4 := by
    have hh : 4 ≤ exp z := by linarith [add_one_le_exp z]
    simpa only [exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hh
  have heq : exp (-2 * z) = exp (-z) ^ 2 := by
    rw [show -2 * z = -z + -z by ring, exp_add, pow_two]
  rw [heq] at hprod
  nlinarith [exp_pos (-z)]

theorem frequency_transport_budget (k θ : ℝ) (hk : 1 ≤ k) (hθ : θ ≤ 1 / 4)
    (hz : 8 ≤ k ^ (θ / 2)) :
    k ^ (-(1 / 2 : ℝ)) ≤ 1 / (8 * (k ^ (θ / 2)) ^ 3) := by
  have hk0 : 0 < k := by linarith
  have hz0 : 0 < k ^ (θ / 2) := rpow_pos_of_pos hk0 _
  have hp : (k ^ (θ / 2)) ^ 4 ≤ k ^ (1 / 2 : ℝ) := by
    rw [← rpow_natCast _ 4, ← rpow_mul hk0.le]
    exact rpow_le_rpow_of_exponent_le hk (by norm_num; nlinarith)
  rw [rpow_neg hk0.le]
  calc
    _ ≤ ((k ^ (θ / 2)) ^ 4)⁻¹ := inv_anti₀ (by positivity) hp
    _ ≤ 1 / (8 * (k ^ (θ / 2)) ^ 3) := by
      rw [inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have h := mul_le_mul_of_nonneg_right hz (pow_nonneg hz0.le 3)
      nlinarith

theorem source_coefficient_bound (P k c Q θ : ℝ) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hc : c ≤ Q) (hθ : 0 ≤ θ) (hsmall : P ^ Q ≤ k ^ (θ / 100)) :
    P ^ c ≤ k ^ (θ / 2) := by
  exact (rpow_le_rpow_of_exponent_le hP hc).trans
    (hsmall.trans (rpow_le_rpow_of_exponent_le hk (by nlinarith)))

theorem source_residual_budget (k θ C S : ℝ) (hk : 0 < k)
    (hz : 256 ≤ k ^ (θ / 2)) (hlog : 1 ≤ log k)
    (hC : 0 ≤ C) (hCk : C ≤ k ^ (θ / 2)) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    2 * exp (-(7 / 10) * k ^ θ * log k) * exp (3 * C * S) ≤
      exp (-(k ^ (θ / 2))) / 2 := by
  have he : (k ^ (θ / 2)) ^ 2 = k ^ θ := by
    rw [← rpow_natCast _ 2, ← rpow_mul hk.le]
    congr 1
    norm_num
  simpa only [he] using residual_beats_amplification (k ^ (θ / 2)) C S (log k)
    hz hC hCk hS hS1 hlog

end EulerEnergyParameters
