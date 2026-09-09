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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketSourceTime

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketBaseScales

open Real

/-- A negative total real power absorbs a fixed monomial horizon. -/
theorem base_power_decay (T p : ℝ) (m k : ℕ)
    (hp : p + 2 * m + k < 0) :
    Tendsto (fun x : ℝ => x ^ p * (T * x ^ 2) ^ m * x ^ k) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).const_mul (T ^ m)
  simp only [neg_neg, mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring

/-- Exponential decay absorbs every fixed real polynomial power and
every fixed monomial horizon power. -/
theorem base_exponential_decay (T p b : ℝ) (m k : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ p * exp (-b * x) * (T * x ^ 2) ^ m * x ^ k)
      atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 2 * m + k) b hb).const_mul (T ^ m)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring

/-- The first normal stage has `h=x₀^1000`, hence epsilon of order
`x₀^-500`; its complete coefficient error beats `x₀^-10 Θ^-60`. -/
theorem first_stage_coefficient_error_tendsto_zero
    (T D N b : ℝ) (hD : 1000 ≤ D) (hb : 0 < b) :
    Tendsto (fun x : ℝ =>
      (16 * (8 * x ^ (-500 : ℝ) * (T * x ^ 2) +
        x ^ (-D / 4) + x ^ N * exp (-b * x))) * (T * x ^ 2) ^ 60 * x ^ 10)
      atTop (𝓝 0) := by
  have h₁ := (base_power_decay T (-500) 61 10 (by norm_num)).const_mul 8
  have h₂ := base_power_decay T (-D / 4) 60 10 (by push_cast; linarith)
  have h₃ := base_exponential_decay T N b 60 10 hb
  have hh := ((h₁.add h₂).add h₃).const_mul 16
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [show (61 : ℕ) = 60 + 1 from rfl, pow_succ]
  ring

/-- At the special second stage the older gradient is polynomial in
the base scale, while the new inverse shear is exponentially small. -/
theorem second_stage_shear_error_tendsto_zero
    (T b : ℝ) (hb : 0 < b) (A : ℕ) :
    Tendsto (fun x : ℝ => exp (-b * x) * (1 + x ^ (1000 : ℕ)) ^ 2 *
      (T * x ^ 2) ^ A) atTop (𝓝 0) := by
  have h₀ := base_exponential_decay T 0 b A 0 hb
  have h₁ := (base_exponential_decay T 1000 b A 0 hb).const_mul 2
  have h₂ := base_exponential_decay T 2000 b A 0 hb
  have hh := (h₀.add h₁).add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro x
  dsimp only
  simp only [rpow_zero, rpow_ofNat, pow_zero, mul_one, one_mul]
  have hp : x ^ (2000 : ℕ) = (x ^ (1000 : ℕ)) ^ 2 := by rw [← pow_mul]
  rw [hp]
  ring

/-- The exact base horizon `6 J² x₀^(2-1000/2)` tends to zero. -/
theorem base_horizon_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => 6 * J ^ 2 * x ^ (2 - 1000 / 2 : ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 498)).const_mul (6 * J ^ 2)
  norm_num at hh ⊢
  exact hh

/-- The core-volume guard `h r³ Sbase`, with `r=x₀^-1000`,
also tends to zero from the explicit base choices. -/
theorem base_core_volume_cost_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => x ^ (1000 : ℕ) * (x ^ (-1000 : ℝ)) ^ 3 *
      (6 * J ^ 2 * x ^ (-498 : ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2498)).const_mul (6 * J ^ 2)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hid : (-2498 : ℝ) = 1000 + (-1000) * 3 + (-498) := by norm_num
  rw [hid, rpow_add hx, rpow_add hx, rpow_mul hx.le]
  norm_num only [rpow_ofNat]
  ring

end EulerPacketBaseScales
