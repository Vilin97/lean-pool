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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFiniteScaleChoice

@[expose] public section

noncomputable section

namespace EulerPacketScaleActivation

open Real EulerPacketScaleGeometry

/-- The actual quadratic target and frame invariant imply every basic
small-beta and target-time guard used in the scalar ODE estimates. -/
theorem source_activation_ode_guards {j x β : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    0 < β ∧ β ≤ 1 / 16 ∧ 0 < sqrt β ∧ sqrt β ≤ 1 / 4 ∧
    1 / sqrt β ≤ (j ^ 2 * x) / sqrt β ∧
    (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 ∧
    0 < 1 / (j ^ 2 * x) ∧ 1 / (j ^ 2 * x) ≤ 1 / 2 := by
  have hxp : 0 < x := by linarith
  have hjp : 0 < j := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hx64 : 64 ≤ x ^ 2 := by nlinarith only [hx]
  have hm := mul_le_mul_of_nonneg_left hx64 hβ.le
  have hβsmall : β ≤ 1 / 16 := by nlinarith only [hm, hβx₂]
  have hσ : 0 < sqrt β := sqrt_pos.mpr hβ
  have hσsmall : sqrt β ≤ 1 / 4 := (sqrt_le_iff).2 ⟨by norm_num, by nlinarith only [hβsmall]⟩
  have hj2 : 9 ≤ j ^ 2 := by nlinarith only [hj]
  have hX : 2 ≤ j ^ 2 * x := by
    have hh := mul_le_mul hj2 hx (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg j)
    nlinarith only [hh]
  have htLow : 1 / sqrt β ≤ (j ^ 2 * x) / sqrt β :=
    div_le_div_of_nonneg_right (by linarith only [hX]) hσ.le
  have htime := activation_time_bounds (a := 1) (H := 1) (β := β) (x := x) (X := j ^ 2 * x)
    (by norm_num) (by norm_num) (by norm_num) hxp (by positivity) hβx hβx₂
  norm_num only [mul_one, sqrt_one, div_one] at htime
  have htUp : (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 := by nlinarith only [htime.2]
  have hy : 0 < 1 / (j ^ 2 * x) := by positivity
  have hy₂ : 1 / (j ^ 2 * x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < j ^ 2 * x)).2
    nlinarith only [hX]
  exact ⟨hβ, hβsmall, hσ, hσsmall, htLow, htUp, hy, hy₂⟩

/-- The source polynomial horizon contains the target activation time. -/
theorem source_activation_within_horizon {j x β C : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x) (hC : 2 ≤ C)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    1 ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      (j ^ 2 * x) / sqrt β ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      β * ((j ^ 2 * x) / sqrt β) ^ 2 = (j ^ 2 * x) ^ 2 := by
  obtain ⟨hβ, _, _, _, _, ht, _, _⟩ := source_activation_ode_guards hj hx hβx hβx₂
  have hn : 0 ≤ j ^ 2 * x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hC (by nlinarith only [hn] : 0 ≤ 1 + j ^ 2 * x ^ 2)
  refine ⟨by nlinarith only [hh, hn], by nlinarith only [ht, hh], ?_⟩
  rw [div_pow, sq_sqrt hβ.le]
  field_simp

end EulerPacketScaleActivation
