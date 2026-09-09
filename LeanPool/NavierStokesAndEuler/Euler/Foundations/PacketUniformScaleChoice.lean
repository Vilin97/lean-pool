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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformLogBounds

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleChoice

open Real EulerScale EulerPacketScaleGeometry EulerPacketUniformScaleSums
  EulerPacketUniformLogBounds

/-- One sufficiently large initial stage makes every predecessor-log
coefficient small, uniformly over all subsequent stages. -/
theorem exists_uniform_stage_choice (d B N : ℕ) (a c b : ℝ)
    (haB : a < B) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ d < J ∧ (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2 ∧
      ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4 := by
  have hh := (stage_rpow_div_shifted_power_tendsto_zero (d + 1) d B (by omega) a haB).const_mul c
  simp only [mul_zero] at hh
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hh.eventually_le_const (by positivity : (0 : ℝ) < b / 4))
  let R : ℕ := 2 ^ (2 * N + 3) + 3
  let J : ℕ := (d + 1) + M + R
  have hR3 : 3 ≤ R := Nat.le_add_left 3 _
  have hJ3 : 3 ≤ J := by dsimp [J]; omega
  have hdJ : d < J := by dsimp [J]; omega
  have hpJ : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) := by
    exact_mod_cast (show 2 ^ (2 * N + 3) ≤ J by dsimp [J, R]; omega)
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  refine ⟨J, hJ3, hdJ, by nlinarith only [hpJ, hJr], ?_⟩
  intro n
  have h := hM (M + R + n) (by omega)
  have hj : d + 1 + (M + R + n) = J + n := by dsimp [J]; omega
  have hp : d + 1 - d + (M + R + n) = J - d + n := by dsimp [J]; omega
  simpa only [hj, hp] using h

/-- For a stage chosen above, one explicit lower bound on the initial
scale controls all logarithmic scale errors at once. -/
theorem uniform_source_exponent_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    ∀ n, -b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      -(b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ N) := by
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hlog := polynomial_logs_uniformly_absorbed J N hJ hJN x hx0 hx C p q (b / 2)
    (by positivity) (by convert! hlarge using 1; ring)
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
  have hxn : 0 < x n := by linarith [hx1 n]
  have hpow : ((J + n : ℕ) : ℝ) ^ a ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 haN
  have hscales := div_le_div_of_nonneg_left hxn.le (rpow_pos_of_pos hj a) hpow
  have hcm := mul_le_mul_of_nonneg_right (hcoeff n)
    (div_nonneg hxn.le (rpow_nonneg hj.le a))
  have hct : c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) ≤
      (b / 4) * (x n / ((J + n : ℕ) : ℝ) ^ a) := by
    convert! hcm using 1
    field_simp [(rpow_pos_of_pos hj a).ne', hp.ne']
  have hscaleB := mul_le_mul_of_nonneg_left hscales hb.le
  have hl := hlog n
  nlinarith only [hct, hscaleB, hl]

/-- The complete logarithmic source cost has a uniform geometric-series
bound after choosing the stage and then the initial scale. -/
theorem uniform_source_cost_tsum_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤
      exp (-(b / 2) * (x 0 / (J : ℝ) ^ N)) /
        (1 - exp (-(b / 2) * (x 0 / (J : ℝ) ^ N))) := by
  have hmajor := fun n => exp_le_exp.mpr
    (uniform_source_exponent_bound J d B N hJ hdJ hJN x hx0 hx a b c C p q haN hb hcoeff hlarge n)
  have hsum := exponential_decay_summable J hJ x (by linarith) hx N (b / 2) (by positivity)
  have hcost := hsum.of_nonneg_of_le (fun _ => (exp_pos _).le) hmajor
  have hh := hcost.tsum_le_tsum hmajor hsum
  have hpower : (2 : ℝ) ^ (N + 1) ≤ (J : ℝ) ^ 2 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : N + 1 ≤ 2 * N + 3)).trans hJN
  exact hh.trans (source_exponential_tsum_bound J N hJ hpower x (by linarith) hx (b / 2) (by
    positivity))

/-- The source's order of parameter choice is valid: first one chooses
the stage `J`, then the base scale `x₀`, and the whole infinite sum is
arbitrarily small. This includes the real support exponent `7/2`. -/
theorem source_uniform_small_sum_choice
    (d B N : ℕ) (a b c C p q : ℝ) (haB : a < B) (haN : a ≤ N) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) →
        (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
          c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
          C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤ δ := by
  obtain ⟨J, hJ3, hdJ, hJN, hcoeff⟩ := exists_uniform_stage_choice d B N a c b haB hb
  have hJ : 1 ≤ J := by omega
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hh := source_exponential_bound_tendsto_zero J N hJ (b / 2) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (hh.eventually_le_const hδ)
  let L := (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2)
  let X₀ := max 1 (max L Y)
  have hX₀ : 1 ≤ X₀ := le_max_left _ _
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx0 hx
  have hx1 : 1 ≤ x 0 := hX₀.trans hx0
  have hlarge : L ≤ x 0 := (le_trans (le_max_left L Y) (le_max_right 1 (max L Y))).trans hx0
  have hYx : Y ≤ x 0 := (le_trans (le_max_right L Y) (le_max_right 1 (max L Y))).trans hx0
  exact (uniform_source_cost_tsum_bound J d B N hJ hdJ hJN x hx1 hx a b c C p q
    haN hb hcoeff hlarge).trans (hY (x 0) hYx)

end EulerPacketUniformScaleChoice
