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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketSourceScales

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketSourceTime

open Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales

/-- The preceding two shear logarithms are exactly those obtained by
substituting the quadratic recurrence into (37). -/
theorem preceding_scale_identities {p q x X Y : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hx : x = p ^ 2 * X) (hX : X = q ^ 2 * Y) :
    X / p ^ 5 = x / p ^ 7 ∧ Y / q ^ 5 = x / (p ^ 2 * q ^ 7) := by
  constructor
  · rw [hx]
    field_simp
  · rw [hx, hX]
    field_simp

/-- A frame normalization `a≤2` gives the explicit source epsilon bound. -/
theorem epsilon_of_shear_bound {a L : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    sqrt (a / exp L) ≤ 2 * exp (-L / 2) := by
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  rw [sqrt_div ha, ← exp_half]
  have hid : -L / 2 = -(L / 2) := by ring
  rw [hid, exp_neg]
  change sqrt a / exp (L / 2) ≤ 2 / exp (L / 2)
  exact div_le_div_of_nonneg_right hs (exp_pos (L / 2)).le

/-- The current time width in (37), after exact substitution of the scales. -/
noncomputable def sourceTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 *
    exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The following time width, using `x_j=j²x_{j-1}` twice. -/
noncomputable def sourceNextTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))

/-- The exact quotient of consecutive time widths. -/
noncomputable def sourceTimeRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) +
      x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- Exact cancellation computes the consecutive time-width quotient. -/
theorem source_time_ratio_identity (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    sourceNextTimeWidth J x n = sourceTimeRatio J x n * sourceTimeWidth J x n := by
  unfold sourceNextTimeWidth sourceTimeRatio sourceTimeWidth
  rw [exp_add]
  have hc : exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) = 1 := by
    rw [← exp_add]
    convert! exp_zero using 1
    ring_nf
  linear_combination -(3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 *
    (x n) ^ 2 * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) * hc

/-- Consecutive time-width ratios are summable, so they tend to zero. -/
theorem source_time_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (sourceTimeRatio J x) := by
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) 4 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, pow_zero, mul_one] at hsum
  apply hsum.of_nonneg_of_le
  · intro n; unfold sourceTimeRatio; positivity
  · intro n
    have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hj]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ((J + n : ℕ) : ℝ))
    have hh' := mul_le_mul_of_nonneg_right hh (exp_pos
      (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))).le
    unfold sourceTimeRatio
    have hid : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) + (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by
        ring
    rw [hid] at hh' ⊢
    convert! hh' using 1
    ring

/-- The actual next time width is eventually at most half of the current width. -/
theorem source_time_width_eventually_contracts
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ᶠ n in atTop, sourceNextTimeWidth J x n ≤ sourceTimeWidth J x n / 2 := by
  have hh := (source_time_ratio_summable J hJ x hx0 hx).tendsto_atTop_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hh] with n hn
  rw [source_time_ratio_identity]
  have hW : 0 ≤ sourceTimeWidth J x n := by unfold sourceTimeWidth; positivity
  have hb := mul_le_mul_of_nonneg_right hn hW
  nlinarith only [hb]

/-- The extra normalized horizon length has the explicit polynomial/exponential
bound asserted after (39). -/
theorem source_extra_time_bound
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) * sourceNextTimeWidth J x n ≤
      48 * ((J + n : ℕ) : ℝ) ^ 6 * (x n) ^ 2 *
        exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) +
          (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hroot : sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) ≤
      2 * exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
    rw [sqrt_mul ha, ← exp_half]
    have hh := mul_le_mul_of_nonneg_right hs (exp_pos ((x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) / 2)).le
    convert! hh using 1
    congr 2
    ring
  have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by nlinarith only [hj]
  have hW : 0 ≤ sourceNextTimeWidth J x n := by unfold sourceNextTimeWidth; positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤
    2)) hW
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 12 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5)))
  unfold sourceNextTimeWidth at hh
  have hpE : x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by ring
  have hnE : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) := by ring
  rw [hpE, hnE] at hh hp'
  rw [exp_add]
  change 2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
    (3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) ≤ _
  rw [hnE]
  refine hh.trans ?_
  convert! hp' using 1 <;> ring

/-- Every horizon power times the extra normalized length is summable. -/
theorem source_extra_time_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2) :
    Summable (fun n => 2 * sqrt (a n * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      sourceNextTimeWidth J x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) (48 * (2 * C) ^ A) (6 + 2 * A) (2 + 2 * A)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  simp only [rpow_ofNat] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    have hθ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold sourceNextTimeWidth
    positivity
  · intro n
    have hθ₀ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    have hθ := pow_le_pow_left₀ hθ₀ (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul (source_extra_time_bound J hJ1 x n (ha n) (ha₂ n)) hθ
      (pow_nonneg hθ₀ A) (by positivity)
    convert! hh using 1
    simp only [mul_pow, pow_add, ← pow_mul]
    ring

/-- The parent-shear square is negligible relative to the newly chosen shear. -/
theorem source_parent_shear_square_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (2 * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) /
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5)) := by
  have hh := source_scale_exponential_summable J 1 7 (by omega) x (by linarith) hx
    5 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hh
  apply hh.congr
  intro n
  rw [← exp_sub]
  congr 1
  ring

/-- The good-interval pressure costs of the source are summable. -/
theorem source_good_interval_cost_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (-x n / ((J + n : ℕ) : ℝ) ^ 3) *
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5) *
      exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hsum := source_scale_exponential_summable J 1 5 (by omega) x (by linarith) hx
    3 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hsum
  have hx1 := quadratic_growth_one_le J (by omega) x hx0 hx
  apply hsum.of_nonneg_of_le
  · intro n; positivity
  · intro n
    have hp : (1 : ℝ) ≤ (J - 1 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 1 + n by omega)
    have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (show J - 1 + n ≤ J +
      n by omega)
    have hd₁ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_left₀ (by linarith) hpj 5)
    have hd₂ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hd₁ hd₂ ⊢
    nlinarith only [hd₁, hd₂]

end EulerPacketSourceTime
