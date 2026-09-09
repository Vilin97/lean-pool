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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketTargetCompression

@[expose] public section

noncomputable section

/-!
Convergence estimates for the actual quadratic scale recurrence in (37).
The sequence is reindexed so that `x 0 = x_{J-1}` and
`x (n+1) = (J+n)^2 x n`; hence `J+n` is the stage index in the source.
-/

namespace EulerScale

open Filter
open scoped Topology

/-- Positivity propagates through the scale recurrence from any positive initial scale. -/
theorem quadratic_growth_pos (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 0 < x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
      positivity

/-- The reciprocal of the stage index tends to zero. -/
theorem stage_inv_tendsto_zero (J : ℕ) :
    Tendsto (fun n : ℕ => (((J + n : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using
    ((tendsto_add_atTop_iff_nat J).2
      (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0)))

/-- Every fixed polynomial in the stage index divided by the scale is summable. -/
theorem polynomial_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  have hlim : Tendsto
      (fun n : ℕ => (1 + (((J + n : ℕ) : ℝ))⁻¹) ^ A *
        ((((J + n : ℕ) : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (stage_inv_tendsto_zero J)).pow A).mul
      ((stage_inv_tendsto_zero J).pow 2)
    simpa using h
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Eventually.of_forall fun n => ne_of_gt (div_pos (pow_pos (hjp n) _) (hxp n))
  · apply hlim.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp (n + 1)).le _) (hxp (n + 1)).le),
      Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp n).le _) (hxp n).le), hx]
    have hj : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hj]
    have hi : 1 + (((J + n : ℕ) : ℝ))⁻¹ =
        (((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ) := by
      field_simp [ne_of_gt (hjp n)]
    rw [hi, div_pow]
    field_simp [ne_of_gt (hjp n), ne_of_gt (hxp n)]

/-- A simple exponential majorization requiring no numerical approximations. -/
theorem exp_neg_le_reciprocal (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ 1 / t := by
  have he : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le ht he

/-- Every exponential decay in a scale divided by a fixed natural power is summable. -/
theorem exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) (b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx A).mul_left (1 / b)
  apply hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have ht : 0 < b * (x n / ((J + n : ℕ) : ℝ) ^ A) :=
    mul_pos hb (div_pos (hxp n) (pow_pos hj _))
  calc
    _ = Real.exp (-(b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by congr 1; ring
    _ ≤ 1 / (b * (x n / ((J + n : ℕ) : ℝ) ^ A)) := exp_neg_le_reciprocal _ ht
    _ = (1 / b) * (((J + n : ℕ) : ℝ) ^ A / x n) := by field_simp

/-- The same decay conclusion holds for every real power, including `7/2`. -/
theorem exponential_decay_real_power_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  apply (exponential_decay_summable J hJ x hx0 hx N b hb).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj
  have hpow : ((J + n : ℕ) : ℝ) ^ A ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hj hN.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (div_le_div_of_nonneg_left (hxp n).le (Real.rpow_pos_of_pos hjp A) hpow) (by linarith)

/-- The logarithm of the rapidly growing scale still has a quadratic polynomial bound. -/
theorem abs_log_growth_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, |Real.log (x n)| ≤ (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  intro n
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hJ2 : (1 : ℝ) ≤ (J : ℝ) ^ 2 := one_le_pow₀ hJr
      calc
        _ ≤ |Real.log (x 0)| + 2 := by linarith
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hJ2 (by positivity : 0 ≤ |Real.log (x 0)|
          + 2)
  | succ n ih =>
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj1
      have hlog : 0 ≤ Real.log ((J + n : ℕ) : ℝ) := Real.log_nonneg hj1
      have hlogle : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
        (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
      have hjnext : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hx, Real.log_mul (pow_ne_zero _ hjp.ne') (hxp n).ne', Real.log_pow]
      calc
        _ ≤ |(2 : ℝ) * Real.log ((J + n : ℕ) : ℝ)| + |Real.log (x n)| := abs_add_le _ _
        _ = 2 * Real.log ((J + n : ℕ) : ℝ) + |Real.log (x n)| := by rw [abs_of_nonneg (by
          positivity)]
        _ ≤ 2 * ((J + n : ℕ) : ℝ) +
            (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by linarith
        _ ≤ _ := by
          rw [hjnext]
          nlinarith [abs_nonneg (Real.log (x 0)),
            mul_nonneg (abs_nonneg (Real.log (x 0))) hjp.le]

/-- Every polynomial weight times `|log x|/x` is summable. -/
theorem polynomial_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * |Real.log (x n)| / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx (A + 2)).mul_left
    (|Real.log (x 0)| + 2)
  apply hs.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (hxp n).le)
  intro n
  have h := mul_le_mul_of_nonneg_left (abs_log_growth_le J hJ x hx0 hx n)
    (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)
  have hd := div_le_div_of_nonneg_right h (hxp n).le
  simpa only [pow_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd

/-- The logarithmic term on the right side of (39) tends to zero with every fixed polynomial weight. -/
theorem polynomial_log_over_growth_tendsto_zero (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) :
    Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * Real.log (x n) / x n) atTop (𝓝 0) := by
  have hs := polynomial_log_over_growth_summable J hJ x hx0 hx A
  have hn : Tendsto (fun n => -(((J + n : ℕ) : ℝ) ^ A * |Real.log (x n)| / x n))
      atTop (𝓝 0) := by simpa using hs.tendsto_atTop_zero.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hn hs.tendsto_atTop_zero
  · intro n
    have hxp := quadratic_growth_pos J hJ x hx0 hx n
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (x n)))
      (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)
    simpa only [mul_neg, neg_div] using div_le_div_of_nonneg_right h hxp.le
  · intro n
    have hxp := quadratic_growth_pos J hJ x hx0 hx n
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self (Real.log (x n))) (by positivity)) hxp.le

/-- The logarithm of the stage index is also harmless in every polynomially weighted scale sum. -/
theorem polynomial_stage_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) :
    Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * Real.log ((J + n : ℕ) : ℝ) / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : ∀ n, (1 : ℝ) ≤ (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 1 ≤ J + n by omega)
  apply (polynomial_over_growth_summable J hJ x hx0 hx (A + 1)).of_nonneg_of_le
  · intro n
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (hj1 n))) (hxp n).le
  · intro n
    have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one (hj1 n)
    have hl : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
      (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
    simpa only [pow_succ] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)) (hxp n).le

/-- A power at least three in the denominator dominates the square from `1/log k_j`. -/
theorem stage_sq_div_real_power_tendsto_zero (J : ℕ) (hJ : 1 ≤ J)
    (A : ℝ) (hA : 3 ≤ A) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ 2 / ((J + n : ℕ) : ℝ) ^ A)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (stage_inv_tendsto_zero J)
  · intro n
    positivity
  · intro n
    have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj1
    have hp : ((J + n : ℕ) : ℝ) ^ 3 ≤ ((J + n : ℕ) : ℝ) ^ A := by
      simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hj1 hA
    calc
      _ ≤ ((J + n : ℕ) : ℝ) ^ 2 / ((J + n : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hjp _) hp
      _ = _ := by field_simp

/-- The previous-stage frequency and shear terms have vanishing relative logarithms. -/
theorem stage_sq_div_predecessor_power_tendsto_zero (J : ℕ) (hJ : 2 ≤ J)
    (A : ℕ) (hA : 3 ≤ A) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ 2 / ((J - 1 + n : ℕ) : ℝ) ^ A)
      atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun n : ℕ => (1 + (((J - 1 + n : ℕ) : ℝ))⁻¹) ^ 2 *
        ((((J - 1 + n : ℕ) : ℝ))⁻¹) ^ (A - 2)) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add
      (stage_inv_tendsto_zero (J - 1))).pow 2).mul
      ((stage_inv_tendsto_zero (J - 1)).pow (A - 2))
    simpa only [add_zero, one_pow, zero_pow (show A - 2 ≠ 0 by omega), mul_zero] using h
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by exact_mod_cast (show 0 < J - 1 + n by omega)
  have hj : (((J + n : ℕ) : ℝ)) = ((J - 1 + n : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show J + n = (J - 1 + n) + 1 by omega)
  have hi : 1 + (((J - 1 + n : ℕ) : ℝ))⁻¹ =
      (((J - 1 + n : ℕ) : ℝ) + 1) / ((J - 1 + n : ℕ) : ℝ) := by field_simp
  have hpow : ((J - 1 + n : ℕ) : ℝ) ^ A =
      ((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 1 + n : ℕ) : ℝ) ^ (A - 2) := by
    rw [← pow_add, show 2 + (A - 2) = A by omega]
  rw [hj, hi, hpow, div_pow]
  field_simp [hp.ne']
  simp only [one_div, ← mul_pow, inv_mul_cancel₀ hp.ne', one_pow]

/-- A finite sum of positive exponential scales has an explicit logarithmic upper bound. -/
theorem log_sum_exp_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ Real.log (∑ i, Real.exp (a i)) ∧
      Real.log (∑ i, Real.exp (a i)) ≤ Real.log (Fintype.card ι : ℝ) + ∑ i, a i := by
  classical
  have hpos : 0 < ∑ i, Real.exp (a i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hone : 1 ≤ ∑ i, Real.exp (a i) :=
    (Real.one_le_exp (ha (Classical.arbitrary ι))).trans
      (Finset.single_le_sum (fun i _ => (Real.exp_pos (a i)).le) (Finset.mem_univ _))
  constructor
  · exact Real.log_nonneg hone
  · have hs : (∑ i, Real.exp (a i)) ≤ (Fintype.card ι : ℝ) * Real.exp (∑ i, a i) := by
      calc
        _ ≤ ∑ _i : ι, Real.exp (∑ i, a i) := by
          apply Finset.sum_le_sum
          intro i _hi
          exact Real.exp_monotone (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
        _ = _ := by simp
    calc
      _ ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (∑ i, a i)) := Real.log_le_log hpos hs
      _ = _ := by rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp]

/-- Finite aggregation preserves a logarithmic scale separation proved for each explicit term. -/
theorem log_sum_exp_mul_tendsto_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ → ℝ) (r : ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n) (hr : ∀ n, 0 ≤ r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (halim : ∀ i, Tendsto (fun n => a i n * r n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (∑ i, Real.exp (a i n)) * r n) atTop (𝓝 0) := by
  classical
  have hs : Tendsto (fun n => ∑ i, a i n * r n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => halim i)
  have hu : Tendsto (fun n => (Real.log (Fintype.card ι : ℝ) + ∑ i, a i n) * r n)
      atTop (𝓝 0) := by
    have h := (hrlim.const_mul (Real.log (Fintype.card ι : ℝ))).add hs
    simpa only [mul_zero, add_zero, add_mul, Finset.sum_mul] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact mul_nonneg (log_sum_exp_bounds (fun i => a i n) (fun i => ha i n)).1 (hr n)
  · intro n
    exact mul_le_mul_of_nonneg_right (log_sum_exp_bounds (fun i => a i n) (fun i => ha i n)).2 (hr
      n)

/-- A starting scale at least one stays at least one. -/
theorem quadratic_growth_one_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 1 ≤ x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 1 ≤ x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) ih

/--
The logarithms of the eight terms in the source's aggregate parameter: the fixed
base constant; the previous frequency power; inverse support and spike scales;
the present and previous shears; and the present and previous geometric sizes.
-/
noncomputable def sourceParameterExponent (J : ℕ) (Cbase Cstar : ℝ) (x : ℕ → ℝ) (i : Fin 8) (n : ℕ)
  : ℝ :=
  ![Real.log Cbase,
    Cstar * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4,
    x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ),
    x n / ((J + n : ℕ) : ℝ) ^ 3,
    x n / ((J + n : ℕ) : ℝ) ^ 5,
    x n / ((J - 1 + n : ℕ) : ℝ) ^ 7,
    Real.log (((J + n : ℕ) : ℝ) ^ 2 * x n),
    Real.log (x n)] i

/-- The sum of precisely those eight positive parameter terms. -/
noncomputable def sourceParameterAggregate (J : ℕ) (Cbase Cstar : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 8, Real.exp (sourceParameterExponent J Cbase Cstar x i n)

theorem sourceParameterExponent_nonneg (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ i n, 0 ≤ sourceParameterExponent J Cbase Cstar x i n := by
  intro i n
  have hxn : 1 ≤ x n := quadratic_growth_one_le J (by omega) x hx0 hx n
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hprod : 1 ≤ ((J + n : ℕ) : ℝ) ^ 2 * x n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) hxn
  fin_cases i
  · simpa [sourceParameterExponent] using Real.log_nonneg hCbase
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simpa [sourceParameterExponent] using Real.log_nonneg hprod
  · simpa [sourceParameterExponent] using Real.log_nonneg hxn

/-- Every explicitly defined parameter term is negligible on the logarithmic frequency scale. -/
theorem sourceParameterExponent_relative_tendsto_zero (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ i, Tendsto (fun n => sourceParameterExponent J Cbase Cstar x i n *
      (((J + n : ℕ) : ℝ) ^ 2 / x n)) atTop (𝓝 0) := by
  intro i
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x hx0 hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  have hlx := polynomial_log_over_growth_tendsto_zero J hJ1 x hx0 hx 2
  fin_cases i
  · simpa [sourceParameterExponent] using
      ((polynomial_over_growth_summable J hJ1 x hx0 hx 2).tendsto_atTop_zero.const_mul (Real.log
        Cbase))
  · have h := (stage_sq_div_predecessor_power_tendsto_zero J hJ 4 (by omega)).const_mul Cstar
    simp only [mul_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 (7 / 2) (by norm_num)
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 3 (by norm_num)
    simp only [Real.rpow_ofNat] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 5 (by norm_num)
    simp only [Real.rpow_ofNat] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_predecessor_power_tendsto_zero J hJ 7 (by omega)
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := ((polynomial_stage_log_over_growth_summable J hJ1 x hx0 hx
    2).tendsto_atTop_zero.const_mul 2).add hlx
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    have hjp' : (0 : ℝ) < (J : ℝ) + n := by simpa using hjp n
    rw [Real.log_mul (pow_ne_zero _ hjp'.ne') (hxp n).ne', Real.log_pow]
    push_cast
    ring
  · apply hlx.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    ring

/-- Expansion of the aggregate into the scales listed immediately before (39). -/
theorem sourceParameterAggregate_eq (J : ℕ) (hJ : 1 ≤ J) (Cbase Cstar : ℝ)
    (hCbase : 0 < Cbase) (x : ℕ → ℝ) (hxp : ∀ n, 0 < x n) (n : ℕ) :
    sourceParameterAggregate J Cbase Cstar x n = Cbase +
      Real.exp (Cstar * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ 3) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ 5) +
      Real.exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) +
      ((J + n : ℕ) : ℝ) ^ 2 * x n + x n := by
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have hprod : 0 < ((J + n : ℕ) : ℝ) ^ 2 * x n := mul_pos (pow_pos hj _) (hxp n)
  have hprod' : 0 < ((J : ℝ) + n) ^ 2 * x n := by simpa using hprod
  simp [sourceParameterAggregate, sourceParameterExponent, Fin.sum_univ_succ,
    Real.exp_log hCbase, Real.exp_log (hxp n), Real.exp_log hprod']
  ring

/--
The full logarithmic separation in (39), for the explicit aggregate of all eight
scales. Its hypotheses contain only the scale recurrence and fixed positivity
conditions; the logarithmic separation is a conclusion.
-/
theorem source_parameters_separated (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Tendsto (fun n => Real.log (sourceParameterAggregate J Cbase Cstar x n) /
      (x n / ((J + n : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hJ1 : 1 ≤ J := by omega
  have hx0p : 0 < x 0 := lt_of_lt_of_le zero_lt_one hx0
  have hxp := quadratic_growth_pos J hJ1 x hx0p hx
  have hlim := log_sum_exp_mul_tendsto_zero
    (sourceParameterExponent J Cbase Cstar x)
    (fun n => ((J + n : ℕ) : ℝ) ^ 2 / x n)
    (sourceParameterExponent_nonneg J hJ Cbase Cstar hCbase hCstar x hx0 hx)
    (fun n => div_nonneg (sq_nonneg _) (hxp n).le)
    (polynomial_over_growth_summable J hJ1 x hx0p hx 2).tendsto_atTop_zero
    (sourceParameterExponent_relative_tendsto_zero J hJ Cbase Cstar x hx0p hx)
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [sourceParameterAggregate]
  field_simp

/-- Exponential scale decay remains summable after a quantitatively vanishing relative error. -/
theorem perturbed_exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) (e : ℕ → ℝ)
    (he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0)) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) + e n)) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hb2 : 0 < b / 2 := by linarith
  apply (exponential_decay_real_power_summable J hJ x hx0 hx A (b / 2)
    hb2).of_norm_bounded_eventually_nat
  filter_upwards [he.eventually_le_const hb2] with n hn
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have hy : 0 < x n / ((J + n : ℕ) : ℝ) ^ A := div_pos (hxp n) (Real.rpow_pos_of_pos hj A)
  have herror := (div_le_iff₀ hy).mp hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  linarith

/--
Both initial-increment exponential bounds after (22) are summable. In particular,
the mean estimate needs no extra power of the oscillation frequency.
-/
theorem initial_increment_majorants_summable (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (m C b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * x n +
      m * (x n / ((J + n : ℕ) : ℝ) ^ 2) +
      m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      C * Real.log (sourceParameterAggregate J Cbase Cstar x n))) ∧
    Summable (fun n => Real.exp (-2 * (x n / ((J + n : ℕ) : ℝ) ^ 2) +
      m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      C * Real.log (sourceParameterAggregate J Cbase Cstar x n))) := by
  have hJ1 : 1 ≤ J := by omega
  have hx0p : 0 < x 0 := lt_of_lt_of_le zero_lt_one hx0
  have hxp := quadratic_growth_pos J hJ1 x hx0p hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  let e : ℕ → ℝ := fun n => m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
    C * Real.log (sourceParameterAggregate J Cbase Cstar x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := ((stage_sq_div_real_power_tendsto_zero J hJ1 (7 / 2) (by norm_num)).const_mul m).add
      ((source_parameters_separated J hJ Cbase Cstar hCbase hCstar x hx0 hx).const_mul C)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only [e]
    field_simp [(hxp n).ne', (hjp n).ne', (Real.rpow_pos_of_pos (hjp n) (7 / 2)).ne']
  have hmean : Summable (fun n => Real.exp (-2 * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n)) := by
    have h := perturbed_exponential_decay_summable J hJ1 x hx0p hx 2 2 (by norm_num) e
      (by simpa only [Real.rpow_ofNat] using he)
    simpa only [Real.rpow_ofNat] using h
  have hehigh : Tendsto
      (fun n => (m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n) / x n) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := m)).add he).mul ((stage_inv_tendsto_zero J).pow 2)
    simp only [add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    field_simp [(hxp n).ne', (hjp n).ne']
  have hhigh : Summable (fun n => Real.exp (-b * x n +
      (m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n))) := by
    have h := perturbed_exponential_decay_summable J hJ1 x hx0p hx 0 b hb
      (fun n => m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n)
      (by simpa only [Real.rpow_zero, div_one] using hehigh)
    simpa only [Real.rpow_zero, div_one] using h
  constructor
  · simpa only [e, add_assoc] using hhigh
  · simpa only [e, add_assoc] using hmean

end EulerScale
