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
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialCutoffs

@[expose] public section

noncomputable section

namespace EulerPeriodicProfile

open scoped ContDiff
open Real
open EulerGevrey EulerGevreyInverse EulerGevreyFunctions

/-- Explicit smooth periodic profile with a narrow positive derivative peak. -/
def profile (δ t : ℝ) : ℝ := arctan (sin t / (1 + δ - cos t))

/-- Denominator of the derivative of the periodic profile. -/
def denominator (δ t : ℝ) : ℝ := (1 + δ) ^ 2 - 2 * (1 + δ) * cos t + 1

theorem first_denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < 1 + δ - cos t := by
  linarith [cos_le_one t]

theorem denominator_lower (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) : δ ^ 2 ≤ denominator δ t := by
  have h := mul_nonneg (show 0 ≤ 2 * (1 + δ) by positivity) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < denominator δ t :=
  lt_of_lt_of_le (sq_pos_of_pos hδ) (denominator_lower δ hδ.le t)

theorem profile_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (profile δ) := by
  apply contDiff_arctan.comp
  exact contDiff_sin.div ((contDiff_const.add contDiff_const).sub contDiff_cos)
    (fun t => (first_denominator_pos δ hδ t).ne')

theorem profile_odd (δ t : ℝ) : profile δ (-t) = -profile δ t := by
  simp [profile, neg_div]

theorem profile_periodic (δ : ℝ) : Function.Periodic (profile δ) (2 * π) := by
  intro t
  simp [profile, sin_add_two_pi, cos_add_two_pi]

theorem profile_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (profile δ) (((1 + δ) * cos t - 1) / denominator δ t) t := by
  have hd := first_denominator_pos δ hδ t
  have he := denominator_pos δ hδ t
  have hs := sin_sq_add_cos_sq t
  have hg : HasDerivAt (fun x => sin x / (1 + δ - cos x))
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) t := by
    have hfun : (sin / ((fun _ : ℝ => 1 + δ) - cos)) =
        (fun x => sin x / (1 + δ - cos x)) := rfl
    have ht := (hasDerivAt_sin t).div
      ((hasDerivAt_const t (1 + δ)).sub (hasDerivAt_cos t)) hd.ne'
    rw [hfun] at ht
    simpa only [sub_neg_eq_add, zero_add, Pi.sub_apply, Pi.div_apply] using
      ht
  have heq : (1 + (sin t / (1 + δ - cos t)) ^ 2)⁻¹ *
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) =
      ((1 + δ) * cos t - 1) / denominator δ t := by
    have hds : (1 + δ - cos t) ^ 2 + sin t ^ 2 = denominator δ t := by
      dsimp [denominator]
      nlinarith
    have hnum : cos t * (1 + δ - cos t) - sin t * sin t = (1 + δ) * cos t - 1 := by
      nlinarith
    rw [hnum]
    field_simp [hd.ne', he.ne']
    rw [hds]
    ring
  exact hg.arctan.congr_deriv (by simpa only [one_div] using heq)

theorem profile_deriv (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (profile δ) t = ((1 + δ) * cos t - 1) / denominator δ t :=
  (profile_hasDerivAt δ hδ t).deriv

theorem profile_deriv_zero (δ : ℝ) (hδ : 0 < δ) : deriv (profile δ) 0 = δ⁻¹ := by
  rw [profile_deriv δ hδ]
  have he : denominator δ 0 = δ ^ 2 := by simp [denominator]; ring
  rw [he, cos_zero, mul_one]
  ring_nf
  field_simp [hδ.ne']

theorem profile_deriv_lower (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : -1 ≤ deriv (profile δ) t := by
  rw [profile_deriv δ hδ, le_div_iff₀ (denominator_pos δ hδ t)]
  have h := mul_pos (show 0 < 1 + δ by linarith) (first_denominator_pos δ hδ t)
  dsimp [denominator]
  nlinarith

theorem profile_deriv_upper (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : deriv (profile δ) t ≤ δ⁻¹ := by
  rw [profile_deriv δ hδ, inv_eq_one_div,
    div_le_div_iff₀ (denominator_pos δ hδ t) hδ]
  have h := mul_nonneg (mul_nonneg (show 0 ≤ 2 + δ by linarith)
    (show 0 ≤ 1 + δ by linarith)) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem profile_mean_zero (δ : ℝ) : ∫ t in (-π)..π, profile δ t = 0 := by
  have he : (fun t => profile δ (-t)) = fun t => -profile δ t := funext (profile_odd δ)
  have hi := intervalIntegral.integral_comp_neg (f := profile δ) (a := -π) (b := π)
  rw [he, intervalIntegral.integral_neg] at hi
  simp only [neg_neg] at hi
  linarith

theorem denominator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (denominator δ) := by
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_cos)).add contDiff_const)

theorem denominator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv (n + 1) (denominator δ) t| ≤ majorant 4 0 (n + 1) := by
  have he : denominator δ = fun t => ((1 + δ) ^ 2 + 1) - (2 * (1 + δ)) * cos t := by
    funext t
    dsimp [denominator]
    ring
  rw [he, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg,
    iteratedDeriv_const_mul_field, abs_neg, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * (1 + δ) by positivity)]
  have hc := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
    (show 0 ≤ 2 * (1 + δ) by positivity)
  have hp : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    have h : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have hf : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    nlinarith
  dsimp [majorant]
  nlinarith

theorem denominator_inverse_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun t => (denominator δ t)⁻¹) t| ≤
      (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ hδsq).2
    nlinarith
  have hb (t : ℝ) : |(denominator δ t)⁻¹| ≤ (δ ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (denominator_pos δ hδ t))]
    exact inv_anti₀ hδsq (denominator_lower δ hδ.le t)
  have h := reciprocal_gevrey (denominator δ) (denominator_contDiff δ)
    (fun t => (denominator_pos δ hδ t).ne') ((δ ^ 2)⁻¹) 4 (10 * (δ ^ 2)⁻¹)
    hA (by norm_num) (by ring_nf; rfl) hb (denominator_derivative_bound δ hδ.le hδ1) n t
  simpa only [show (4 : ℝ) * (10 * (δ ^ 2)⁻¹) = 40 * (δ ^ 2)⁻¹ by ring] using h

/-- The numerator of the derivative of the explicit periodic profile. -/
def numerator (δ t : ℝ) : ℝ := (1 + δ) * cos t - 1

theorem numerator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (numerator δ) :=
  (contDiff_const.mul contDiff_cos).sub contDiff_const

theorem numerator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv n (numerator δ) t| ≤ 3 := by
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero]
    dsimp [numerator]
    have ht := abs_cos_le_one t
    have h : |(1 + δ) * cos t - 1| ≤ |(1 + δ) * cos t| + |(1 : ℝ)| := abs_sub _ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity), abs_one] at h
    nlinarith
  | succ n =>
    have he : numerator δ = fun t => (-1 : ℝ) + (1 + δ) * cos t := by
      funext t
      dsimp [numerator]
      ring
    rw [he, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity)]
    have h := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
      (show 0 ≤ 1 + δ by positivity)
    nlinarith

theorem profile_gevrey (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (profile δ) t| ≤
      (100 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ (sq_pos_of_pos hδ)).2
    nlinarith
  have hB : 1 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hBi : 0 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hAi : 0 ≤ (δ ^ 2)⁻¹ := by positivity
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, majorant, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have hp := arctan_lt_pi_div_two (sin t / (1 + δ - cos t))
    have hm := neg_pi_div_two_lt_arctan (sin t / (1 + δ - cos t))
    rw [abs_le]
    dsimp [profile]
    constructor <;> nlinarith [pi_le_four]
  | succ n =>
    have hn (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (numerator δ) x‖ ≤
        3 * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      have hp : 1 ≤ (40 * (δ ^ 2)⁻¹) ^ k := one_le_pow₀ hB
      have hf : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by
        have hh : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        nlinarith
      have hb := numerator_derivative_bound δ hδ.le hδ1 k x
      dsimp [majorant]
      nlinarith
    have hi (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (fun t => (denominator δ t)⁻¹) x‖ ≤
        (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        denominator_inverse_bound δ hδ hδ1 k x
    have hp := product_bound (numerator δ) (fun t => (denominator δ t)⁻¹)
      (numerator_contDiff δ) ((denominator_contDiff δ).inv (fun t => (denominator_pos δ hδ t).ne'))
      (40 * (δ ^ 2)⁻¹) 3 (10 * (δ ^ 2)⁻¹) hBi (by norm_num) (by positivity) hn hi n t
    have he : deriv (profile δ) = fun t => numerator δ t * (denominator δ t)⁻¹ := by
      funext t
      rw [profile_deriv δ hδ]
      rfl
    rw [iteratedDeriv_succ', he]
    have hm : majorant (40 * (δ ^ 2)⁻¹) 0 n ≤ majorant (40 * (δ ^ 2)⁻¹) 0 (n + 1) := by
      unfold majorant
      apply mul_le_mul
      · exact pow_le_pow_right₀ hB (by omega)
      · gcongr; omega
      · positivity
      · positivity
    have hp' : |iteratedDeriv n (fun t => numerator δ t * (denominator δ t)⁻¹) t| ≤
        (90 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        show (3 : ℝ) * 3 * (10 * (δ ^ 2)⁻¹) = 90 * (δ ^ 2)⁻¹ by ring] using hp
    exact hp'.trans (mul_le_mul (by nlinarith) hm (majorant_nonneg _ hBi _ _)
      (by positivity))

end EulerPeriodicProfile
