/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Order.Basic

/-!
# Moving sofa: related mathematical developments

* `LeanCert.Contrib.Sinc`.
* `LeanCert.Core.DerivativeIntervals`.
* `LeanCert.Core.Dyadic`.
* `LeanCert.Core.Expr`.
* `LeanCert.Core.Interval`.
* `LeanCert.Core.IntervalRat.Basic`.
* `LeanCert.Core.IntervalRat.LogReduction`.
* `LeanCert.Core.IntervalRat.Transcendental`.
* `LeanCert.Core.Support`.
* `LeanCert.Core.Taylor`.
* `LeanCert.Core.IntervalRat.Taylor`.
* `LeanCert.Core.IntervalReal`.
* `LeanCert.Core.IntervalDyadic`.
* `LeanCert.Core.IntervalRealEndpoints`.
* `LeanCert.Core.TrigReduction`.
* `LeanCert.Core.IntervalRat.TrigReduced`.
* `LeanCert.Engine.Eval.Core`.
* `LeanCert.Engine.Eval.Result`.
* `LeanCert.Engine.Eval.Extended`.
* `LeanCert.Engine.Bounds.Lemmas`.
* `LeanCert.Engine.IntervalEval`.
* `LeanCert.Engine.AD.Basic`.
* `LeanCert.Engine.AD.Transcendental`.
* `LeanCert.Engine.AD.Eval`.
* `LeanCert.Engine.AD.Correctness`.
* `LeanCert.Engine.AD.Computable`.
* `LeanCert.Engine.AD.DomainChecked`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2025 LeanCert Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Differentiability of sinc and dslope

This file proves that the sinc function is differentiable everywhere, including at 0.

## Main results

* `Real.differentiableAt_sinc`: sinc is differentiable at every point
* `Real.hasDerivAt_sinc_zero`: sinc has derivative 0 at x = 0

## Mathematical background

The sinc function is defined as:
- `sinc x = sin x / x` for `x ≠ 0`
- `sinc 0 = 1`

Equivalently, `sinc = dslope sin 0`.

The derivative of sinc at 0 can be computed using Taylor expansion:
- `sin x = x - x³/6 + x⁵/120 - ...`
- `sinc x = 1 - x²/6 + x⁴/120 - ...`
- `sinc'(0) = 0`
-/

public section

open Filter Topology
open scoped Topology

namespace Real

variable {x : ℝ}

/-- Bound on |sin x - x| in terms of |x|³.
For x > 0: sin x < x and x - x³/4 < sin x, so 0 < x - sin x < x³/4.
By symmetry (sin(-x) = -sin(x)), |sin x - x| ≤ |x|³/4 for all x with |x| ≤ 1. -/
theorem abs_sin_sub_self_le (x : ℝ) (_hx : |x| ≤ 1) : |sin x - x| ≤ |x| ^ 3 / 4 := by
  rcases le_or_gt x 0 with hx_neg | hx_pos
  · -- Case x ≤ 0
    have hx' : 0 ≤ -x := neg_nonneg.mpr hx_neg
    rcases eq_or_lt_of_le hx' with hx_zero | hx_pos'
    · -- x = 0
      have : x = 0 := neg_eq_zero.mp hx_zero.symm
      simp [this]
    · -- x < 0, i.e., 0 < -x ≤ 1
      have h1 : sin (-x) < -x := sin_lt hx_pos'
      have h2six : -x - (-x) ^ 3 / 6 < sin (-x) := sin_gt_sub_cube hx_pos'
      have h2 : -x - (-x) ^ 3 / 4 < sin (-x) := by
        have hcubed : 0 < (-x) ^ 3 := pow_pos hx_pos' _
        linarith
      -- sin x = -sin(-x), so sin x - x = -sin(-x) - x
      -- From h1: sin(-x) < -x, so sin(-x) + x < 0
      -- Therefore -sin(-x) - x = -(sin(-x) + x) > 0
      rw [abs_of_nonpos hx_neg]
      have hsinx : sin x = -sin (-x) := by simp [sin_neg]
      rw [hsinx]
      have hsum_pos : 0 < -sin (-x) - x := by linarith
      rw [abs_of_pos hsum_pos]
      -- Goal: -sin(-x) - x ≤ (-x) ^ 3 / 4
      -- From h2: sin(-x) > -x - (-x)^3/4, so -sin(-x) < x + (-x)^3/4
      -- Therefore -sin(-x) - x < (-x)^3/4
      linarith
  · -- Case x > 0
    have h1 : sin x < x := sin_lt hx_pos
    have h2six : x - x ^ 3 / 6 < sin x := sin_gt_sub_cube hx_pos
    have h2 : x - x ^ 3 / 4 < sin x := by
      have hcubed : 0 < x ^ 3 := pow_pos hx_pos _
      linarith
    rw [abs_of_pos hx_pos]
    have hsub_pos : 0 < x - sin x := by linarith
    rw [abs_of_neg (by linarith : sin x - x < 0)]
    linarith

/-- The derivative of sinc at 0 is 0.

The proof uses the squeeze theorem with the bound `|sinc x - 1| ≤ |x|² / 4`,
which follows from sin bounds in Mathlib. -/
theorem hasDerivAt_sinc_zero : HasDerivAt sinc 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- Need to show: Tendsto (slope sinc 0) (𝓝[≠] 0) (𝓝 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use min 1 (ε * 4)
  constructor
  · positivity
  intro y hy_ne hy_dist
  simp only [slope, vsub_eq_sub, sinc_zero, smul_eq_mul, dist_eq_norm, sub_zero] at *
  by_cases hy : y = 0
  · exact absurd hy hy_ne
  rw [Real.norm_eq_abs] at hy_dist ⊢
  rw [abs_mul, abs_inv]
  rw [sinc_of_ne_zero hy, div_sub_one hy, abs_div]
  -- Goal: |y|⁻¹ * (|sin y - y| / |y|) < ε
  -- i.e., |sin y - y| / |y|² < ε
  have hy_le_1 : |y| ≤ 1 := (lt_min_iff.mp hy_dist).1.le
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy
  have hy_sq_pos : 0 < |y| ^ 2 := sq_pos_of_pos hy_abs_pos
  -- |sin y - y| ≤ |y|³/4
  have hbound : |sin y - y| ≤ |y| ^ 3 / 4 := abs_sin_sub_self_le y hy_le_1
  -- |y|⁻¹ * (|sin y - y| / |y|) = |sin y - y| / |y|² ≤ |y|³/4 / |y|² = |y|/4
  calc |y|⁻¹ * (|sin y - y| / |y|)
      = |sin y - y| / |y| ^ 2 := by rw [inv_mul_eq_div, div_div, sq]
    _ ≤ (|y| ^ 3 / 4) / |y| ^ 2 := by
        apply div_le_div_of_nonneg_right hbound
        exact hy_sq_pos.le
    _ = |y| / 4 := by
        have hy_ne : |y| ≠ 0 := ne_of_gt hy_abs_pos
        have hsq : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        field_simp [hy_ne]
    _ < ε := by
        have h_eps : |y| < ε * 4 := (lt_min_iff.mp hy_dist).2
        linarith

theorem differentiableAt_sinc_zero : DifferentiableAt ℝ sinc 0 :=
  hasDerivAt_sinc_zero.differentiableAt

/-- sinc is differentiable everywhere. -/
theorem differentiableAt_sinc (x : ℝ) : DifferentiableAt ℝ sinc x := by
  by_cases hx : x = 0
  · exact hx ▸ differentiableAt_sinc_zero
  · rw [sinc_eq_dslope, differentiableAt_dslope_of_ne hx]
    exact differentiable_sin.differentiableAt

/-- sinc is a differentiable function. -/
theorem differentiable_sinc : Differentiable ℝ sinc := fun x => differentiableAt_sinc x

/-- Integral representation of sinc:
    `sinc x = ∫ t in 0..1, cos (x * t)`.
    This is the standard average-cosine form used for derivative bounds. -/
theorem sinc_eq_integral_cos (x : ℝ) :
    sinc x = ∫ t in (0 : ℝ)..1, cos (x * t) := by
  by_cases hx : x = 0
  · subst hx
    simp [sinc_zero]
  · have hcomp :
      ∫ t in (0 : ℝ)..1, cos (x * t) = x⁻¹ * ∫ u in (0 : ℝ)..x, cos u := by
      simpa [mul_comm] using
        (intervalIntegral.integral_comp_mul_right
          (f := fun u : ℝ => cos u) (a := (0 : ℝ)) (b := 1) (c := x) hx)
    rw [hcomp, integral_cos, sin_zero, sub_zero, inv_mul_eq_div, sinc_of_ne_zero hx]

/-- The derivative of sinc at a nonzero point. -/
theorem hasDerivAt_sinc_of_ne_zero (hx : x ≠ 0) :
    HasDerivAt sinc ((x * cos x - sin x) / x ^ 2) x := by
  have h1 : HasDerivAt sin (cos x) x := hasDerivAt_sin x
  have h2 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun y => sin y / y) ((cos x * x - sin x * 1) / x ^ 2) x :=
    h1.div h2 hx
  simp only [mul_one] at h3
  have h4 : HasDerivAt (fun y => sin y / y) ((x * cos x - sin x) / x ^ 2) x := by
    convert h3 using 1; ring
  -- sinc agrees with sin/id on a neighborhood of x (since x ≠ 0)
  have heq : sinc =ᶠ[𝓝 x] (fun y => sin y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sinc_of_ne_zero hy
  exact h4.congr_of_eventuallyEq heq

/-- The derivative of sinc. For x = 0, deriv sinc 0 = 0. For x ≠ 0, deriv sinc x = (x cos x - sin x)
/ x². -/
theorem deriv_sinc : deriv sinc x = if x = 0 then 0 else (x * cos x - sin x) / x ^ 2 := by
  split_ifs with hx
  · exact hx ▸ hasDerivAt_sinc_zero.deriv
  · exact (hasDerivAt_sinc_of_ne_zero hx).deriv

@[simp]
theorem deriv_sinc_zero : deriv sinc 0 = 0 := hasDerivAt_sinc_zero.deriv

/-
The derivative of sinc is bounded: |sinc'(x)| ≤ 1 for all x.

The key insight is that for x ≠ 0:
- sinc'(x) = (x cos x - sin x) / x²
- Let g(x) = x cos x - sin x. Then g(0) = 0 and g'(x) = -x sin x.
- |g(x)| = |∫₀ˣ -t sin t dt| ≤ ∫₀ˣ |t| dt = x²/2
- Therefore |sinc'(x)| = |g(x)|/x² ≤ 1/2 < 1

The proof using integration is mathematically straightforward but requires
formalizing the integral representation. Instead we use a direct monotonicity argument.
-/

/-- Bound: |x cos x - sin x| ≤ x² for all x.
    Proof uses monotonicity of auxiliary functions on [0, ∞). -/
theorem abs_x_mul_cos_sub_sin_le_sq (x : ℝ) : |x * cos x - sin x| ≤ x ^ 2 := by
  suffices ∀ x ≥ 0, |x * cos x - sin x| ≤ x ^ 2 by
    obtain h | h := le_total 0 x
    · exact this x h
    · rw [← abs_neg, ← neg_sq x]
      convert this (-x) (neg_nonneg.mpr h) using 2
      ring_nf
      simp only [cos_neg, sin_neg]
      ring
  intro x hx
  rw [abs_le]
  constructor
  · -- -x^2 ≤ x cos x - sin x, equivalently 0 ≤ x cos x - sin x + x^2
    -- Define g(t) = t * cos t - sin t + t^2, show g is monotone on [0,∞) with g(0) = 0
    let g : ℝ → ℝ := fun t => t * cos t - sin t + t^2
    have hg_diff : ∀ t, HasDerivAt g (t * (2 - sin t)) t := fun t => by
      have h1 : HasDerivAt (fun t => t * cos t) (1 * cos t + t * (-sin t)) t :=
        hasDerivAt_id t |>.mul (hasDerivAt_cos t)
      have h2 : HasDerivAt (fun t => t * cos t - sin t) (1 * cos t + t * (-sin t) - cos t) t :=
        h1.sub (hasDerivAt_sin t)
      have hpow : HasDerivAt (fun t => t^2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
        exact this
      have h3 : HasDerivAt (fun t => t * cos t - sin t + t^2)
          (1 * cos t + t * (-sin t) - cos t + 2 * t) t :=
        h2.add hpow
      convert h3 using 1
      ring
    have hg_cont : Continuous g :=
      (continuous_id.mul continuous_cos).sub continuous_sin |>.add (continuous_pow 2)
    have hg_diffble : Differentiable ℝ g := fun t => (hg_diff t).differentiableAt
    have hg' : ∀ t, deriv g t = t * (2 - sin t) := fun t => (hg_diff t).deriv
    have hg_nonneg : ∀ t ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv g t := by
      intro t ht
      rw [interior_Ici] at ht
      rw [hg' t]
      apply mul_nonneg (le_of_lt (Set.mem_Ioi.mp ht))
      linarith [sin_le_one t]
    have g_nonneg : 0 ≤ g x := by
      have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hg_cont.continuousOn
        hg_diffble.differentiableOn hg_nonneg
      have hg0 : g 0 = 0 := by simp [g]
      calc 0 = g 0 := hg0.symm
        _ ≤ g x := hmono (by simp : (0:ℝ) ∈ Set.Ici 0) (Set.mem_Ici.mpr hx) hx
    linarith [g_nonneg]
  · -- x cos x - sin x ≤ x^2, equivalently 0 ≤ x^2 - (x cos x - sin x)
    -- Define g(t) = t^2 - (t * cos t - sin t), show g is monotone on [0,∞) with g(0) = 0
    let g : ℝ → ℝ := fun t => t^2 - (t * cos t - sin t)
    have hg_diff : ∀ t, HasDerivAt g (t * (2 + sin t)) t := fun t => by
      have h1 : HasDerivAt (fun t => t * cos t) (1 * cos t + t * (-sin t)) t :=
        hasDerivAt_id t |>.mul (hasDerivAt_cos t)
      have h2 : HasDerivAt (fun t => t * cos t - sin t) (1 * cos t + t * (-sin t) - cos t) t :=
        h1.sub (hasDerivAt_sin t)
      have hpow : HasDerivAt (fun t => t^2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
        exact this
      have h3 : HasDerivAt (fun t => t^2 - (t * cos t - sin t))
          (2 * t - (1 * cos t + t * (-sin t) - cos t)) t :=
        hpow.sub h2
      convert h3 using 1
      ring
    have hg_cont : Continuous g :=
      (continuous_pow 2).sub ((continuous_id.mul continuous_cos).sub continuous_sin)
    have hg_diffble : Differentiable ℝ g := fun t => (hg_diff t).differentiableAt
    have hg' : ∀ t, deriv g t = t * (2 + sin t) := fun t => (hg_diff t).deriv
    have hg_nonneg : ∀ t ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv g t := by
      intro t ht
      rw [interior_Ici] at ht
      rw [hg' t]
      apply mul_nonneg (le_of_lt (Set.mem_Ioi.mp ht))
      linarith [neg_one_le_sin t]
    have g_nonneg : 0 ≤ g x := by
      have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hg_cont.continuousOn
        hg_diffble.differentiableOn hg_nonneg
      have hg0 : g 0 = 0 := by simp [g]
      calc 0 = g 0 := hg0.symm
        _ ≤ g x := hmono (by simp : (0:ℝ) ∈ Set.Ici 0) (Set.mem_Ici.mpr hx) hx
    linarith [g_nonneg]

theorem abs_deriv_sinc_le_one (x : ℝ) : |deriv sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [(hasDerivAt_sinc_of_ne_zero hx).deriv]
    rw [abs_div]
    have hx_sq : x ^ 2 > 0 := sq_pos_of_ne_zero hx
    have habs_sq : |x ^ 2| = x ^ 2 := abs_of_pos hx_sq
    rw [habs_sq, div_le_one hx_sq]
    exact abs_x_mul_cos_sub_sin_le_sq x

/-- deriv sinc x is in [-1, 1] for all x -/
theorem deriv_sinc_mem_Icc (x : ℝ) : deriv sinc x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc]
  have h := abs_deriv_sinc_le_one x
  rw [abs_le] at h
  exact h

/-!
## Integral representation and smoothness of sinc

The sinc function is smooth (C^∞). The key insight is the integral representation:
  sinc(x) = ∫ t in 0..1, cos(t * x) dt

This works because:
- For x ≠ 0: ∫₀¹ cos(tx) dt = [sin(tx)/x]₀¹ = sin(x)/x = sinc(x)
- For x = 0: ∫₀¹ cos(0) dt = ∫₀¹ 1 dt = 1 = sinc(0)

Smoothness follows from differentiation under the integral sign (Leibniz rule):
since cos(t*x) is C^∞ in x and the domain [0,1] is compact, the integral is C^∞.
-/

open MeasureTheory intervalIntegral in
/-- The integral representation of sinc: sinc(x) = ∫ t in 0..1, cos(t * x) -/
theorem sinc_eq_integral (x : ℝ) : sinc x = ∫ t in (0 : ℝ)..1, cos (t * x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · -- Case x = 0: both sides equal 1
    simp only [sinc_zero, mul_zero, cos_zero]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  · -- Case x ≠ 0: use fundamental theorem of calculus
    have hcont : Continuous (fun t => cos (t * x)) := continuous_cos.comp (continuous_mul_const x)
    have hderiv : ∀ t, HasDerivAt (fun u => sin (u * x) / x) (cos (t * x)) t := by
      intro t
      have : HasDerivAt (fun u => sin (u * x)) (x * cos (t * x)) t := by
        have := Real.hasDerivAt_sin (t * x)
        convert! HasDerivAt.comp t this (hasDerivAt_mul_const x) using 1
        ring
      convert! this.div_const x using 1
      field_simp
    -- The antiderivative is sin(tx)/x, which is continuous
    have hcont_anti : ContinuousOn (fun t => sin (t * x) / x) (Set.Icc 0 1) :=
      (continuous_sin.comp (continuous_mul_const x)).continuousOn.div_const x
    -- cos(tx) is interval integrable since it's continuous
    have hint : IntervalIntegrable (fun t => cos (t * x)) volume 0 1 :=
      hcont.intervalIntegrable 0 1
    rw [integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
        hcont_anti (fun t _ => hderiv t) hint]
    simp only [one_mul, zero_mul, sin_zero, zero_div, sub_zero]
    rw [sinc_of_ne_zero hx]

/-- The derivative of sinc equals dslope (cos - sinc) at 0.

For x ≠ 0:
  dslope (cos - sinc) 0 x = (cos x - sinc x) / x = (x cos x - sin x) / x² = deriv sinc x

For x = 0:
  dslope (cos - sinc) 0 0 = deriv (cos - sinc) 0 = -sin 0 - deriv sinc 0 = 0 = deriv sinc 0
-/
theorem deriv_sinc_eq_dslope : deriv sinc = dslope (cos - sinc) 0 := by
  ext x
  by_cases hx : x = 0
  · -- At x = 0
    simp only [hx, dslope_same, deriv_sinc_zero]
    simp only [deriv_sub, differentiableAt_cos, differentiableAt_sinc_zero, deriv_cos, sin_zero,
      deriv_sinc_zero, sub_zero, neg_zero]
  · -- At x ≠ 0
    rw [dslope_of_ne _ hx, slope, vsub_eq_sub]
    simp only [Pi.sub_apply, cos_zero, sinc_zero, sub_self, sub_zero]
    rw [(hasDerivAt_sinc_of_ne_zero hx).deriv]
    rw [sinc_of_ne_zero hx, smul_eq_mul]
    field_simp

/-- sinc is smooth at every nonzero point. -/
theorem contDiffAt_sinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ ⊤ sinc x := by
  have heq : sinc =ᶠ[𝓝 x] fun y => sin y / y := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sinc_of_ne_zero hy
  exact (contDiff_sin.contDiffAt.div contDiff_id.contDiffAt hx).congr_of_eventuallyEq heq

/-- sinc is analytic at 0.

The proof uses the order theory of analytic functions. Since sin is analytic at 0
with order ≥ 1 (because sin(0) = 0), there exists an analytic function g such that
sin(z) = z • g(z) near 0. This g must equal sinc away from 0, and by continuity
of both functions at 0, g = sinc everywhere near 0. Therefore sinc is analytic at 0. -/
theorem analyticAt_sinc_zero : AnalyticAt ℝ sinc 0 := by
  -- sin has order ≥ 1 at 0 because sin(0) = 0 and sin is analytic
  have hsin_an : AnalyticAt ℝ sin 0 := analyticAt_sin
  -- sin(0) = 0 implies order ≠ 0, hence order ≥ 1
  have horder_ne_zero : analyticOrderAt sin (0 : ℝ) ≠ 0 :=
    hsin_an.analyticOrderAt_ne_zero.mpr sin_zero
  -- From the order, we get an analytic g with sin(z) = z * g(z) near 0
  have horder : (1 : ℕ) ≤ analyticOrderAt sin (0 : ℝ) := Order.one_le_iff_ne_zero.mpr horder_ne_zero
  rw [natCast_le_analyticOrderAt hsin_an] at horder
  simp only [pow_one, sub_zero] at horder
  obtain ⟨g, hg_an, hg_eq⟩ := horder
  -- g equals sinc away from 0: from sin z = z • g z, we get g z = sin z / z = sinc z
  have hg_eq_sinc : g =ᶠ[𝓝[≠] 0] sinc := by
    filter_upwards [hg_eq.filter_mono nhdsWithin_le_nhds,
                    self_mem_nhdsWithin] with z hsin_eq hz
    simp only [smul_eq_mul] at hsin_eq
    have hz' : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    rw [sinc_of_ne_zero hz']
    field_simp [hz']
    linarith [hsin_eq]
  -- Since g is continuous at 0 and sinc is continuous at 0,
  -- and they agree on the punctured neighborhood, they agree at 0
  have hg_zero : g 0 = sinc 0 := by
    have hg_cont : ContinuousAt g 0 := hg_an.continuousAt
    have hsinc_cont : ContinuousAt sinc 0 := continuous_sinc.continuousAt
    -- g → g(0) as x → 0, and sinc(x) → sinc(0) as x → 0
    -- Since g(x) = sinc(x) for x ≠ 0 near 0, limits must be equal
    have h : Tendsto g (𝓝[≠] 0) (𝓝 (sinc 0)) := by
      have := hsinc_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      exact this.congr' hg_eq_sinc.symm
    have h2 : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) :=
      hg_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    exact tendsto_nhds_unique h2 h
  -- Now sinc = g near 0, so sinc is analytic at 0
  exact hg_an.congr (hg_eq.mono fun z hsin_eq => by
    simp only [smul_eq_mul] at hsin_eq
    by_cases hz : z = 0
    · simp [hz, hg_zero]
    · rw [sinc_of_ne_zero hz]
      field_simp [hz]
      linarith [hsin_eq])

/-- sinc is analytic at every point. -/
theorem analyticAt_sinc (x : ℝ) : AnalyticAt ℝ sinc x := by
  by_cases hx : x = 0
  · exact hx ▸ analyticAt_sinc_zero
  · exact contDiffAt_sinc_of_ne_zero hx |>.analyticAt

/-- sinc is smooth (infinitely differentiable).

The proof uses that sinc is analytic everywhere (analyticAt_sinc),
and analytic functions are smooth. -/
theorem contDiff_sinc : ContDiff ℝ ⊤ sinc :=
  AnalyticOnNhd.contDiff (fun x _ => analyticAt_sinc x)

/-- sinc is an analytic function. -/
theorem analyticOnNhd_sinc : AnalyticOnNhd ℝ sinc Set.univ := fun x _ => analyticAt_sinc x

end Real

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Derivative Interval Library

This file provides a systematic collection of derivative interval facts for basic functions.
These lemmas establish that derivatives of common functions lie within specified intervals,
which feeds into:
- Monotonicity analysis
- Lipschitz/contractivity bounds
- Newton method analysis
- Global optimization pruning

## Main theorems

### Exp (derivative = exp, always positive)
* `exp_deriv_pos` - exp' x > 0 for all x
* `exp_deriv_interval` - exp' x ∈ [exp a, exp b] for x ∈ [a, b]

### Log (derivative = 1/x on (0, ∞))
* `log_deriv_interval` - log' x ∈ [1/b, 1/a] for x ∈ [a, b] with 0 < a

### Arctan (derivative = 1/(1+x²) ∈ (0, 1])
* `arctan_deriv_interval` - arctan' x ∈ (0, 1] for all x
* `arctan_deriv_mem_Icc` - arctan' x ∈ [0, 1] for all x

### Arsinh (derivative = 1/√(1+x²) ∈ (0, 1])
* `arsinh_deriv_interval` - arsinh' x ∈ (0, 1] for all x
* `arsinh_deriv_mem_Icc` - arsinh' x ∈ [0, 1] for all x

### Sin/Cos (derivatives bounded by 1)
* `sin_deriv_interval` - |sin' x| = |cos x| ≤ 1
* `cos_deriv_interval` - |cos' x| = |sin x| ≤ 1

### Sinh/Cosh (derivative relationships)
* `sinh_deriv_eq_cosh` - sinh' = cosh
* `cosh_deriv_eq_sinh` - cosh' = sinh
* `cosh_deriv_interval` - cosh' x = sinh x, monotonicity facts

## Design notes

These lemmas are independent of any specific algorithm; they're just facts about functions.
They're designed to be composable with the chain rule for AD correctness proofs.
-/

/-! ### Exp derivative intervals -/

public section

namespace LeanCert.Core.DerivativeIntervals

open Real Set

/-- The derivative of exp is positive everywhere -/
theorem exp_deriv_pos (x : ℝ) : 0 < deriv exp x := by
  rw [Real.deriv_exp]
  exact Real.exp_pos x

/-- exp is strictly increasing (follows from positive derivative) -/
theorem exp_strictMono : StrictMono exp := Real.exp_strictMono

/-- For x ∈ [a, b], we have exp' x = exp x ∈ [exp a, exp b] -/
theorem exp_deriv_interval {a b x : ℝ} (hx : x ∈ Icc a b) :
    deriv exp x ∈ Icc (exp a) (exp b) := by
  rw [Real.deriv_exp]
  exact ⟨exp_le_exp.mpr hx.1, exp_le_exp.mpr hx.2⟩

/-! ### Log derivative intervals -/

/-- The derivative of log at x > 0 is x⁻¹ -/
theorem log_deriv_eq_inv {x : ℝ} (_hx : 0 < x) : deriv log x = x⁻¹ :=
  Real.deriv_log x

/-- For x ∈ [a, b] with 0 < a ≤ b, we have log' x = 1/x ∈ [1/b, 1/a] -/
theorem log_deriv_interval {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Icc a b) :
    deriv log x ∈ Icc (b⁻¹) (a⁻¹) := by
  have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
  rw [log_deriv_eq_inv hx_pos]
  constructor
  · exact inv_anti₀ hx_pos hx.2
  · have ha_le_x : a ≤ x := hx.1
    exact inv_anti₀ ha ha_le_x

/-- log is strictly increasing on (0, ∞) -/
theorem log_strictMonoOn : StrictMonoOn log (Ioi 0) := Real.strictMonoOn_log

/-! ### Arctan derivative intervals -/

/-- The derivative of arctan at x is 1/(1+x²) -/
theorem arctan_deriv_eq (x : ℝ) : deriv arctan x = (1 + x ^ 2)⁻¹ :=
  (Real.hasDerivAt_arctan' x).deriv

/-- 1/(1+x²) is always positive -/
theorem arctan_deriv_pos (x : ℝ) : 0 < deriv arctan x := by
  rw [arctan_deriv_eq]
  exact inv_pos.mpr (by nlinarith [sq_nonneg x])

/-- 1/(1+x²) ≤ 1 for all x -/
theorem arctan_deriv_le_one (x : ℝ) : deriv arctan x ≤ 1 := by
  rw [arctan_deriv_eq]
  have h : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  exact inv_le_one_of_one_le₀ h

/-- arctan' x ∈ (0, 1] for all x -/
theorem arctan_deriv_interval (x : ℝ) : deriv arctan x ∈ Ioc 0 1 :=
  ⟨arctan_deriv_pos x, arctan_deriv_le_one x⟩

/-- arctan' x ∈ [0, 1] for all x (closed interval version for interval arithmetic) -/
theorem arctan_deriv_mem_Icc (x : ℝ) : deriv arctan x ∈ Icc 0 1 :=
  ⟨le_of_lt (arctan_deriv_pos x), arctan_deriv_le_one x⟩

/-- arctan is strictly increasing (follows from positive derivative) -/
theorem arctan_strictMono : StrictMono arctan := Real.arctan_strictMono

/-! ### Arsinh derivative intervals -/

/-- The derivative of arsinh at x is (√(1+x²))⁻¹ -/
theorem arsinh_deriv_eq (x : ℝ) : deriv arsinh x = (sqrt (1 + x ^ 2))⁻¹ := by
  have h := Real.hasDerivAt_arsinh x
  rw [h.deriv]

/-- √(1+x²) ≥ 1 for all x -/
theorem sqrt_one_add_sq_ge_one (x : ℝ) : 1 ≤ sqrt (1 + x ^ 2) := by
  have h : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  calc sqrt (1 + x ^ 2) ≥ sqrt 1 := sqrt_le_sqrt h
    _ = 1 := sqrt_one

/-- √(1+x²) > 0 for all x -/
theorem sqrt_one_add_sq_pos (x : ℝ) : 0 < sqrt (1 + x ^ 2) := by
  apply sqrt_pos.mpr
  nlinarith [sq_nonneg x]

/-- arsinh' x > 0 for all x -/
theorem arsinh_deriv_pos (x : ℝ) : 0 < deriv arsinh x := by
  rw [arsinh_deriv_eq]
  exact inv_pos.mpr (sqrt_one_add_sq_pos x)

/-- arsinh' x ≤ 1 for all x -/
theorem arsinh_deriv_le_one (x : ℝ) : deriv arsinh x ≤ 1 := by
  rw [arsinh_deriv_eq]
  exact inv_le_one_of_one_le₀ (sqrt_one_add_sq_ge_one x)

/-- arsinh' x ∈ (0, 1] for all x -/
theorem arsinh_deriv_interval (x : ℝ) : deriv arsinh x ∈ Ioc 0 1 :=
  ⟨arsinh_deriv_pos x, arsinh_deriv_le_one x⟩

/-- arsinh' x ∈ [0, 1] for all x (closed interval version) -/
theorem arsinh_deriv_mem_Icc (x : ℝ) : deriv arsinh x ∈ Icc 0 1 :=
  ⟨le_of_lt (arsinh_deriv_pos x), arsinh_deriv_le_one x⟩

/-- arsinh is strictly increasing -/
theorem arsinh_strictMono : StrictMono arsinh := Real.arsinh_strictMono

/-! ### Sin derivative intervals -/

/-- The derivative of sin is cos -/
theorem sin_deriv_eq (x : ℝ) : deriv sin x = cos x := by
  have h := Real.deriv_sin
  exact congrFun h x

/-- |sin' x| = |cos x| ≤ 1 -/
theorem sin_deriv_abs_le_one (x : ℝ) : |deriv sin x| ≤ 1 := by
  rw [sin_deriv_eq]
  exact abs_cos_le_one x

/-- sin' x ∈ [-1, 1] for all x -/
theorem sin_deriv_mem_Icc (x : ℝ) : deriv sin x ∈ Icc (-1) 1 := by
  rw [sin_deriv_eq]
  exact ⟨neg_one_le_cos x, cos_le_one x⟩

/-! ### Cos derivative intervals -/

/-- The derivative of cos is -sin -/
theorem cos_deriv_eq (x : ℝ) : deriv cos x = -sin x := by
  have h := Real.deriv_cos'
  exact congrFun h x

/-- |cos' x| = |sin x| ≤ 1 -/
theorem cos_deriv_abs_le_one (x : ℝ) : |deriv cos x| ≤ 1 := by
  rw [cos_deriv_eq, abs_neg]
  exact abs_sin_le_one x

/-- cos' x ∈ [-1, 1] for all x -/
theorem cos_deriv_mem_Icc (x : ℝ) : deriv cos x ∈ Icc (-1) 1 := by
  rw [cos_deriv_eq]
  constructor
  · simp only [neg_le_neg_iff]; exact sin_le_one x
  · have h := neg_one_le_sin x; linarith

/-! ### Sinh derivative intervals -/

/-- The derivative of sinh is cosh -/
theorem sinh_deriv_eq (x : ℝ) : deriv sinh x = cosh x := by
  have h := Real.deriv_sinh
  exact congrFun h x

/-- sinh' x = cosh x ≥ 1 for all x -/
theorem sinh_deriv_ge_one (x : ℝ) : 1 ≤ deriv sinh x := by
  rw [sinh_deriv_eq]
  exact Real.one_le_cosh x

/-- sinh' x > 0 for all x -/
theorem sinh_deriv_pos (x : ℝ) : 0 < deriv sinh x := by
  have h := sinh_deriv_ge_one x
  linarith

/-- sinh is strictly increasing -/
theorem sinh_strictMono : StrictMono sinh := Real.sinh_strictMono

/-! ### Cosh derivative intervals -/

/-- The derivative of cosh is sinh -/
theorem cosh_deriv_eq (x : ℝ) : deriv cosh x = sinh x := by
  have h := Real.deriv_cosh
  exact congrFun h x

/-- cosh' 0 = sinh 0 = 0 -/
theorem cosh_deriv_zero : deriv cosh 0 = 0 := by
  rw [cosh_deriv_eq, Real.sinh_zero]

/-- For x > 0, cosh' x = sinh x > 0 -/
theorem cosh_deriv_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < deriv cosh x := by
  rw [cosh_deriv_eq]
  exact Real.sinh_pos_iff.mpr hx

/-- For x < 0, cosh' x = sinh x < 0 -/
theorem cosh_deriv_neg_of_neg {x : ℝ} (hx : x < 0) : deriv cosh x < 0 := by
  rw [cosh_deriv_eq]
  exact Real.sinh_neg_iff.mpr hx

/-- cosh is strictly decreasing on (-∞, 0] -/
theorem cosh_strictAntiOn_nonpos : StrictAntiOn cosh (Iic 0) := by
  intro x hx y hy hxy
  simp only [mem_Iic] at hx hy
  -- Use that cosh is even and decreasing on negative reals
  calc cosh y = cosh (-(-y)) := by ring_nf
    _ = cosh (-y) := by rw [Real.cosh_neg]
    _ < cosh (-x) := by
        apply Real.cosh_strictMonoOn
        · simp only [mem_Ici]; linarith
        · simp only [mem_Ici]; linarith
        · linarith
    _ = cosh x := by rw [Real.cosh_neg]

/-- cosh is strictly increasing on [0, ∞) -/
theorem cosh_strictMonoOn_nonneg : StrictMonoOn cosh (Ici 0) :=
  Real.cosh_strictMonoOn

end LeanCert.Core.DerivativeIntervals

/-! ## One-Sided Taylor Bounds

For convex functions, the Taylor polynomial provides a one-sided bound.
For exp on [0, ∞), the n-th Taylor polynomial is a lower bound.
For concave functions, similar upper bounds hold.

These bounds are tighter than symmetric remainder bounds at endpoints,
which is important for verified numerics.
-/

namespace LeanCert.Core.OneSidedTaylor

open Real Set

/-! ### Exp lower bounds (convexity gives Taylor poly ≤ function) -/

/-- 1 ≤ exp x for x ≥ 0 (Taylor degree 0) -/
theorem one_le_exp_of_nonneg (x : ℝ) (hx : 0 ≤ x) : 1 ≤ exp x :=
  Real.one_le_exp hx

/-- 1 + x ≤ exp x for all x (Taylor degree 1) -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ exp x := by
  have h := add_one_le_exp x
  linarith

/-- x + 1 ≤ exp x for all x (alternate form) -/
theorem add_one_le_exp' (x : ℝ) : x + 1 ≤ exp x :=
  add_one_le_exp x

/-! ### Monotonicity from derivative bounds

These wrap the Mathlib lemmas for convenience with our naming. -/

/-- If f' ≥ 0 on [a, b], then f is monotone increasing on [a, b] -/
theorem monotoneOn_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) :
    MonotoneOn f (Icc a b) := by
  refine _root_.monotoneOn_of_deriv_nonneg (convex_Icc a b) hf ?_ ?_
  · rw [interior_Icc]; exact hf'
  · intro x hx; rw [interior_Icc] at hx; exact hderiv x hx

/-- If f' > 0 on (a, b), then f is strictly monotone on [a, b] -/
theorem strictMonoOn_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (_hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Icc a b) := by
  refine _root_.strictMonoOn_of_deriv_pos (convex_Icc a b) hf ?_
  intro x hx; rw [interior_Icc] at hx; exact hderiv x hx

/-- If f' ≤ 0 on [a, b], then f is antitone (monotone decreasing) on [a, b] -/
theorem antitoneOn_of_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv f x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  refine _root_.antitoneOn_of_deriv_nonpos (convex_Icc a b) hf ?_ ?_
  · rw [interior_Icc]; exact hf'
  · intro x hx; rw [interior_Icc] at hx; exact hderiv x hx

/-- If f' < 0 on (a, b), then f is strictly antitone on [a, b] -/
theorem strictAntiOn_of_deriv_neg {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (_hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv f x < 0) :
    StrictAntiOn f (Icc a b) := by
  refine _root_.strictAntiOn_of_deriv_neg (convex_Icc a b) hf ?_
  intro x hx; rw [interior_Icc] at hx; exact hderiv x hx

end LeanCert.Core.OneSidedTaylor

end

end

section

/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Dyadic Rationals (n * 2^e)

This file defines Dyadic rationals, which are the backbone of high-performance
verified numerics. Unlike arbitrary `Rat`, Dyadics do not require GCD
normalization, making them significantly faster for kernel evaluation.

## Main definitions

* `Dyadic` - A dyadic rational number: `mantissa * 2^exponent`
* `Dyadic.toRat` - Convert to standard rational
* `Dyadic.add`, `Dyadic.mul`, `Dyadic.neg` - Arithmetic operations
* `Dyadic.shiftDown`, `Dyadic.shiftUp` - Directed rounding for interval bounds

## Design notes

Dyadics use power-of-2 multiplications instead of GCD-based normalization.
This makes them orders of magnitude faster for kernel evaluation via
`native_decide`, since 2^n can be computed by simple bit operations.

For interval arithmetic, we use directed rounding:
- Lower bounds use `shiftDown` (round toward -∞)
- Upper bounds use `shiftUp` (round toward +∞)

This ensures mathematical soundness even when truncating precision.
-/

public section

namespace LeanCert.Core

/-- A Dyadic rational number: `mantissa * 2^exponent`

This representation allows fast arithmetic without GCD normalization. -/
structure Dyadic where
  /-- The significand/mantissa -/
  mantissa : Int
  /-- The exponent (power of 2) -/
  exponent : Int
  deriving Repr, DecidableEq, Inhabited

namespace Dyadic

/-! ### Helper: Power of 2 -/

/-- Compute 2^n for natural n -/
def pow2Nat (n : Nat) : Nat := Nat.shiftLeft 1 n

/-- Shift an integer left by n bits (multiply by 2^n) -/
def shiftLeftInt (m : Int) (n : Nat) : Int :=
  m * (pow2Nat n : Int)

/-- Shift an integer right by n bits (divide by 2^n, floor toward -∞) -/
def shiftRightInt (m : Int) (n : Nat) : Int :=
  m / (pow2Nat n : Int)

/-- Check if any of the low n bits are set -/
def hasLowBits (m : Int) (n : Nat) : Bool :=
  m % (pow2Nat n : Int) ≠ 0

/-! ### Conversion to Rat -/

/-- Convert Dyadic to standard Rat.

For non-negative exponents: `mantissa * 2^exponent`
For negative exponents: `mantissa / 2^(-exponent)` -/
@[expose]
def toRat (d : Dyadic) : ℚ :=
  if d.exponent ≥ 0 then
    d.mantissa * (pow2Nat d.exponent.toNat : ℤ)
  else
    (d.mantissa : ℚ) / (pow2Nat (-d.exponent).toNat : ℕ)

instance : Coe Dyadic ℚ where coe := toRat

/-- Equality of represented values, ignoring noncanonical mantissa/exponent pairs. -/
@[expose]
def ValueEq (d₁ d₂ : Dyadic) : Prop := d₁.toRat = d₂.toRat

instance (d₁ d₂ : Dyadic) : Decidable (d₁.ValueEq d₂) :=
  inferInstanceAs (Decidable (d₁.toRat = d₂.toRat))

instance : Setoid Dyadic where
  r := ValueEq
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

@[simp] theorem valueEq_iff (d₁ d₂ : Dyadic) :
    d₁.ValueEq d₂ ↔ d₁.toRat = d₂.toRat := Iff.rfl

/-- A lawful identity key for caches, sets, serialization, and deduplication.

Arithmetic keeps the fast, noncanonical `Dyadic` representation. Converting at
an identity boundary collapses all representations of the same rational value.
-/
structure CanonicalKey where
  /-- The exact rational value used to compare normalized dyadic numbers. -/
  value : ℚ
  deriving Repr, DecidableEq, BEq, Hashable

/-- Convert a dyadic value to its canonical identity key. -/
@[expose]
def canonicalKey (d : Dyadic) : CanonicalKey := ⟨d.toRat⟩

@[simp] theorem canonicalKey_value (d : Dyadic) : d.canonicalKey.value = d.toRat := rfl

/-- Canonical keys agree exactly when represented dyadic values agree. -/
theorem canonicalKey_eq_iff (d₁ d₂ : Dyadic) :
    d₁.canonicalKey = d₂.canonicalKey ↔ d₁.ValueEq d₂ := by
  simp only [canonicalKey, ValueEq, CanonicalKey.mk.injEq]

/-- Cast a Dyadic to ℝ by going through ℚ -/
def toReal (d : Dyadic) : ℝ := Rat.cast (toRat d)

instance : Coe Dyadic ℝ where coe := toReal

/-- Equality of rational denotations gives semantic dyadic equality. -/
theorem valueEq_of_toRat_eq {d₁ d₂ : Dyadic}
    (h : d₁.toRat = d₂.toRat) : d₁.ValueEq d₂ := h

/-! ### Construction -/

/-- Create a dyadic from an integer (exponent = 0) -/
def ofInt (i : Int) : Dyadic := ⟨i, 0⟩

/-- Create a dyadic for 2^n -/
def pow2 (n : Int) : Dyadic := ⟨1, n⟩

/-- Zero as a Dyadic -/
@[expose]
def zero : Dyadic := ⟨0, 0⟩

/-- One as a Dyadic -/
def one : Dyadic := ⟨1, 0⟩

instance : Zero Dyadic where zero := Dyadic.zero
instance : One Dyadic where one := Dyadic.one

theorem toRat_ofInt (i : Int) : (ofInt i).toRat = i := by
  simp only [ofInt, toRat, pow2Nat, Int.toNat_zero, le_refl, ↓reduceIte]
  have h : Nat.shiftLeft 1 0 = 1 := rfl
  simp only [h, Nat.cast_one, Int.cast_one, mul_one]

@[simp]
theorem toRat_zero : (0 : Dyadic).toRat = 0 := by
  have h := toRat_ofInt 0; rw [Int.cast_zero] at h; exact h

@[simp]
theorem toRat_one : (1 : Dyadic).toRat = 1 := by
  have h := toRat_ofInt 1; rw [Int.cast_one] at h; exact h

/-! ### Arithmetic Operations -/

/-- Negation of a Dyadic -/
def neg (d : Dyadic) : Dyadic := ⟨-d.mantissa, d.exponent⟩

instance : Neg Dyadic where neg := Dyadic.neg

/-- Addition of Dyadics. Aligns exponents by shifting the mantissa with
larger exponent to match the smaller one. -/
def add (d₁ d₂ : Dyadic) : Dyadic :=
  if d₁.exponent ≤ d₂.exponent then
    let shift := (d₂.exponent - d₁.exponent).toNat
    ⟨d₁.mantissa + shiftLeftInt d₂.mantissa shift, d₁.exponent⟩
  else
    let shift := (d₁.exponent - d₂.exponent).toNat
    ⟨shiftLeftInt d₁.mantissa shift + d₂.mantissa, d₂.exponent⟩

instance : Add Dyadic where add := Dyadic.add

/-- Subtraction of Dyadics -/
def sub (d₁ d₂ : Dyadic) : Dyadic := add d₁ (neg d₂)

instance : Sub Dyadic where sub := Dyadic.sub

/-- Multiplication of Dyadics. Simply multiplies mantissas and adds exponents. -/
def mul (d₁ d₂ : Dyadic) : Dyadic :=
  ⟨d₁.mantissa * d₂.mantissa, d₁.exponent + d₂.exponent⟩

instance : Mul Dyadic where mul := Dyadic.mul

/-- Absolute value of a Dyadic -/
def abs (d : Dyadic) : Dyadic := ⟨Int.natAbs d.mantissa, d.exponent⟩

/-- Scale by a power of 2 (efficient: just adjusts exponent) -/
def scale2 (d : Dyadic) (n : Int) : Dyadic := ⟨d.mantissa, d.exponent + n⟩

/-! ### Directed Rounding for Interval Arithmetic -/

/-- Shift a dyadic to a new (larger) exponent with "Down" rounding (for lower bounds).

If `newExp > d.exponent`, we lose precision by right-shifting the mantissa.
Bits are discarded (floor division toward -∞). -/
def shiftDown (d : Dyadic) (newExp : Int) : Dyadic :=
  if newExp ≤ d.exponent then
    d -- already at or below target precision
  else
    let diff := (newExp - d.exponent).toNat
    -- Integer division is floor division toward -∞ for positive divisor
    ⟨shiftRightInt d.mantissa diff, newExp⟩

/-- Shift a dyadic to a new (larger) exponent with "Up" rounding (for upper bounds).

If `newExp > d.exponent`, we lose precision by right-shifting the mantissa.
If any bits are lost, we add 1 to ensure upward rounding (ceiling toward +∞). -/
def shiftUp (d : Dyadic) (newExp : Int) : Dyadic :=
  if newExp ≤ d.exponent then
    d -- already at or below target precision
  else
    let diff := (newExp - d.exponent).toNat
    if hasLowBits d.mantissa diff then
      -- Lost bits: round up
      ⟨shiftRightInt d.mantissa diff + 1, newExp⟩
    else
      -- No lost bits: exact
      ⟨shiftRightInt d.mantissa diff, newExp⟩

/-! ### Normalization (Mantissa Control) -/

/-- Get the bit length of a natural number -/
def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Get the bit length of the absolute value of an integer -/
def bitLength (m : Int) : Nat := natBitLength m.natAbs

/-- Normalize a Dyadic to keep the mantissa within a reasonable bit-limit.

This prevents mantissas from growing without bound during repeated multiplications.
Similar to how hardware floats work, but with directed rounding.

- `maxBits`: Maximum allowed bits for mantissa (default 256)
- `roundUp`: If true, round toward +∞; if false, round toward -∞ -/
def normalize (d : Dyadic) (maxBits : Nat := 256) (roundUp : Bool := false) : Dyadic :=
  let bits := bitLength d.mantissa
  if bits ≤ maxBits then d
  else
    let shift := bits - maxBits
    let newExp := d.exponent + shift
    if roundUp then shiftUp d newExp
    else shiftDown d newExp

/-- Normalize for lower bounds (round down) -/
def normalizeDown (d : Dyadic) (maxBits : Nat := 256) : Dyadic :=
  normalize d maxBits false

/-- Normalize for upper bounds (round up) -/
def normalizeUp (d : Dyadic) (maxBits : Nat := 256) : Dyadic :=
  normalize d maxBits true

/-! ### Comparison -/

/-- Compare two Dyadics (decidable) -/
def compare (d₁ d₂ : Dyadic) : Ordering :=
  -- Align to smaller exponent for comparison
  if d₁.exponent ≤ d₂.exponent then
    let shift := (d₂.exponent - d₁.exponent).toNat
    Ord.compare d₁.mantissa (shiftLeftInt d₂.mantissa shift)
  else
    let shift := (d₁.exponent - d₂.exponent).toNat
    Ord.compare (shiftLeftInt d₁.mantissa shift) d₂.mantissa

instance : Ord Dyadic where compare := Dyadic.compare

/-- Less-than-or-equal for Dyadics -/
def le (d₁ d₂ : Dyadic) : Bool := compare d₁ d₂ != .gt

/-- Less-than for Dyadics -/
def lt (d₁ d₂ : Dyadic) : Bool := compare d₁ d₂ == .lt

instance : LE Dyadic where le d₁ d₂ := le d₁ d₂
instance : LT Dyadic where lt d₁ d₂ := lt d₁ d₂

instance : DecidableRel (α := Dyadic) (· ≤ ·) := fun d₁ d₂ =>
  if h : le d₁ d₂ then isTrue h else isFalse h

instance : DecidableRel (α := Dyadic) (· < ·) := fun d₁ d₂ =>
  if h : lt d₁ d₂ then isTrue h else isFalse h

/-- Minimum of two Dyadics -/
def min (d₁ d₂ : Dyadic) : Dyadic := if le d₁ d₂ then d₁ else d₂

/-- Maximum of two Dyadics -/
def max (d₁ d₂ : Dyadic) : Dyadic := if le d₁ d₂ then d₂ else d₁

/-- Minimum of four Dyadics -/
def min4 (a b c d : Dyadic) : Dyadic := min (min a b) (min c d)

/-- Maximum of four Dyadics -/
def max4 (a b c d : Dyadic) : Dyadic := max (max a b) (max c d)

/-! ### Correctness Theorems -/

/-! #### Helper lemmas for shift proofs -/

/-- shiftRightInt is floor division by 2^n -/
private theorem shiftRightInt_eq_div (m : Int) (n : Nat) :
    shiftRightInt m n = m / (pow2Nat n : Int) := by
  simp only [shiftRightInt, pow2Nat]

/-- shiftLeftInt is multiplication by 2^n -/
private theorem shiftLeftInt_eq_mul (m : Int) (n : Nat) :
    shiftLeftInt m n = m * (pow2Nat n : Int) := by
  simp only [shiftLeftInt, pow2Nat]

/-- pow2Nat n is always positive.
    Proof: 2^n ≥ 1 for all n. -/
private theorem pow2Nat_pos (n : Nat) : 0 < pow2Nat n := by
  unfold pow2Nat
  -- Use the fact that shiftLeft 1 n = 2^n
  conv => lhs; rw [show (0 : ℕ) = 0 from rfl]
  conv => rhs; rw [show Nat.shiftLeft 1 n = 1 * 2^n from Nat.shiftLeft_eq 1 n]
  simp only [one_mul]
  exact Nat.one_le_two_pow

/-- pow2Nat as Int is positive -/
private theorem pow2Nat_int_pos (n : Nat) : (0 : Int) < (pow2Nat n : Int) := by
  exact Int.natCast_pos.mpr (pow2Nat_pos n)

/-- Floor division property: (m / d) * d ≤ m for positive d.
    Follows from m % d ≥ 0 and m = m % d + d * (m / d). -/
private theorem int_ediv_mul_le (m : Int) (d : Int) (hd : 0 < d) :
    (m / d) * d ≤ m := Int.ediv_mul_le m (ne_of_gt hd)

/-- Ceiling division property: m ≤ (m / d + 1) * d when m % d ≠ 0 -/
private theorem int_ediv_add_one_mul_ge (m : Int) (d : Int) (hd : 0 < d) (_hrem : m % d ≠ 0) :
    m ≤ (m / d + 1) * d := by
  -- From Int.emod_add_mul_ediv: m % d + d * (m / d) = m
  have h := Int.emod_add_mul_ediv m d
  -- m % d < d since d > 0
  have hlt := Int.emod_lt_of_pos m hd
  -- d + d * (m / d) = (m / d + 1) * d
  have heq : d + d * (m / d) = (m / d + 1) * d := by
    rw [add_mul, one_mul, mul_comm d (m / d), add_comm]
  -- m = m % d + d * (m / d) < d + d * (m / d) = (m / d + 1) * d
  have hcalc : m < (m / d + 1) * d :=
    calc m = m % d + d * (m / d) := h.symm
      _ < d + d * (m / d) := by gcongr 1
      _ = (m / d + 1) * d := heq
  exact le_of_lt hcalc

/-- Exact division: m = (m / d) * d when m % d = 0 -/
private theorem int_ediv_mul_eq (m : Int) (d : Int) (_hd : 0 < d) (hrem : m % d = 0) :
    (m / d) * d = m := by
  -- From Int.emod_add_mul_ediv: m % d + d * (m / d) = m
  have h := Int.emod_add_mul_ediv m d
  -- Since m % d = 0, we have d * (m / d) = m
  simp only [hrem, zero_add] at h
  -- d * (m / d) = m, so (m / d) * d = m
  calc (m / d) * d = d * (m / d) := mul_comm _ _
    _ = m := h

theorem toRat_neg (d : Dyadic) : (neg d).toRat = -(d.toRat) := by
  by_cases h : d.exponent ≥ 0
  · simp [neg, toRat, h]
  · simp only [toRat, neg, ge_iff_le, h, ↓reduceIte, Int.cast_neg]
    rw [neg_div]

/-! ### Arithmetic Homomorphisms -/

/-- Helper: pow2Nat n = 2^n -/
private theorem pow2Nat_eq_pow (n : Nat) : pow2Nat n = 2 ^ n := by
  unfold pow2Nat
  rw [show Nat.shiftLeft 1 n = 1 * 2^n from Nat.shiftLeft_eq 1 n]
  simp only [one_mul]

/-- Unification lemma: toRat d = d.mantissa * 2^d.exponent -/
theorem toRat_eq (d : Dyadic) : d.toRat = d.mantissa * (2 : ℚ) ^ d.exponent := by
  unfold toRat
  split_ifs with h
  · -- Case: exponent ≥ 0
    have he : d.exponent = (d.exponent.toNat : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [he, zpow_natCast, pow2Nat_eq_pow]
    -- Simplify (↑n : ℤ).toNat = n
    simp only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat,
               Int.toNat_natCast]
  · -- Case: exponent < 0
    push Not at h
    have hpos : 0 ≤ -d.exponent := Int.neg_nonneg.mpr (le_of_lt h)
    -- (-d.exponent).toNat = the natural number n such that d.exponent = -n
    set n := (-d.exponent).toNat with hn_def
    have hne : d.exponent = -(n : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]; omega
    rw [hne, zpow_neg, zpow_natCast, pow2Nat_eq_pow]
    -- Goal: mantissa / 2^n = mantissa * (2^n)⁻¹
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

theorem toRat_add (d₁ d₂ : Dyadic) : (add d₁ d₂).toRat = d₁.toRat + d₂.toRat := by
  -- Rewrite using toRat_eq to work with mantissa * 2^exponent form
  rw [toRat_eq d₁, toRat_eq d₂]
  unfold add
  split_ifs with h
  · -- Case: d₁.exponent ≤ d₂.exponent
    rw [toRat_eq]
    simp only [shiftLeftInt, pow2Nat_eq_pow]
    -- Goal: (m₁ + m₂ * 2^shift) * 2^e₁ = m₁ * 2^e₁ + m₂ * 2^e₂
    set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
    have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
      rw [hshift_def, Int.toNat_of_nonneg]; omega
    -- 2^shift * 2^e₁ = 2^e₂
    have hexp : (2 : ℚ) ^ shift * 2 ^ d₁.exponent = 2 ^ d₂.exponent := by
      have h2 : (2 : ℚ) ^ shift = (2 : ℚ) ^ (shift : ℤ) := by rw [zpow_natCast]
      rw [h2, ← zpow_add₀ (two_ne_zero), hshift]
      congr 1; omega
    -- Show ↑(2^shift : ℕ) = (2 : ℚ)^shift
    have hcast : (↑(2 ^ shift : ℕ) : ℚ) = (2 : ℚ) ^ shift := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    -- Push casts inside and simplify
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hcast, add_mul, mul_assoc, hexp]
  · -- Case: d₁.exponent > d₂.exponent
    rw [toRat_eq]
    simp only [shiftLeftInt, pow2Nat_eq_pow]
    set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
    have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
      rw [hshift_def, Int.toNat_of_nonneg]; omega
    have hexp : (2 : ℚ) ^ shift * 2 ^ d₂.exponent = 2 ^ d₁.exponent := by
      have h2 : (2 : ℚ) ^ shift = (2 : ℚ) ^ (shift : ℤ) := by rw [zpow_natCast]
      rw [h2, ← zpow_add₀ (two_ne_zero), hshift]
      congr 1; omega
    have hcast : (↑(2 ^ shift : ℕ) : ℚ) = (2 : ℚ) ^ shift := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hcast, add_mul, mul_assoc, hexp,
      add_comm]

theorem toRat_mul (d₁ d₂ : Dyadic) : (mul d₁ d₂).toRat = d₁.toRat * d₂.toRat := by
  -- Key: (m1*m2) * 2^(e1+e2) = (m1*2^e1) * (m2*2^e2)
  rw [toRat_eq d₁, toRat_eq d₂, toRat_eq]
  unfold mul
  simp only [Int.cast_mul]
  -- Goal: (m₁ * m₂) * 2^(e₁ + e₂) = (m₁ * 2^e₁) * (m₂ * 2^e₂)
  -- Use zpow_add₀: 2^(e₁ + e₂) = 2^e₁ * 2^e₂
  rw [zpow_add₀ (two_ne_zero)]
  -- Goal: (a * b) * (c * d) = (a * c) * (b * d)
  -- Use mul_mul_mul_comm: a * b * (c * d) = a * c * (b * d)
  rw [mul_mul_mul_comm]

/-! ### Rounding Properties -/

/-- shiftDown produces a value ≤ the original -/
theorem toRat_shiftDown_le (d : Dyadic) (newExp : Int) :
    (shiftDown d newExp).toRat ≤ d.toRat := by
  simp only [shiftDown]
  split_ifs with h
  · exact le_refl _
  · -- newExp > d.exponent
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow]
    -- Use int_ediv_mul_le: (m / b) * b ≤ m
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hdiv : d.mantissa / (2 ^ diff : ℕ) * (2 ^ diff : ℕ) ≤ d.mantissa :=
      int_ediv_mul_le d.mantissa (2 ^ diff : ℕ) hpow_int_pos
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    -- Goal: (m / 2^diff) * (2^d.exp * 2^diff) ≤ m * 2^d.exp
    have hpos : (0 : ℚ) < 2 ^ d.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
    have hpow2_pos : (0 : ℚ) < (2 : ℚ) ^ diff := pow_pos (by norm_num : (0 : ℚ) < 2) _
    -- Convert hdiv to ℚ: (m / 2^diff) * 2^diff ≤ m
    have hq : (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * ((2 : ℚ) ^ diff) ≤ d.mantissa := by
      have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
      rw [heq]
      -- Goal: (m/b : ℤ) * (b : ℕ) ≤ m in ℚ
      -- hdiv: (m/b) * b ≤ m in ℤ
      calc (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * ↑(2 ^ diff : ℕ)
          = ↑(d.mantissa / (2 ^ diff : ℕ) * (2 ^ diff : ℕ)) := by simp only [Int.cast_mul,
            Int.cast_natCast]
        _ ≤ ↑d.mantissa := Int.cast_le.mpr hdiv
    -- Rearrange: (m/b) * (c * b) = (m/b) * b * c and apply hq
    have hrearr : (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * (2 ^ d.exponent * (2 : ℚ) ^ diff)
                = (↑(d.mantissa / (2 ^ diff : ℕ))) * ((2 : ℚ) ^ diff) * 2 ^ d.exponent := by
      rw [mul_comm (2 ^ d.exponent) ((2 : ℚ) ^ diff), mul_assoc]
    rw [hrearr]
    exact mul_le_mul_of_nonneg_right hq (le_of_lt hpos)

/-- shiftUp produces a value ≥ the original -/
theorem toRat_shiftUp_ge (d : Dyadic) (newExp : Int) :
    d.toRat ≤ (shiftUp d newExp).toRat := by
  simp only [shiftUp]
  split_ifs with h hlowbits
  · exact le_refl _
  · -- Case: Lost bits, added 1
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow, hasLowBits] at hlowbits ⊢
    -- Use int_ediv_add_one_mul_ge: m ≤ (m/b + 1) * b when m % b ≠ 0
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hrem : d.mantissa % (2 ^ diff : ℕ) ≠ 0 := by
      simpa only [ne_eq, decide_eq_true_eq] using hlowbits
    have hceil : d.mantissa ≤ (d.mantissa / (2 ^ diff : ℕ) + 1) * (2 ^ diff : ℕ) :=
      int_ediv_add_one_mul_ge d.mantissa (2 ^ diff : ℕ) hpow_int_pos hrem
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    have hpos : (0 : ℚ) < 2 ^ d.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
    -- Convert hceil to ℚ: m ≤ (m/b + 1) * b
    have hq : (d.mantissa : ℚ) ≤ (↑(d.mantissa / (2 ^ diff : ℕ) + 1)) * ((2 : ℚ) ^ diff) := by
      have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
      rw [heq]
      calc (d.mantissa : ℚ) ≤ ↑((d.mantissa / (2 ^ diff : ℕ) + 1) * (2 ^ diff : ℕ)) :=
        Int.cast_le.mpr hceil
        _ = ↑(d.mantissa / (2 ^ diff : ℕ) + 1) * ↑(2 ^ diff : ℕ) := by simp only [Int.cast_mul,
          Int.cast_natCast]
    -- Rearrange and apply hq
    have hrearr : (↑(d.mantissa / (2 ^ diff : ℕ) + 1) : ℚ) * (2 ^ d.exponent * (2 : ℚ) ^ diff)
                = (↑(d.mantissa / (2 ^ diff : ℕ) + 1)) * ((2 : ℚ) ^ diff) * 2 ^ d.exponent := by
      rw [mul_comm (2 ^ d.exponent) ((2 : ℚ) ^ diff), mul_assoc]
    rw [hrearr]
    calc (d.mantissa : ℚ) * 2 ^ d.exponent
        ≤ (↑(d.mantissa / (2 ^ diff : ℕ) + 1) * ((2 : ℚ) ^ diff)) * 2 ^ d.exponent :=
            mul_le_mul_of_nonneg_right hq (le_of_lt hpos)
      _ = ↑(d.mantissa / (2 ^ diff : ℕ) + 1) * (2 : ℚ) ^ diff * 2 ^ d.exponent := by rfl
  · -- Case: No lost bits, exact (equality)
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow, hasLowBits] at hlowbits ⊢
    -- Use int_ediv_mul_eq: (m/b) * b = m when m % b = 0
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hrem : d.mantissa % (2 ^ diff : ℕ) = 0 := by
      simp only [ne_eq, decide_eq_true_eq, not_not] at hlowbits; exact hlowbits
    have hexact : (d.mantissa / (2 ^ diff : ℕ)) * (2 ^ diff : ℕ) = d.mantissa :=
      int_ediv_mul_eq d.mantissa (2 ^ diff : ℕ) hpow_int_pos hrem
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    -- Goal: m * 2^exp ≤ (m/b) * (2^exp * 2^diff)
    -- Since (m/b) * b = m, this is equality
    have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
    calc (d.mantissa : ℚ) * 2 ^ d.exponent
        = ↑((d.mantissa / (2 ^ diff : ℕ)) * (2 ^ diff : ℕ)) * 2 ^ d.exponent := by
            simp only [hexact]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * ↑(2 ^ diff : ℕ) * 2 ^ d.exponent := by
            simp only [Int.cast_mul, Int.cast_natCast]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * ((2 : ℚ) ^ diff * 2 ^ d.exponent) := by
            rw [← heq, mul_assoc]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * (2 ^ d.exponent * (2 : ℚ) ^ diff) := by
            rw [mul_comm ((2 : ℚ) ^ diff) (2 ^ d.exponent)]
      _ ≤ ↑(d.mantissa / (2 ^ diff : ℕ)) * (2 ^ d.exponent * (2 : ℚ) ^ diff) := le_refl _

/-! ### Comparison Helper Lemmas -/

/-- Helper: comparing integers reflects comparing rationals when scaled by positive factor -/
private theorem int_lt_iff_rat_mul_lt (a b : ℤ) (c : ℚ) (hc : 0 < c) :
    a < b ↔ (a : ℚ) * c < (b : ℚ) * c :=
    ⟨fun h ↦ mul_lt_mul_of_pos_right (Int.cast_lt.mpr h) hc, fun h ↦ Int.cast_lt.mp
      ((Rat.mul_lt_mul_right hc).mp h)⟩

private theorem int_eq_iff_rat_mul_eq (a b : ℤ) (c : ℚ) (hc : c ≠ 0) :
    a = b ↔ (a : ℚ) * c = (b : ℚ) * c := by
  constructor
  · intro h; rw [h]
  · intro h
    have hcancel := (mul_eq_mul_right_iff (c := c)).mp h
    cases hcancel with
    | inl heq => exact Int.cast_inj.mp heq
    | inr hzero => exact absurd hzero hc

private theorem int_gt_iff_rat_mul_gt (a b : ℤ) (c : ℚ) (hc : 0 < c) :
    a > b ↔ (a : ℚ) * c > (b : ℚ) * c := int_lt_iff_rat_mul_lt b a c hc

/-- Key lemma: shiftLeftInt relates to multiplication by 2^shift in ℚ -/
private theorem shiftLeftInt_toRat (m : ℤ) (n : ℕ) :
    (shiftLeftInt m n : ℚ) = (m : ℚ) * (2 : ℚ) ^ n := by
  simp only [shiftLeftInt, pow2Nat_eq_pow, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- Ord.compare on Int correctly reflects <, =, > -/
private theorem ord_compare_int_lt (a b : ℤ) : Ord.compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    by_contra! hge
    have hcases := lt_or_eq_of_le hge
    cases hcases with
    | inl hgt =>
      simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt hgt), ne_of_gt hgt,
        ↓reduceIte] at h
      exact absurd h (by decide)
    | inr heq =>
      simp only [Ord.compare, compareOfLessAndEq, heq, lt_irrefl, ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, h, ↓reduceIte]

private theorem ord_compare_int_eq (a b : ℤ) : Ord.compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    by_contra hne
    have hcases := lt_or_gt_of_ne hne
    cases hcases with
    | inl hlt =>
      simp only [Ord.compare, compareOfLessAndEq, hlt, ↓reduceIte] at h
      exact absurd h (by decide)
    | inr hgt =>
      simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt hgt), ne_of_gt hgt,
        ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, h, lt_irrefl, ↓reduceIte]

private theorem ord_compare_int_gt (a b : ℤ) : Ord.compare a b = .gt ↔ a > b := by
  constructor
  · intro h
    by_contra! hle
    have hcases := lt_or_eq_of_le hle
    cases hcases with
    | inl hlt =>
      simp only [Ord.compare, compareOfLessAndEq, hlt, ↓reduceIte] at h
      exact absurd h (by decide)
    | inr heq =>
      simp only [Ord.compare, compareOfLessAndEq, heq, lt_irrefl, ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt h), ne_of_gt h, ↓reduceIte]

/-- Ord.compare not gt means ≤ -/
private theorem ord_compare_ne_gt_iff (a b : ℤ) : (Ord.compare a b != .gt) = true ↔ a ≤ b := by
  rw [bne_iff_ne, ne_eq]
  constructor
  · intro h
    by_contra! hgt
    have := ord_compare_int_gt a b |>.mpr hgt
    exact h this
  · intro hle hgt
    have := ord_compare_int_gt a b |>.mp hgt
    exact not_lt.mpr hle this

/-! ### Comparison Theorems -/

/-- Helper: Convert aligned integer comparison to toRat comparison (case e₁ ≤ e₂) -/
private theorem aligned_lt_iff_toRat_lt_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa < shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat < d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  -- Key: 2^e₂ = 2^shift * 2^e₁
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₁.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  -- Rewrite RHS: m₂ * 2^e₂ = m₂ * (2^shift * 2^e₁) = (m₂ * 2^shift) * 2^e₁
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs]
  -- Now: m₁ < shiftLeftInt m₂ shift ↔ m₁ * 2^e₁ < (m₂ * 2^shift) * 2^e₁
  rw [int_lt_iff_rat_mul_lt _ _ _ hpos, shiftLeftInt_toRat]

private theorem aligned_eq_iff_toRat_eq_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa = shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat = d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hne : (2 : ℚ) ^ d₁.exponent ≠ 0 := zpow_ne_zero _ (two_ne_zero)
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs, int_eq_iff_rat_mul_eq _ _ _ hne, shiftLeftInt_toRat]

private theorem aligned_gt_iff_toRat_gt_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa > shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat > d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₁.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs, int_gt_iff_rat_mul_gt _ _ _ hpos, shiftLeftInt_toRat]

/-- Helper: Convert aligned integer comparison to toRat comparison (case e₁ > e₂) -/
private theorem aligned_lt_iff_toRat_lt_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat < d₂.mantissa ↔ d₁.toRat < d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₂.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  -- Rewrite LHS: m₁ * 2^e₁ = m₁ * (2^shift * 2^e₂) = (m₁ * 2^shift) * 2^e₂
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_lt_iff_rat_mul_lt _ _ _ hpos, shiftLeftInt_toRat]

private theorem aligned_eq_iff_toRat_eq_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat = d₂.mantissa ↔ d₁.toRat = d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hne : (2 : ℚ) ^ d₂.exponent ≠ 0 := zpow_ne_zero _ (two_ne_zero)
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_eq_iff_rat_mul_eq _ _ _ hne, shiftLeftInt_toRat]

private theorem aligned_gt_iff_toRat_gt_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat > d₂.mantissa ↔ d₁.toRat > d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₂.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_gt_iff_rat_mul_gt _ _ _ hpos, shiftLeftInt_toRat]

/-- le is correct with respect to toRat ordering -/
theorem le_iff_toRat_le (d₁ d₂ : Dyadic) :
    le d₁ d₂ = true ↔ d₁.toRat ≤ d₂.toRat := by
  unfold le compare
  split_ifs with h
  · -- Case: d₁.exponent ≤ d₂.exponent
    set shift := (d₂.exponent - d₁.exponent).toNat
    rw [ord_compare_ne_gt_iff]
    constructor
    · intro hle
      by_cases! hlt : d₁.mantissa < shiftLeftInt d₂.mantissa shift
      · exact le_of_lt ((aligned_lt_iff_toRat_lt_case1 d₁ d₂ h).mp hlt)
      · have heq_or_gt := lt_or_eq_of_le hlt
        cases heq_or_gt with
        | inl hgt =>
          exfalso; exact not_lt.mpr hle hgt
        | inr heq =>
          exact le_of_eq ((aligned_eq_iff_toRat_eq_case1 d₁ d₂ h).mp heq.symm)
    · intro hle
      by_contra! hgt
      have hgt' := (aligned_gt_iff_toRat_gt_case1 d₁ d₂ h).mp hgt
      exact not_lt.mpr hle hgt'
  · -- Case: d₁.exponent > d₂.exponent
    push Not at h
    set shift := (d₁.exponent - d₂.exponent).toNat
    rw [ord_compare_ne_gt_iff]
    constructor
    · intro hle
      by_cases! hlt : shiftLeftInt d₁.mantissa shift < d₂.mantissa
      · exact le_of_lt ((aligned_lt_iff_toRat_lt_case2 d₁ d₂ h).mp hlt)
      · have heq_or_gt := lt_or_eq_of_le hlt
        cases heq_or_gt with
        | inl hgt =>
          exfalso; exact not_lt.mpr hle hgt
        | inr heq =>
          exact le_of_eq ((aligned_eq_iff_toRat_eq_case2 d₁ d₂ h).mp heq.symm)
    · intro hle
      by_contra! hgt
      have hgt' := (aligned_gt_iff_toRat_gt_case2 d₁ d₂ h).mp hgt
      exact not_lt.mpr hle hgt'

/-- compare reflects toRat ordering: lt case -/
theorem compare_lt_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .lt ↔ d₁.toRat < d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_lt]; exact aligned_lt_iff_toRat_lt_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_lt]; exact aligned_lt_iff_toRat_lt_case2 d₁ d₂ h

/-- compare reflects toRat ordering: gt case -/
theorem compare_gt_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .gt ↔ d₁.toRat > d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_gt]; exact aligned_gt_iff_toRat_gt_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_gt]; exact aligned_gt_iff_toRat_gt_case2 d₁ d₂ h

/-- compare reflects toRat ordering: eq case -/
theorem compare_eq_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .eq ↔ d₁.toRat = d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_eq]; exact aligned_eq_iff_toRat_eq_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_eq]; exact aligned_eq_iff_toRat_eq_case2 d₁ d₂ h

/-! ### Min/Max Lemmas -/

/-- min produces value ≤ first argument -/
theorem min_toRat_le_left (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat ≤ d₁.toRat := by
  unfold min
  split_ifs with h
  · exact le_refl _
  · exact le_of_not_ge (fun hle => h (le_iff_toRat_le d₁ d₂ |>.mpr hle))

/-- min produces value ≤ second argument -/
theorem min_toRat_le_right (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat ≤ d₂.toRat := by
  unfold min
  split_ifs with h
  · exact le_iff_toRat_le d₁ d₂ |>.mp h
  · exact le_refl _

/-- first argument ≤ max -/
theorem le_max_toRat_left (d₁ d₂ : Dyadic) : d₁.toRat ≤ (max d₁ d₂).toRat := by
  unfold max
  split_ifs with h
  · exact le_iff_toRat_le d₁ d₂ |>.mp h
  · exact le_refl _

/-- second argument ≤ max -/
theorem le_max_toRat_right (d₁ d₂ : Dyadic) : d₂.toRat ≤ (max d₁ d₂).toRat := by
  unfold max
  split_ifs with h
  · exact le_refl _
  · exact le_of_not_ge (fun hle => h (le_iff_toRat_le d₁ d₂ |>.mpr hle))

/-- Dyadic.min commutes with toRat -/
theorem min_toRat (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat = Min.min d₁.toRat d₂.toRat := by
  unfold min
  split_ifs with h
  · -- h : le d₁ d₂
    have hle : d₁.toRat ≤ d₂.toRat := le_iff_toRat_le d₁ d₂ |>.mp h
    exact (min_eq_left hle).symm
  · -- ¬ le d₁ d₂, so d₂.toRat < d₁.toRat
    have hgt : d₂.toRat < d₁.toRat := by
      have := le_iff_toRat_le d₁ d₂
      exact lt_of_not_ge (fun hle => h (this.mpr hle))
    exact (min_eq_right (le_of_lt hgt)).symm

/-- Dyadic.max commutes with toRat -/
theorem max_toRat (d₁ d₂ : Dyadic) : (max d₁ d₂).toRat = Max.max d₁.toRat d₂.toRat := by
  unfold max
  split_ifs with h
  · -- h : le d₁ d₂
    have hle : d₁.toRat ≤ d₂.toRat := le_iff_toRat_le d₁ d₂ |>.mp h
    exact (max_eq_right hle).symm
  · -- ¬ le d₁ d₂, so d₂.toRat < d₁.toRat
    have hgt : d₂.toRat < d₁.toRat := by
      have := le_iff_toRat_le d₁ d₂
      exact lt_of_not_ge (fun hle => h (this.mpr hle))
    exact (max_eq_left (le_of_lt hgt)).symm

/-- min4 ≤ max4 -/
theorem min4_le_max4 (a b c d : Dyadic) : (min4 a b c d).toRat ≤ (max4 a b c d).toRat := by
  unfold min4 max4
  calc (min (min a b) (min c d)).toRat
      ≤ (min a b).toRat := min_toRat_le_left _ _
    _ ≤ a.toRat := min_toRat_le_left _ _
    _ ≤ (max a b).toRat := le_max_toRat_left _ _
    _ ≤ (max (max a b) (max c d)).toRat := le_max_toRat_left _ _

/-! ### Normalize Lemmas -/

/-- normalizeDown produces value ≤ original -/
theorem toRat_normalizeDown_le (d : Dyadic) (maxBits : Nat) :
    (d.normalizeDown maxBits).toRat ≤ d.toRat := by
  unfold normalizeDown normalize
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact le_refl _
  · exact toRat_shiftDown_le d _

/-- normalizeUp produces value ≥ original -/
theorem toRat_normalizeUp_ge (d : Dyadic) (maxBits : Nat) :
    d.toRat ≤ (d.normalizeUp maxBits).toRat := by
  unfold normalizeUp normalize
  simp only [↓reduceIte]
  split_ifs with h
  · exact le_refl _
  · exact toRat_shiftUp_ge d _

/-! ### Scale2 Lemmas -/

/-- scale2 multiplies by 2^n -/
theorem toRat_scale2 (d : Dyadic) (n : Int) :
    (d.scale2 n).toRat = d.toRat * (2 : ℚ) ^ n := by
  unfold scale2
  rw [toRat_eq, toRat_eq]
  simp only []
  rw [mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0)]

/-- scale2 preserves order -/
theorem toRat_scale2_le_scale2 (d₁ d₂ : Dyadic) (n : Int) (h : d₁.toRat ≤ d₂.toRat) :
    (d₁.scale2 n).toRat ≤ (d₂.scale2 n).toRat := by
  rw [toRat_scale2, toRat_scale2]
  exact mul_le_mul_of_nonneg_right h (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) n)

/-! ### Square Root Operations -/

/-- Integer square root of a natural number.
    Satisfies: `(intSqrtNat n)^2 ≤ n < (intSqrtNat n + 1)^2` -/
def intSqrtNat (n : Nat) : Nat := Nat.sqrt n

/-- Integer square root of a non-negative integer.
    Returns 0 for negative inputs. -/
def intSqrt (n : Int) : Int :=
  if n < 0 then 0 else Int.ofNat (intSqrtNat n.toNat)

/-- Key property of Nat.sqrt: `Nat.sqrt n ^ 2 ≤ n` -/
private theorem nat_sqrt_sq_le (n : Nat) : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n

/-- Key property of Nat.sqrt: `n < (Nat.sqrt n + 1) ^ 2` -/
private theorem nat_lt_succ_sqrt_sq (n : Nat) : n < (Nat.sqrt n + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  rw [sq]
  exact h

/-- intSqrt n ^ 2 ≤ n for n ≥ 0 -/
theorem intSqrt_sq_le {n : Int} (hn : 0 ≤ n) : (intSqrt n) ^ 2 ≤ n := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  have h := nat_sqrt_sq_le n.toNat
  calc ((Nat.sqrt n.toNat : ℤ) ^ 2 : ℤ)
      = ((Nat.sqrt n.toNat) ^ 2 : ℕ) := by norm_cast
    _ ≤ (n.toNat : ℤ) := Int.ofNat_le.mpr h
    _ = n := Int.toNat_of_nonneg hn

/-- n < (intSqrt n + 1) ^ 2 for n ≥ 0 -/
theorem int_lt_succ_sqrt_sq {n : Int} (hn : 0 ≤ n) : n < (intSqrt n + 1) ^ 2 := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  have h := nat_lt_succ_sqrt_sq n.toNat
  calc n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    _ < ((Nat.sqrt n.toNat + 1) ^ 2 : ℕ) := Int.ofNat_lt.mpr h
    _ = ((Nat.sqrt n.toNat : ℤ) + 1) ^ 2 := by norm_cast

/-- intSqrt is nonnegative for nonnegative inputs -/
theorem intSqrt_nonneg {n : Int} (hn : 0 ≤ n) : 0 ≤ intSqrt n := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  exact Int.natCast_nonneg _

/-- Compute sqrt(d) with a target exponent `prec`.
    Returns a Dyadic with exponent `prec` such that result ≤ sqrt(d).

    For d = m * 2^e, we compute:
    - shift = e - 2*prec (to align for sqrt)
    - m' = m * 2^shift (or m / 2^(-shift) if shift < 0)
    - result = floor(sqrt(m')) * 2^prec

    This ensures: result.toRat ≤ sqrt(d.toRat) -/
def sqrtDown (d : Dyadic) (prec : Int) : Dyadic :=
  if d.mantissa < 0 then zero
  else
    let shift := d.exponent - 2 * prec
    let m := if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)
    ⟨intSqrt m, prec⟩

/-- Compute sqrt(d) rounded up with target exponent `prec`.
    Returns a Dyadic with exponent `prec` such that result ≥ sqrt(d).

    Uses the same computation as sqrtDown, but if the result is not
    a perfect square, adds 1 to round up. -/
def sqrtUp (d : Dyadic) (prec : Int) : Dyadic :=
  if d.mantissa < 0 then zero
  else
    let shift := d.exponent - 2 * prec
    let m := if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)
    let s := intSqrt m
    -- If m is a perfect square of s, return s; otherwise s+1
    if s * s = m then ⟨s, prec⟩ else ⟨s + 1, prec⟩

/-! #### Sqrt Correctness Theorems -/

/-- Helper: For non-negative m and shift ≥ 0, the scaled mantissa is non-negative -/
private theorem sqrt_scaled_shift_nonneg {m : Int} {shift : Int}
    (hm : 0 ≤ m) (_hshift : 0 ≤ shift) :
    0 ≤ m * (pow2Nat shift.toNat : Int) := by
  apply mul_nonneg hm
  exact Int.natCast_nonneg _

/-- sqrtDown is non-negative for non-negative inputs -/
theorem sqrtDown_nonneg (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    0 ≤ (sqrtDown d prec).mantissa := by
  simp only [sqrtDown, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  exact intSqrt_nonneg hm_nonneg

/-- sqrtUp is non-negative for non-negative inputs -/
theorem sqrtUp_nonneg (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    0 ≤ (sqrtUp d prec).mantissa := by
  simp only [sqrtUp, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  set m := (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int))
  set s := intSqrt m
  by_cases hperfect : s * s = m
  · simp only [hperfect, ↓reduceIte]
    exact intSqrt_nonneg hm_nonneg
  · simp only [hperfect, ↓reduceIte]
    calc 0 ≤ s := intSqrt_nonneg hm_nonneg
      _ ≤ s + 1 := by omega

/-- sqrtDown.toRat ≤ sqrtUp.toRat for non-negative inputs -/
theorem sqrtDown_le_sqrtUp (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    (sqrtDown d prec).toRat ≤ (sqrtUp d prec).toRat := by
  simp only [sqrtDown, sqrtUp, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  set m := (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int))
  set s := intSqrt m
  by_cases hperfect : s * s = m
  · -- Perfect square: both return s
    simp only [hperfect, ↓reduceIte]
    exact le_refl _
  · -- Non-perfect: sqrtDown returns s, sqrtUp returns s+1
    simp only [hperfect, ↓reduceIte]
    rw [toRat_eq, toRat_eq]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _))
    simp only [Int.cast_add, Int.cast_one]
    exact le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ 1)

end Dyadic
end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Unified Expression AST

This file defines the unified AST for real expressions (`Expr`) and its
evaluation semantics. All numerical algorithms in LeanCert operate on this
single expression type.

## Main definitions

* `LeanCert.Core.Expr` - The expression AST supporting algebraic and transcendental operations
* `LeanCert.Core.Expr.eval` - Evaluation of expressions given a variable assignment

## Design notes

The expression type uses natural number indices for variables. This simplifies
the interval evaluation and automatic differentiation implementations.
-/

/-! ## Auxiliary definition for atanh

Since Mathlib doesn't provide `Real.atanh`, we define it here using the
standard formula: `atanh x = (1/2) * log((1+x)/(1-x))` for `|x| < 1`.
-/

public section

namespace LeanCert.Core

/-- The inverse hyperbolic tangent function.
    Defined as `atanh x = (1/2) * log((1+x)/(1-x))` for `|x| < 1`. -/
noncomputable def Real.atanh (x : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + x) / (1 - x))

/-- For |x| < 1, the argument (1+x)/(1-x) is positive. -/
theorem Real.atanh_arg_pos {x : ℝ} (hx : |x| < 1) : 0 < (1 + x) / (1 - x) := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := (abs_lt.mp hx).2
  have hnum : 0 < 1 + x := by linarith
  have hdenom : 0 < 1 - x := by linarith
  exact div_pos hnum hdenom

/-- atanh(0) = 0 -/
@[simp]
theorem Real.atanh_zero : Real.atanh 0 = 0 := by
  simp only [Real.atanh, add_zero, sub_zero, div_one, Real.log_one, mul_zero]

/-- atanh(-x) = -atanh(x) for |x| < 1 -/
theorem Real.atanh_neg {x : ℝ} (hx : |x| < 1) : Real.atanh (-x) = -Real.atanh x := by
  simp only [Real.atanh]
  have hlo : -1 < x := (abs_lt.mp hx).1
  have hhi : x < 1 := (abs_lt.mp hx).2
  have hpos1 : 0 < 1 + x := by linarith
  have hpos2 : 0 < 1 - x := by linarith
  have h1 : 1 + -x = 1 - x := by ring
  have h2 : 1 - -x = 1 + x := by ring
  rw [h1, h2]
  rw [Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
  rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
  ring

/-- atanh is strictly monotone on (-1, 1) -/
theorem Real.atanh_strictMonoOn : StrictMonoOn Real.atanh (Set.Ioo (-1) 1) := by
  intro x hx y hy hxy
  simp only [Real.atanh]
  have hx1 : 0 < 1 + x := by linarith [hx.1]
  have hx2 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 + y := by linarith [hy.1]
  have hy2 : 0 < 1 - y := by linarith [hy.2]
  have hargx : 0 < (1 + x) / (1 - x) := div_pos hx1 hx2
  have hargy : 0 < (1 + y) / (1 - y) := div_pos hy1 hy2
  gcongr 1
  rw [Real.log_lt_log_iff hargx hargy]
  -- Need (1+x)/(1-x) < (1+y)/(1-y) when x < y
  rw [div_lt_div_iff₀ hx2 hy2]
  ring_nf
  linarith

/-- atanh is monotone on (-1, 1): if x ≤ y then atanh x ≤ atanh y -/
theorem Real.atanh_mono {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) (hxy : x ≤ y) :
    Real.atanh x ≤ Real.atanh y := by
  rcases hxy.lt_or_eq with hlt | heq
  · have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hy).1, (abs_lt.mp hy).2⟩
    exact le_of_lt (Real.atanh_strictMonoOn hx' hy' hlt)
  · rw [heq]

/-- The error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt.
    Essential for statistical and financial modeling (normal distribution CDF).
    Uses interval integral notation (∫ t in 0..x) which handles negative x correctly. -/
@[expose]
noncomputable def Real.erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))

/-- The Gaussian function exp(-t²) is always positive. -/
private theorem exp_neg_sq_pos (t : ℝ) : 0 < Real.exp (-(t^2)) :=
  Real.exp_pos _

/-- The Gaussian function exp(-t²) is integrable on any compact interval. -/
private theorem intervalIntegrable_exp_neg_sq (a b : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(t^2))) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))

/-- Helper: The interval integral of a positive function over [0, x] is bounded by the
    half-Gaussian integral when x ≥ 0. -/
private theorem integral_exp_neg_sq_le_half_gaussian (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 := by
  have hgauss : ∫ t in Set.Ioi 0, Real.exp (-(1:ℝ) * t^2) = Real.sqrt (Real.pi / 1) / 2 :=
    integral_gaussian_Ioi 1
  simp only [div_one] at hgauss
  -- The interval integral equals the set integral on Ioc when x ≥ 0
  rw [intervalIntegral.integral_of_le hx]
  -- Need: ∫ t in Ioc 0 x, ... ≤ ∫ t in Ioi 0, ...
  -- We have Ioc 0 x ⊆ Ioi 0 for x ≥ 0
  have hint : MeasureTheory.Integrable (fun t => Real.exp (-(1:ℝ) * t^2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have hint_Ioi : MeasureTheory.Integrable (fun t => Real.exp (-(t^2)))
    (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have heq : (fun t : ℝ => Real.exp (-(t^2))) = (fun t => Real.exp (-(1:ℝ) * t^2)) := by
      funext t; ring_nf
    rw [heq]
    exact hint.restrict
  calc ∫ t in Set.Ioc 0 x, Real.exp (-(t^2))
      ≤ ∫ t in Set.Ioi 0, Real.exp (-(t^2)) := by
        apply MeasureTheory.setIntegral_mono_set hint_Ioi
        · -- Nonnegativity
          filter_upwards with t using le_of_lt (exp_neg_sq_pos t)
        · -- Set inclusion: Ioc 0 x ⊆ Ioi 0 (need to convert to ae form)
          exact Filter.Eventually.of_forall (fun t ht => Set.Ioc_subset_Ioi_self ht)
      _ = Real.sqrt Real.pi / 2 := by
        have heq : (fun t : ℝ => Real.exp (-(t^2))) = (fun t => Real.exp (-(1:ℝ) * t^2)) := by
          funext t; ring_nf
        rw [heq, hgauss]

/-- Helper: The interval integral of a positive function over [0, x] is nonneg when x ≥ 0. -/
private theorem integral_exp_neg_sq_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := by
  rw [intervalIntegral.integral_of_le hx]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
  intro t _
  exact le_of_lt (exp_neg_sq_pos t)

/-- The error function is bounded above by 1. -/
theorem Real.erf_le_one (x : ℝ) : Real.erf x ≤ 1 := by
  unfold Real.erf
  by_cases! hx : 0 ≤ x
  · -- Case x ≥ 0: Use that integral is bounded by √π/2
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 :=
      integral_exp_neg_sq_le_half_gaussian x hx
    calc (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))
        ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (by norm_num) (le_of_lt h1)
        _ = 1 := by field_simp
  · -- Case x < 0: Integral is negative (∫ 0..x = -∫ x..0), so erf(x) ≤ 0 ≤ 1
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have hxle : x ≤ 0 := le_of_lt hx
    -- For x < 0: ∫ 0..x = -∫ x..0, and ∫ x..0 ≥ 0 since we integrate a positive function
    have h2 : ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      apply neg_nonpos.mpr
      -- ∫ x..0 for x < 0 means integrating from x to 0, i.e., over [x, 0]
      rw [intervalIntegral.integral_of_le hxle]
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      intro t _
      exact le_of_lt (exp_neg_sq_pos t)
    calc (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2))
        ≤ (2 / Real.sqrt Real.pi) * 0 := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (by norm_num) (le_of_lt h1)
        _ = 0 := by ring
        _ ≤ 1 := by norm_num

/-- Helper: The integral ∫ x..0 exp(-t²) for x ≤ 0 is bounded by √π/2. -/
private theorem integral_exp_neg_sq_le_half_gaussian' (x : ℝ) (hx : x ≤ 0) :
    ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 := by
  -- Use substitution: the function is even, so ∫ x..0 = ∫ 0..-x
  have heq : ∀ t : ℝ, Real.exp (-(t^2)) = Real.exp (-((-t)^2)) := fun t => by ring_nf
  have hsub : ∫ t in x..(0:ℝ), Real.exp (-(t^2)) = ∫ t in (0:ℝ)..(-x), Real.exp (-(t^2)) := by
    calc ∫ t in x..(0:ℝ), Real.exp (-(t^2))
        = ∫ t in x..(0:ℝ), Real.exp (-((-t)^2)) := by simp only [neg_sq]
      _ = ∫ t in (-0:ℝ)..(-x), Real.exp (-(t^2)) := by
          rw [intervalIntegral.integral_comp_neg (fun t => Real.exp (-(t^2)))]
      _ = ∫ t in (0:ℝ)..(-x), Real.exp (-(t^2)) := by simp only [neg_zero]
  rw [hsub]
  exact integral_exp_neg_sq_le_half_gaussian (-x) (by linarith)

/-- The error function is bounded below by -1. -/
theorem Real.neg_one_le_erf (x : ℝ) : -1 ≤ Real.erf x := by
  unfold Real.erf
  by_cases! hx : 0 ≤ x
  · -- Case x ≥ 0: Integral is nonneg, so erf(x) ≥ 0 > -1
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 ≤ ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := integral_exp_neg_sq_nonneg x hx
    have h3 : 0 ≤ (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t^2)) := by
      apply mul_nonneg
      · exact div_nonneg (by norm_num) (le_of_lt h1)
      · exact h2
    linarith
  · -- Case x < 0: ∫ 0..x = -∫ x..0, and ∫ x..0 ≤ √π/2
    have h1 : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have hxle : x ≤ 0 := le_of_lt hx
    -- ∫ 0..x = -∫ x..0
    rw [intervalIntegral.integral_symm]
    have h2 : ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ Real.sqrt Real.pi / 2 :=
      integral_exp_neg_sq_le_half_gaussian' x hxle
    -- Need: -1 ≤ (2/√π) * (-∫ x..0 f)
    -- i.e., -1 ≤ -(2/√π) * ∫ x..0 f
    -- i.e., (2/√π) * ∫ x..0 f ≤ 1
    -- From h2: ∫ x..0 f ≤ √π/2, so (2/√π) * ∫ x..0 f ≤ (2/√π) * (√π/2) = 1
    have h3 : (2 / Real.sqrt Real.pi) * ∫ t in x..(0:ℝ), Real.exp (-(t^2)) ≤ 1 := by
      calc (2 / Real.sqrt Real.pi) * ∫ t in x..(0:ℝ), Real.exp (-(t^2))
          ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) := by
            apply mul_le_mul_of_nonneg_left h2
            exact div_nonneg (by norm_num) (le_of_lt h1)
          _ = 1 := by field_simp
    linarith

/-- The error function always lies in `[-1, 1]`. -/
theorem Real.erf_mem_Icc (x : ℝ) : Real.erf x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_erf x, Real.erf_le_one x⟩

/-- The normalized sinc function always lies in `[-1, 1]`. -/
theorem Real.sinc_mem_Icc (x : ℝ) : Real.sinc x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_sinc x, Real.sinc_le_one x⟩

/-- Named mathematical constants with known interval bounds.
    Adding a new constant (e.g., Catalan's) only requires extending this enum
    and its lookup tables — zero evaluator files need updating. -/
inductive MathConst where
  | pi
  | eulerMascheroni
  deriving Repr, DecidableEq, Inhabited

/-- The real value of a named mathematical constant. -/
@[expose]
noncomputable def MathConst.toReal : MathConst → ℝ
  | .pi => Real.pi
  | .eulerMascheroni => Real.eulerMascheroniConstant

/-- Float approximation for heuristic evaluation (unverified). -/
def MathConst.toFloat : MathConst → Float
  | .pi => 3.141592653589793
  | .eulerMascheroni => 0.5772156649015329

/-- Rational approximation for display/debugging (unverified). -/
def MathConst.toRatApprox : MathConst → ℚ
  | .pi => 157 / 50
  | .eulerMascheroni => 577 / 1000

/-- Unified AST for real-valued expressions. -/
inductive Expr where
  /-- Rational constant -/
  | const (q : ℚ)
  /-- Variable with de Bruijn-style index -/
  | var (idx : Nat)
  /-- Addition -/
  | add (e₁ e₂ : Expr)
  /-- Multiplication -/
  | mul (e₁ e₂ : Expr)
  /-- Negation -/
  | neg (e : Expr)
  /-- Multiplicative inverse (partial: undefined at 0) -/
  | inv (e : Expr)
  /-- Exponential function -/
  | exp (e : Expr)
  /-- Sine function -/
  | sin (e : Expr)
  /-- Cosine function -/
  | cos (e : Expr)
  /-- Natural logarithm (partial: undefined for x ≤ 0) -/
  | log (e : Expr)
  /-- Arctangent function -/
  | atan (e : Expr)
  /-- Inverse hyperbolic sine (arsinh) -/
  | arsinh (e : Expr)
  /-- Inverse hyperbolic tangent (partial: undefined for |x| ≥ 1) -/
  | atanh (e : Expr)
  /-- Sinc function: sinc(x) = sin(x)/x for x ≠ 0, sinc(0) = 1 -/
  | sinc (e : Expr)
  /-- Error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt -/
  | erf (e : Expr)
  /-- Hyperbolic sine: sinh(x) = (exp(x) - exp(-x)) / 2 -/
  | sinh (e : Expr)
  /-- Hyperbolic cosine: cosh(x) = (exp(x) + exp(-x)) / 2 -/
  | cosh (e : Expr)
  /-- Hyperbolic tangent: tanh(x) = sinh(x) / cosh(x) ∈ (-1, 1) -/
  | tanh (e : Expr)
  /-- Square root (partial: undefined for x < 0) -/
  | sqrt (e : Expr)
  /-- A named mathematical constant (π, γ, …) looked up from a table. -/
  | namedConst (c : MathConst)
  deriving Repr, DecidableEq, Inhabited

namespace Expr

/-- Subtraction as a derived operation -/
def sub (e₁ e₂ : Expr) : Expr := add e₁ (neg e₂)

/-- Division as a derived operation -/
def div (e₁ e₂ : Expr) : Expr := mul e₁ (inv e₂)

/-- Integer power (non-negative exponent) -/
def pow (e : Expr) : Nat → Expr
  | 0 => const 1
  | n + 1 => mul e (pow e n)

/-- Absolute value as a derived operation: |x| = sqrt(x²)
    This gives correct results for all real x (except at 0 for interval purposes) -/
def abs (e : Expr) : Expr := sqrt (mul e e)

/-- Evaluate an expression given a variable assignment ρ : Nat → ℝ -/
@[expose]
noncomputable def eval (ρ : Nat → ℝ) : Expr → ℝ
  | const q => (q : ℝ)
  | var idx => ρ idx
  | add e₁ e₂ => eval ρ e₁ + eval ρ e₂
  | mul e₁ e₂ => eval ρ e₁ * eval ρ e₂
  | neg e => -(eval ρ e)
  | inv e => (eval ρ e)⁻¹
  | exp e => Real.exp (eval ρ e)
  | sin e => Real.sin (eval ρ e)
  | cos e => Real.cos (eval ρ e)
  | log e => Real.log (eval ρ e)
  | atan e => Real.arctan (eval ρ e)
  | arsinh e => Real.arsinh (eval ρ e)
  | atanh e => Real.atanh (eval ρ e)
  | sinc e => Real.sinc (eval ρ e)
  | erf e => Real.erf (eval ρ e)
  | sinh e => Real.sinh (eval ρ e)
  | cosh e => Real.cosh (eval ρ e)
  | tanh e => Real.tanh (eval ρ e)
  | sqrt e => Real.sqrt (eval ρ e)
  | namedConst c => c.toReal

/-- Update variable assignment at a specific index -/
@[expose]
def updateVar (ρ : Nat → ℝ) (idx : Nat) (x : ℝ) : Nat → ℝ :=
  fun i => if i = idx then x else ρ i

/-- Notation for replacing one coordinate of a variable environment. -/
notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

@[simp]
theorem updateVar_same (ρ : Nat → ℝ) (idx : Nat) (x : ℝ) :
    updateVar ρ idx x idx = x := by simp [updateVar]

@[simp]
theorem updateVar_other (ρ : Nat → ℝ) (idx i : Nat) (x : ℝ) (h : i ≠ idx) :
    updateVar ρ idx x i = ρ i := by simp [updateVar, h]

theorem updateVar_self (ρ : Nat → ℝ) (idx : Nat) :
    updateVar ρ idx (ρ idx) = ρ := by
  funext i
  simp only [updateVar]
  split_ifs with h
  · rw [h]
  · rfl

/-- Evaluate `e` as a scalar function of variable `idx`, with all other
    variables fixed by `ρ`. This represents the map t ↦ eval ρ[idx ↦ t] e. -/
noncomputable abbrev evalAlong (e : Expr) (ρ : Nat → ℝ) (idx : Nat) : ℝ → ℝ :=
  fun t => eval (updateVar ρ idx t) e

/-- The set of free variable indices in an expression -/
def freeVars : Expr → Finset Nat
  | const _ => ∅
  | var idx => {idx}
  | add e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | mul e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | neg e => freeVars e
  | inv e => freeVars e
  | exp e => freeVars e
  | sin e => freeVars e
  | cos e => freeVars e
  | log e => freeVars e
  | atan e => freeVars e
  | arsinh e => freeVars e
  | atanh e => freeVars e
  | sinc e => freeVars e
  | erf e => freeVars e
  | sinh e => freeVars e
  | cosh e => freeVars e
  | tanh e => freeVars e
  | sqrt e => freeVars e
  | namedConst _ => ∅

/-- An expression is closed if it has no free variables -/
def isClosed (e : Expr) : Prop := freeVars e = ∅

-- Basic lemmas about eval

@[simp]
theorem eval_const (ρ : Nat → ℝ) (q : ℚ) : eval ρ (const q) = q := rfl

@[simp]
theorem eval_var (ρ : Nat → ℝ) (idx : Nat) : eval ρ (var idx) = ρ idx := rfl

@[simp]
theorem eval_add (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (add e₁ e₂) = eval ρ e₁ + eval ρ e₂ := rfl

@[simp]
theorem eval_mul (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (mul e₁ e₂) = eval ρ e₁ * eval ρ e₂ := rfl

@[simp]
theorem eval_neg (ρ : Nat → ℝ) (e : Expr) : eval ρ (neg e) = -(eval ρ e) := rfl

@[simp]
theorem eval_inv (ρ : Nat → ℝ) (e : Expr) : eval ρ (inv e) = (eval ρ e)⁻¹ := rfl

@[simp]
theorem eval_exp (ρ : Nat → ℝ) (e : Expr) : eval ρ (exp e) = Real.exp (eval ρ e) := rfl

@[simp]
theorem eval_sin (ρ : Nat → ℝ) (e : Expr) : eval ρ (sin e) = Real.sin (eval ρ e) := rfl

@[simp]
theorem eval_cos (ρ : Nat → ℝ) (e : Expr) : eval ρ (cos e) = Real.cos (eval ρ e) := rfl

@[simp]
theorem eval_log (ρ : Nat → ℝ) (e : Expr) : eval ρ (log e) = Real.log (eval ρ e) := rfl

@[simp]
theorem eval_atan (ρ : Nat → ℝ) (e : Expr) : eval ρ (atan e) = Real.arctan (eval ρ e) := rfl

@[simp]
theorem eval_arsinh (ρ : Nat → ℝ) (e : Expr) : eval ρ (arsinh e) = Real.arsinh (eval ρ e) := rfl

@[simp]
theorem eval_atanh (ρ : Nat → ℝ) (e : Expr) : eval ρ (atanh e) = Real.atanh (eval ρ e) := rfl

@[simp]
theorem eval_sinc (ρ : Nat → ℝ) (e : Expr) : eval ρ (sinc e) = Real.sinc (eval ρ e) := rfl

@[simp]
theorem eval_erf (ρ : Nat → ℝ) (e : Expr) : eval ρ (erf e) = Real.erf (eval ρ e) := rfl

@[simp]
theorem eval_sinh (ρ : Nat → ℝ) (e : Expr) : eval ρ (sinh e) = Real.sinh (eval ρ e) := rfl

@[simp]
theorem eval_cosh (ρ : Nat → ℝ) (e : Expr) : eval ρ (cosh e) = Real.cosh (eval ρ e) := rfl

@[simp]
theorem eval_tanh (ρ : Nat → ℝ) (e : Expr) : eval ρ (tanh e) = Real.tanh (eval ρ e) := rfl

@[simp]
theorem eval_sqrt (ρ : Nat → ℝ) (e : Expr) : eval ρ (sqrt e) = Real.sqrt (eval ρ e) := rfl

@[simp]
theorem eval_namedConst (ρ : Nat → ℝ) (c : MathConst) :
    eval ρ (namedConst c) = c.toReal := rfl

theorem eval_eulerMascheroni (ρ : Nat → ℝ) :
    eval ρ (namedConst .eulerMascheroni) = Real.eulerMascheroniConstant := rfl

@[simp]
theorem eval_sub (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (sub e₁ e₂) = eval ρ e₁ - eval ρ e₂ := by simp [sub, sub_eq_add_neg]

@[simp]
theorem eval_div (ρ : Nat → ℝ) (e₁ e₂ : Expr) :
    eval ρ (div e₁ e₂) = eval ρ e₁ / eval ρ e₂ := by simp [div, div_eq_mul_inv]

@[simp]
theorem eval_pow (ρ : Nat → ℝ) (e : Expr) (n : ℕ) :
    eval ρ (pow e n) = (eval ρ e) ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow, eval_mul, ih, pow_succ']

/-- Evaluation of abs for any argument: |x| = sqrt(x²) -/
theorem eval_abs (ρ : Nat → ℝ) (e : Expr) :
    eval ρ (abs e) = |eval ρ e| := by
  simp only [abs, eval_sqrt, eval_mul, ← sq, Real.sqrt_sq_eq_abs]

/-- Evaluation of sqrt(x * x) = |x| (unfolded form of `abs`). -/
theorem eval_sqrt_mul_self_eq_abs (ρ : Nat → ℝ) (e : Expr) :
    eval ρ (sqrt (mul e e)) = |eval ρ e| := eval_abs ρ e

/-- `√(x * x) = |x|` — LeanCert-namespaced alias of `Real.sqrt_mul_self_eq_abs`. -/
theorem sqrt_mul_self_eq_abs (x : ℝ) : Real.sqrt (x * x) = |x| :=
  Real.sqrt_mul_self_eq_abs x

/-- For positive x, sqrt(x²) = x -/
theorem eval_sqrt_sq_of_pos (ρ : Nat → ℝ) (e : Expr) (hpos : 0 < eval ρ e) :
    eval ρ (sqrt (mul e e)) = eval ρ e := by
  simp only [eval_sqrt, eval_mul, ← sq, Real.sqrt_sq (le_of_lt hpos)]

/-- Abs correctly computes absolute value for positive inputs -/
theorem eval_abs_of_pos (ρ : Nat → ℝ) (e : Expr) (hpos : 0 < eval ρ e) :
    eval ρ (abs e) = eval ρ e := by
  rw [eval_abs, abs_of_pos hpos]

/-- Abs correctly computes absolute value for negative inputs -/
theorem eval_abs_of_neg (ρ : Nat → ℝ) (e : Expr) (hneg : eval ρ e < 0) :
    eval ρ (abs e) = -(eval ρ e) := by
  rw [eval_abs, abs_of_neg hneg]

-- Lemmas about evalAlong

theorem evalAlong_eq (e : Expr) (ρ : Nat → ℝ) (idx : Nat) (t : ℝ) :
    evalAlong e ρ idx t = eval (ρ[idx ↦ t]) e := rfl

theorem evalAlong_at_ρ (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong e ρ idx (ρ idx) = eval ρ e := by
  simp only [evalAlong, updateVar_self]

/-- evalAlong for a constant is constant -/
theorem evalAlong_const' (ρ : Nat → ℝ) (idx : Nat) (q : ℚ) :
    evalAlong (const q) ρ idx = fun _ => (q : ℝ) := rfl

/-- evalAlong for the active variable is the identity -/
theorem evalAlong_var_active (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (var idx) ρ idx = id := by
  funext t
  simp only [evalAlong, eval_var, updateVar_same, id_eq]

/-- evalAlong for a passive variable is constant -/
theorem evalAlong_var_passive (ρ : Nat → ℝ) (idx i : Nat) (h : i ≠ idx) :
    evalAlong (var i) ρ idx = fun _ => ρ i := by
  funext t
  simp only [evalAlong, eval_var, updateVar_other _ _ _ _ h]

/-- evalAlong for addition -/
theorem evalAlong_add (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (add e₁ e₂) ρ idx = fun t => evalAlong e₁ ρ idx t + evalAlong e₂ ρ idx t := by
  funext t
  simp only [evalAlong, eval_add]

/-- evalAlong for addition (Pi form for compatibility with deriv_add) -/
theorem evalAlong_add_pi (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (add e₁ e₂) ρ idx = evalAlong e₁ ρ idx + evalAlong e₂ ρ idx := rfl

/-- evalAlong for multiplication -/
theorem evalAlong_mul (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (mul e₁ e₂) ρ idx = fun t => evalAlong e₁ ρ idx t * evalAlong e₂ ρ idx t := by
  funext t
  simp only [evalAlong, eval_mul]

/-- evalAlong for multiplication (Pi form for compatibility with deriv_mul) -/
theorem evalAlong_mul_pi (e₁ e₂ : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (mul e₁ e₂) ρ idx = evalAlong e₁ ρ idx * evalAlong e₂ ρ idx := rfl

/-- evalAlong for negation -/
theorem evalAlong_neg (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (neg e) ρ idx = fun t => -(evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_neg]

/-- evalAlong for negation (Pi form for compatibility with deriv.neg) -/
theorem evalAlong_neg_pi (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (neg e) ρ idx = -evalAlong e ρ idx := rfl

/-- evalAlong for sin -/
theorem evalAlong_sin (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (sin e) ρ idx = fun t => Real.sin (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_sin]

/-- evalAlong for cos -/
theorem evalAlong_cos (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (cos e) ρ idx = fun t => Real.cos (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_cos]

/-- evalAlong for exp -/
theorem evalAlong_exp (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (exp e) ρ idx = fun t => Real.exp (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_exp]

/-- evalAlong for inv -/
theorem evalAlong_inv (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (inv e) ρ idx = fun t => (evalAlong e ρ idx t)⁻¹ := by
  funext t
  simp only [evalAlong, eval_inv]

/-- evalAlong for log -/
theorem evalAlong_log (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (log e) ρ idx = fun t => Real.log (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_log]

/-- evalAlong for atan -/
theorem evalAlong_atan (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (atan e) ρ idx = fun t => Real.arctan (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_atan]

/-- evalAlong for arsinh -/
theorem evalAlong_arsinh (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (arsinh e) ρ idx = fun t => Real.arsinh (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_arsinh]

/-- evalAlong for atanh -/
theorem evalAlong_atanh (e : Expr) (ρ : Nat → ℝ) (idx : Nat) :
    evalAlong (atanh e) ρ idx = fun t => Real.atanh (evalAlong e ρ idx t) := by
  funext t
  simp only [evalAlong, eval_atanh]

/-! ## Single-variable expressions

For 1D optimization and root finding, we often work with expressions that only use variable 0.
These lemmas establish that such expressions can be evaluated equivalently with different
environment representations.
-/

/-- Check if an expression only uses variable 0 (computable) -/
def usesOnlyVar0 : Expr → Bool
  | const _ => true
  | var n => n == 0
  | add e₁ e₂ => e₁.usesOnlyVar0 && e₂.usesOnlyVar0
  | mul e₁ e₂ => e₁.usesOnlyVar0 && e₂.usesOnlyVar0
  | neg e => e.usesOnlyVar0
  | inv e => e.usesOnlyVar0
  | exp e => e.usesOnlyVar0
  | sin e => e.usesOnlyVar0
  | cos e => e.usesOnlyVar0
  | log e => e.usesOnlyVar0
  | atan e => e.usesOnlyVar0
  | arsinh e => e.usesOnlyVar0
  | atanh e => e.usesOnlyVar0
  | sinc e => e.usesOnlyVar0
  | erf e => e.usesOnlyVar0
  | sinh e => e.usesOnlyVar0
  | cosh e => e.usesOnlyVar0
  | tanh e => e.usesOnlyVar0
  | sqrt e => e.usesOnlyVar0
  | namedConst _ => true

/-- If two environments agree on variable 0, then a usesOnlyVar0 expression evaluates the same -/
theorem eval_usesOnlyVar0_eq (e : Expr) (he : e.usesOnlyVar0 = true)
    (ρ₁ ρ₂ : Nat → ℝ) (h0 : ρ₁ 0 = ρ₂ 0) :
    eval ρ₁ e = eval ρ₂ e := by
  induction e with
  | const q => rfl
  | var n =>
    simp only [usesOnlyVar0, beq_iff_eq] at he
    simp only [eval_var, he, h0]
  | add e₁ e₂ ih1 ih2 =>
    simp only [usesOnlyVar0, Bool.and_eq_true] at he
    simp only [eval_add, ih1 he.1, ih2 he.2]
  | mul e₁ e₂ ih1 ih2 =>
    simp only [usesOnlyVar0, Bool.and_eq_true] at he
    simp only [eval_mul, ih1 he.1, ih2 he.2]
  | neg e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_neg, ih he]
  | inv e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_inv, ih he]
  | exp e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_exp, ih he]
  | sin e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sin, ih he]
  | cos e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_cos, ih he]
  | log e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_log, ih he]
  | atan e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_atan, ih he]
  | arsinh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_arsinh, ih he]
  | atanh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_atanh, ih he]
  | sinc e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sinc, ih he]
  | erf e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_erf, ih he]
  | sinh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sinh, ih he]
  | cosh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_cosh, ih he]
  | tanh e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_tanh, ih he]
  | sqrt e ih =>
    simp only [usesOnlyVar0] at he
    simp only [eval_sqrt, ih he]
  | namedConst _ => rfl

/-- For single-variable expressions, `fun n => if n = 0 then x else 0` and `fun _ => x`
    give the same evaluation result. -/
theorem eval_1d_equiv (e : Expr) (he : e.usesOnlyVar0 = true) (x : ℝ) :
    eval (fun n => if n = 0 then x else 0) e = eval (fun _ => x) e := by
  apply eval_usesOnlyVar0_eq e he
  simp

/-- Alternative: evaluation with Box-style environment equals 1D evaluation -/
theorem eval_box1d_eq_eval1d (e : Expr) (he : e.usesOnlyVar0 = true) (x : ℝ) :
    eval (fun n => if n = 0 then x else 0) e = eval (fun _ => x) e :=
  eval_1d_equiv e he x

end Expr

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Abstract Interval Interface

This file defines the abstract notion of intervals as subsets of ℝ,
with semantic properties. This provides the mathematical foundation
that `IntervalReal` will implement computationally.

## Main definitions

* Lemmas about `Set.Icc` (closed intervals) relevant to interval arithmetic
* Convexity and integrability properties

## Design notes

We primarily use `Set.Icc a b` from Mathlib as our semantic interval type.
This file collects lemmas and abstractions useful for verified numerics.
-/

/-! ### Interval membership and operations -/

public section

namespace LeanCert.Core

/-- A real number is in the interval [a, b] -/
abbrev memIcc (x a b : ℝ) : Prop := a ≤ x ∧ x ≤ b

theorem mem_Icc_iff (x a b : ℝ) : memIcc x a b ↔ x ∈ Set.Icc a b := Iff.rfl

/-! ### Interval arithmetic semantics

These lemmas establish the semantic foundation for interval arithmetic:
if x ∈ [a, b] and y ∈ [c, d], then x ⊕ y ∈ [a ⊕ c, b ⊕ d] (for appropriate ⊕).
-/

/-- Addition preserves interval membership -/
theorem add_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x + y ∈ Set.Icc (a + c) (b + d) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Negation reverses interval bounds -/
theorem neg_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    -x ∈ Set.Icc (-b) (-a) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Subtraction on intervals -/
theorem sub_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x - y ∈ Set.Icc (a - d) (b - c) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-! ### Convexity -/

/-- Closed intervals are convex -/
theorem Icc_convex (a b : ℝ) : Convex ℝ (Set.Icc a b) := convex_Icc a b

/-! ### Compactness -/

/-- Nonempty closed bounded intervals are compact -/
theorem Icc_compact (a b : ℝ) : IsCompact (Set.Icc a b) := isCompact_Icc

/-! ### Continuous functions on intervals -/

/-- A continuous function on a compact interval attains its bounds -/
theorem continuous_Icc_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) :
    ∃ (lo hi : ℝ), (∀ x ∈ Set.Icc a b, lo ≤ f x ∧ f x ≤ hi) ∧
      (∃ x ∈ Set.Icc a b, f x = lo) ∧ (∃ x ∈ Set.Icc a b, f x = hi) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := hcpt.exists_isMinOn hne hf.continuousOn
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := hcpt.exists_isMaxOn hne hf.continuousOn
  exact ⟨f xmin, f xmax,
    fun x hx => ⟨hxmin hx, hxmax hx⟩,
    ⟨xmin, hxmin_mem, rfl⟩,
    ⟨xmax, hxmax_mem, rfl⟩⟩

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Rational Endpoint Intervals - Core Definitions

This file defines `IntervalRat`, a concrete interval type with rational endpoints
suitable for computation. We prove the Fundamental Theorem of Interval Arithmetic
(FTIA) for each operation.

## Main definitions

* `LeanCert.Core.IntervalRat` - Intervals with rational endpoints
* `LeanCert.Core.IntervalRat.toSet` - Semantic interpretation as a subset of ℝ
* Operations: `add`, `neg`, `sub`, `mul`, `inv`, `div`

## Main theorems

* `mem_add` - FTIA for addition
* `mem_neg` - FTIA for negation
* `mem_sub` - FTIA for subtraction
* `mem_mul` - FTIA for multiplication

## Design notes

All operations maintain the invariant `lo ≤ hi`. Domain restrictions for partial
operations (like `inv`) are encoded via separate types or explicit hypotheses.
-/

public section

namespace LeanCert.Core

/-- An interval with rational endpoints -/
structure IntervalRat where
  /-- Lower endpoint of the interval. -/
  lo : ℚ
  /-- Upper endpoint of the interval. -/
  hi : ℚ
  le : lo ≤ hi
  deriving Repr

@[expose, instance_reducible, instance]
def instDecidableEqIntervalRat : DecidableEq IntervalRat := fun a b =>
  if hlo : a.lo = b.lo then
    if hhi : a.hi = b.hi then
      isTrue (by cases a; cases b; cases hlo; cases hhi; rfl)
    else
      isFalse (by intro hab; exact hhi (congrArg IntervalRat.hi hab))
  else
    isFalse (by intro hab; exact hlo (congrArg IntervalRat.lo hab))

/-- Default interval [0, 0] for unsupported expression branches -/
instance : Inhabited IntervalRat where
  default := ⟨0, 0, le_refl 0⟩

namespace IntervalRat

/-- The set of reals contained in this interval -/
def toSet (I : IntervalRat) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in an interval -/
instance : Membership ℝ IntervalRat where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalRat) : x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) :=
  Iff.rfl

/-- Membership in IntervalRat is the same as membership in Set.Icc -/
theorem mem_iff_mem_Icc (x : ℝ) (I : IntervalRat) : x ∈ I ↔ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ) := by
  simp only [mem_def, Set.mem_Icc]

/-- Universal quantifier over IntervalRat equals universal over Set.Icc -/
theorem forall_mem_iff_forall_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∀ x ∈ I, P x) ↔ (∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro h x hx <;> apply h <;> simp only [mem_iff_mem_Icc] at hx ⊢ <;> exact hx

/-- Existence in IntervalRat equals existence in Set.Icc -/
theorem exists_mem_iff_exists_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∃ x ∈ I, P x) ↔ (∃ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro ⟨x, hx, hp⟩ <;> exact ⟨x, by simp only [mem_iff_mem_Icc] at hx ⊢; exact
    hx, hp⟩

/-- Create an interval from a single rational -/
@[expose]
def singleton (q : ℚ) : IntervalRat := ⟨q, q, le_refl q⟩

theorem mem_singleton (q : ℚ) : (q : ℝ) ∈ singleton q := by
  simp only [mem_def, singleton, le_refl, and_self]

/-- The width of an interval -/
def width (I : IntervalRat) : ℚ := I.hi - I.lo

theorem width_nonneg (I : IntervalRat) : 0 ≤ I.width := by
  simp only [width, sub_nonneg]
  exact I.le

/-- Midpoint of an interval -/
def midpoint (I : IntervalRat) : ℚ := (I.lo + I.hi) / 2

/-- The midpoint of an interval is contained in the interval -/
theorem midpoint_mem (I : IntervalRat) : (I.midpoint : ℝ) ∈ I := by
  simp only [mem_def, midpoint]
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  constructor
  · -- lo ≤ (lo + hi) / 2
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith
  · -- (lo + hi) / 2 ≤ hi
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith

/-! ### Interval addition -/

/-- Add two intervals -/
@[expose]
def add (I J : IntervalRat) : IntervalRat where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le := by linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Rat.cast_add]
  constructor <;> linarith

/-! ### Interval negation -/

/-- Negate an interval -/
@[expose]
def neg (I : IntervalRat) : IntervalRat where
  lo := -I.hi
  hi := -I.lo
  le := by linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval subtraction -/

/-- Subtract two intervals -/
@[expose]
def sub (I J : IntervalRat) : IntervalRat := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval multiplication -/

/-- Helper: minimum of four rationals -/
@[expose]
def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)

/-- Helper: maximum of four rationals -/
@[expose]
def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

theorem min4_le_all (a b c d : ℚ) :
    min4 a b c d ≤ a ∧ min4 a b c d ≤ b ∧ min4 a b c d ≤ c ∧ min4 a b c d ≤ d := by
  simp only [min4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem all_le_max4 (a b c d : ℚ) :
    a ≤ max4 a b c d ∧ b ≤ max4 a b c d ∧ c ≤ max4 a b c d ∧ d ≤ max4 a b c d := by
  simp only [max4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem le_min4_iff (x a b c d : ℚ) :
    x ≤ min4 a b c d ↔ x ≤ a ∧ x ≤ b ∧ x ≤ c ∧ x ≤ d := by
  simp only [min4, le_min_iff, and_assoc]

theorem max4_le_iff (x a b c d : ℚ) :
    max4 a b c d ≤ x ↔ a ≤ x ∧ b ≤ x ∧ c ≤ x ∧ d ≤ x := by
  simp only [max4, max_le_iff, and_assoc]

/-- Multiply two intervals -/
@[expose]
def mul (I J : IntervalRat) : IntervalRat where
  lo := min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  hi := max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  le := by
    simp only [min4, max4]
    exact le_trans (min_le_of_left_le (min_le_left _ _))
                   (le_max_of_le_left (le_max_left _ _))

/-- Fast interval multiplication using sign-based case splitting.
    Reduces from 4 multiplications + 12 comparisons to 2 multiplications
    in the common case (both intervals positive or both negative).
    Falls back to the full 4-way product for mixed-sign intervals. -/
def mulFast (I J : IntervalRat) : IntervalRat :=
  if hIlo : I.lo ≥ 0 then
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.lo, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.lo, I.lo * J.hi, by nlinarith [I.le, J.le]⟩
    else
      ⟨I.hi * J.lo, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
  else if hIhi : I.hi ≤ 0 then
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.hi, I.hi * J.lo, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.hi, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
    else
      ⟨I.lo * J.hi, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
  else
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.hi, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.lo, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
    else
      mul I J

/- We intentionally do not attach `mulFast` as a native replacement here.
   Native certificate checking should execute the same definition that the
   kernel proofs reason about. Keep `mulFast` available only as an internal
   candidate for future explicitly-audited runtime backends. -/

/-- Helper: for x ∈ [a₁, a₂], x*y lies between endpoint products.
    When y ≥ 0: a₁*y ≤ x*y ≤ a₂*y
    When y ≤ 0: a₂*y ≤ x*y ≤ a₁*y -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  by_cases! hy : 0 ≤ y
  · -- y ≥ 0: multiplication preserves order, so a₁*y ≤ x*y ≤ a₂*y
    have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- y < 0: multiplication reverses order, so a₂*y ≤ x*y ≤ a₁*y
    have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products.
    When x ≥ 0: x*b₁ ≤ x*y ≤ x*b₂
    When x ≤ 0: x*b₂ ≤ x*y ≤ x*b₁ -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases! hx : 0 ≤ x
  · -- x ≥ 0: multiplication preserves order, so x*b₁ ≤ x*y ≤ x*b₂
    have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- x < 0: multiplication reverses order, so x*b₂ ≤ x*y ≤ x*b₁
    have hx' := le_of_lt hx
    have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx'
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Lower bound: xy ≥ min of corner products -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  -- First, x*y ≥ min(a₁*y, a₂*y) from mul_mem_endpoints_left
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  -- Now we need: min of corners ≤ min(a₁*y, a₂*y)
  -- Case split on whether a₁*y ≤ a₂*y
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · -- min(a₁*y, a₂*y) = a₁*y
    rw [min_eq_left hcmp] at h1
    -- Need: min corners ≤ a₁*y
    -- a₁*y is between a₁*b₁ and a₁*b₂, so min(a₁*b₁, a₁*b₂) ≤ a₁*y
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · -- min(a₁*y, a₂*y) = a₂*y
    rw [min_eq_right (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₂ * b₁) (a₂ * b₂) := min_le_right _ _
      _ ≤ a₂ * y := h2
      _ ≤ x * y := h1

/-- Upper bound: xy ≤ max of corner products -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · rw [max_eq_left (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).2
    calc x * y
        ≤ a₁ * y := h1
      _ ≤ max (a₁ * b₁) (a₁ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_left _ _

/-- Key lemma: product lies in convex hull of corner products.
    For x ∈ [a₁, a₂] and y ∈ [b₁, b₂], we have
    min{a₁b₁, a₁b₂, a₂b₁, a₂b₂} ≤ xy ≤ max{a₁b₁, a₁b₂, a₂b₁, a₂b₂}

    This is a standard result from interval arithmetic: extrema of bilinear
    functions on rectangles occur at corners. -/
private theorem mul_mem_corners {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) :=
  ⟨mul_lower_bound ha hb, mul_upper_bound ha hb⟩

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  simp only [mem_def] at *
  simp only [mul, min4, max4, Rat.cast_mul, Rat.cast_min, Rat.cast_max]
  exact mul_mem_corners hx hy

/-- Helper: show a = min4 a b c d when a ≤ b, a ≤ c, a ≤ d -/
theorem eq_min4_of_le {a b c d : ℚ} (h1 : a ≤ b) (h2 : a ≤ c) (h3 : a ≤ d) :
    a = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨le_refl _, h1, h2, h3⟩)
      (min4_le_all _ _ _ _).1

theorem eq_min4_of_le2 {a b c d : ℚ} (h1 : b ≤ a) (h2 : b ≤ c) (h3 : b ≤ d) :
    b = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, le_refl _, h2, h3⟩)
      (min4_le_all _ _ _ _).2.1

theorem eq_min4_of_le3 {a b c d : ℚ} (h1 : c ≤ a) (h2 : c ≤ b) (h3 : c ≤ d) :
    c = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, h2, le_refl _, h3⟩)
      (min4_le_all _ _ _ _).2.2.1

theorem eq_min4_of_le4 {a b c d : ℚ} (h1 : d ≤ a) (h2 : d ≤ b) (h3 : d ≤ c) :
    d = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, h2, h3, le_refl _⟩)
      (min4_le_all _ _ _ _).2.2.2

theorem eq_max4_of_ge {a b c d : ℚ} (h1 : b ≤ a) (h2 : c ≤ a) (h3 : d ≤ a) :
    a = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).1 ((max4_le_iff _ _ _ _ _).mpr ⟨le_refl
      _, h1, h2, h3⟩)

theorem eq_max4_of_ge2 {a b c d : ℚ} (h1 : a ≤ b) (h2 : c ≤ b) (h3 : d ≤ b) :
    b = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.1 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      le_refl _, h2, h3⟩)

theorem eq_max4_of_ge3 {a b c d : ℚ} (h1 : a ≤ c) (h2 : b ≤ c) (h3 : d ≤ c) :
    c = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.2.1 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      h2, le_refl _, h3⟩)

theorem eq_max4_of_ge4 {a b c d : ℚ} (h1 : a ≤ d) (h2 : b ≤ d) (h3 : c ≤ d) :
    d = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.2.2 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      h2, h3, le_refl _⟩)

/-- mulFast endpoints match mul endpoints: lo -/
private theorem mulFast_lo (I J : IntervalRat) : (mulFast I J).lo = (mul I J).lo := by
  simp only [mulFast, mul]
  split
  · split
    · exact eq_min4_of_le (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · split
      · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_min4_of_le4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · split
      · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rfl

/-- mulFast endpoints match mul endpoints: hi -/
private theorem mulFast_hi (I J : IntervalRat) : (mulFast I J).hi = (mul I J).hi := by
  simp only [mulFast, mul]
  split
  · split
    · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · exact eq_max4_of_ge2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · split
      · exact eq_max4_of_ge3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · split
      · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rfl

/-- `mulFast` preserves the containment property of `mul`.
    This is retained as documentation and a future audited optimization hook;
    production certificate checking currently uses `mul` directly. -/
theorem mem_mulFast {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulFast I J := by
  simp only [mem_def]
  rw [mulFast_lo, mulFast_hi]
  exact mem_mul hx hy

/-! ### Interval containing zero check -/

/-- Check if an interval contains zero -/
@[expose]
def containsZero (I : IntervalRat) : Prop := I.lo ≤ 0 ∧ 0 ≤ I.hi

/-- Decidable containsZero -/
instance (I : IntervalRat) : Decidable (containsZero I) :=
  inferInstanceAs (Decidable (I.lo ≤ 0 ∧ 0 ≤ I.hi))

/-- An interval that is guaranteed not to contain zero -/
structure IntervalRatNonzero extends IntervalRat where
  nonzero : ¬containsZero toIntervalRat

/-! ### Interval inversion (for nonzero intervals) -/

/-- Invert an interval that doesn't contain zero -/
def invNonzero (I : IntervalRatNonzero) : IntervalRat :=
  if h : 0 < I.lo then
    -- Positive interval: [1/hi, 1/lo]
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo : (0 : ℚ) < I.lo := h
        have hhi : (0 : ℚ) < I.hi := lt_of_lt_of_le hlo I.le
        exact inv_anti₀ hlo I.le }
  else
    -- Negative interval: [1/hi, 1/lo] (both negative)
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo_le : I.lo ≤ 0 := le_of_not_gt h
        have hhi_neg : I.hi < 0 := by
          have hnz := I.nonzero
          simp only [containsZero, not_and, not_le] at hnz
          exact hnz hlo_le
        have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
        exact (inv_le_inv_of_neg hhi_neg hlo_neg).mpr I.le }

/-! ### FTIA for inversion -/

theorem mem_invNonzero {x : ℝ} {I : IntervalRatNonzero} (hx : x ∈ I.toIntervalRat) (_hxne : x ≠ 0) :
    x⁻¹ ∈ invNonzero I := by
  simp only [mem_def] at *
  simp only [invNonzero]
  split_ifs with h
  · -- Positive case: 0 < I.lo
    have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast h
    have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
    have hhi_pos : (0 : ℝ) < I.hi := lt_of_lt_of_le hlo_pos (by exact_mod_cast I.le)
    simp only [Rat.cast_inv]
    constructor
    · exact inv_anti₀ hx_pos hx.2
    · exact inv_anti₀ (by exact_mod_cast h) hx.1
  · -- Negative case
    have hlo_le : I.lo ≤ 0 := le_of_not_gt h
    have hhi_neg : I.hi < 0 := by
      have hnz := I.nonzero
      simp only [containsZero, not_and, not_le] at hnz
      exact hnz hlo_le
    have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
    have hx_neg : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi_neg)
    have hhi_neg_r : (I.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
    have hlo_neg_r : (I.lo : ℝ) < 0 := by exact_mod_cast hlo_neg
    simp only [Rat.cast_inv]
    constructor
    · exact (inv_le_inv_of_neg hhi_neg_r hx_neg).mpr hx.2
    · exact (inv_le_inv_of_neg hx_neg hlo_neg_r).mpr hx.1

/-! ### Scalar operations -/

/-- Scale an interval by a rational -/
@[expose]
def scale (q : ℚ) (I : IntervalRat) : IntervalRat :=
  if hq : 0 ≤ q then
    { lo := q * I.lo
      hi := q * I.hi
      le := mul_le_mul_of_nonneg_left I.le hq }
  else
    { lo := q * I.hi
      hi := q * I.lo
      le := mul_le_mul_of_nonpos_left I.le (le_of_lt (not_le.mp hq)) }

/-- FTIA for scaling -/
theorem mem_scale {x : ℝ} {I : IntervalRat} (q : ℚ) (hx : x ∈ I) :
    (q : ℝ) * x ∈ scale q I := by
  simp only [mem_def, scale] at *
  split_ifs with hq
  · simp only [Rat.cast_mul]
    constructor
    · exact mul_le_mul_of_nonneg_left hx.1 (Rat.cast_nonneg.mpr hq)
    · exact mul_le_mul_of_nonneg_left hx.2 (Rat.cast_nonneg.mpr hq)
  · simp only [Rat.cast_mul]
    have hq' : (q : ℝ) ≤ 0 := Rat.cast_nonpos.mpr (le_of_lt (not_le.mp hq))
    constructor
    · exact mul_le_mul_of_nonpos_left hx.2 hq'
    · exact mul_le_mul_of_nonpos_left hx.1 hq'

/-! ### Interval splitting -/

/-- Split an interval at its midpoint -/
def bisect (I : IntervalRat) : IntervalRat × IntervalRat :=
  let m := I.midpoint
  (⟨I.lo, m, by change I.lo ≤ (I.lo + I.hi) / 2; linarith [I.le]⟩,
   ⟨m, I.hi, by change (I.lo + I.hi) / 2 ≤ I.hi; linarith [I.le]⟩)

theorem mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : x ≤ I.midpoint) :
    x ∈ (bisect I).1 := by
  simp only [mem_def, bisect] at *
  exact ⟨hx.1, hm⟩

theorem mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : I.midpoint ≤ x) :
    x ∈ (bisect I).2 := by
  simp only [mem_def, bisect] at *
  exact ⟨hm, hx.2⟩

/-- Distance from midpoint to lo is half the width -/
theorem midpoint_sub_lo (I : IntervalRat) :
    (I.midpoint : ℝ) - I.lo = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Distance from hi to midpoint is half the width -/
theorem hi_sub_midpoint (I : IntervalRat) :
    (I.hi : ℝ) - I.midpoint = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Midpoint is at least lo -/
theorem midpoint_ge_lo (I : IntervalRat) : I.lo ≤ I.midpoint := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at most hi -/
theorem midpoint_le_hi (I : IntervalRat) : I.midpoint ≤ I.hi := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at least lo (real version) -/
theorem midpoint_ge_lo_real (I : IntervalRat) : (I.lo : ℝ) ≤ I.midpoint := by
  have := midpoint_ge_lo I
  exact_mod_cast this

/-- Midpoint is at most hi (real version) -/
theorem midpoint_le_hi_real (I : IntervalRat) : (I.midpoint : ℝ) ≤ I.hi := by
  have := midpoint_le_hi I
  exact_mod_cast this

/-- Left bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).1) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact hx.1
  · exact le_trans hx.2 (Rat.cast_le.mpr (midpoint_le_hi I))

/-- Right bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).2) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact le_trans (Rat.cast_le.mpr (midpoint_ge_lo I)) hx.1
  · exact hx.2

/-- Any point in an interval is in one of its bisected halves -/
theorem mem_bisect_or {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x ∈ (bisect I).1 ∨ x ∈ (bisect I).2 := by
  by_cases hm : x ≤ I.midpoint
  · left; exact mem_bisect_left hx hm
  · right; exact mem_bisect_right hx (le_of_lt (not_le.mp hm))

/-- The default interval [0,0] contains only 0 -/
theorem mem_default (x : ℝ) : x ∈ (default : IntervalRat) ↔ x = 0 := by
  simp only [mem_def, Inhabited.default, Rat.cast_zero]
  constructor
  · intro ⟨h1, h2⟩; linarith
  · intro h; subst h; exact ⟨le_refl _, le_refl _⟩

/-! ### Interval intersection -/

/-- Intersect two intervals. Returns none if they don't intersect. -/
@[expose]
def intersect (I J : IntervalRat) : Option IntervalRat :=
  let lo := max I.lo J.lo
  let hi := min I.hi J.hi
  if h : lo ≤ hi then
    some ⟨lo, hi, h⟩
  else
    none

/-- If intersection succeeds, the result contains any point in both intervals -/
theorem mem_intersect {x : ℝ} {I J : IntervalRat} (hI : x ∈ I) (hJ : x ∈ J) :
    ∃ K, intersect I J = some K ∧ x ∈ K := by
  simp only [mem_def] at hI hJ
  -- Work with the max/min at rational level
  have hle : max I.lo J.lo ≤ min I.hi J.hi := by
    have hmax_le : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ x := sup_le hI.1 hJ.1
    have hle_min : x ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_inf hI.2 hJ.2
    have hR : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_trans hmax_le hle_min
    -- Convert back: on ℚ, max = sup and min = inf
    calc max I.lo J.lo = I.lo ⊔ J.lo := rfl
      _ ≤ I.hi ⊓ J.hi := by exact_mod_cast hR
      _ = min I.hi J.hi := rfl
  simp only [intersect, hle, ↓reduceDIte]
  refine ⟨⟨max I.lo J.lo, min I.hi J.hi, hle⟩, rfl, ?_⟩
  simp only [mem_def]
  constructor
  · -- Show (max I.lo J.lo : ℝ) ≤ x
    have h1 : max I.lo J.lo ≤ I.lo ∨ max I.lo J.lo = I.lo ∨ max I.lo J.lo = J.lo := by
      simp only [max_def]; split_ifs <;> simp
    cases le_or_gt I.lo J.lo with
    | inl h => simp only [max_eq_right h]; exact hJ.1
    | inr h => simp only [max_eq_left (le_of_lt h)]; exact hI.1
  · -- Show x ≤ (min I.hi J.hi : ℝ)
    cases le_or_gt I.hi J.hi with
    | inl h => simp only [min_eq_left h]; exact hI.2
    | inr h => simp only [min_eq_right (le_of_lt h)]; exact hJ.2

/-- If intersection returns some K, then K ⊆ I -/
theorem intersect_subset_left {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ I.lo ∧ K.hi ≤ I.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_left, inf_le_left⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

/-- If intersection returns some K, then K ⊆ J -/
theorem intersect_subset_right {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ J.lo ∧ K.hi ≤ J.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_right, inf_le_right⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

end IntervalRat

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# Verified Argument Reduction for Logarithm

This file provides argument reduction for computing log(q) using the identity:
  log(q) = log(m) + k * log(2)
where m = q * 2^(-k) is in a "good" range [1/2, 2] for Taylor series convergence.

## Main definitions

* `reductionExponent` - Find k such that q * 2^(-k) is in [1/2, 2]
* `reduceMantissa` - The reduced mantissa m = q * 2^(-k)

## Main theorems

* `reconstruction_eq` - Algebraic identity: q = m * 2^k
* `reduced_bounds` - Bounds on m: 1 / 2 ≤ m ≤ 2 for q > 0

## Design notes

This reduction allows us to use the rapidly converging atanh-based series:
  log(m) = 2 * atanh((m-1)/(m+1))
For m ∈ [1/2, 2], we have (m-1)/(m+1) ∈ [-1/3, 1/3], where atanh converges very fast.
-/

/-! ### Argument Reduction -/

public section

namespace LeanCert.Core.LogReduction

/-- Find k such that q * 2^(-k) is approximately in [1/2, 2].
    Implementation: k = log2(num) - log2(den) approximately. -/
def reductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- The reduced mantissa m = q * 2^(-k). -/
def reduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1  -- Default for non-positive inputs
  else
    let k := reductionExponent q
    q * (2 : ℚ) ^ (-k)

/-- The main algebraic theorem: q = m * 2^k for positive q -/
theorem reconstruction_eq {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    q = m * (2 : ℚ) ^ k := by
  simp only [reductionExponent, reduceMantissa, not_le.mpr hq, ↓reduceIte]
  -- Goal: q = (q * 2^(-k)) * 2^k = q * (2^(-k) * 2^k) = q * 2^0 = q
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [neg_add_cancel, zpow_zero, mul_one]

/-- The reduced mantissa is bounded: 1/4 ≤ m ≤ 4 for q > 0.
    (We use slightly weaker bounds than [1/2, 2] for simpler proofs,
     but the series still converges rapidly.) -/
theorem reduced_bounds_weak {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 4 ≤ m ∧ m ≤ 4 := by
  simp only [reduceMantissa, reductionExponent, not_le.mpr hq, ↓reduceIte]
  set n := q.num.natAbs.log2 with hn_def
  set d := q.den.log2 with hd_def
  have hnum_pos : q.num > 0 := Rat.num_pos.mpr hq
  have hnum_ne : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hnum_pos)
  have hden_pos := q.den_pos
  have hden_ne : q.den ≠ 0 := ne_of_gt hden_pos
  have h_num_lo : (2 : ℕ) ^ n ≤ q.num.natAbs := Nat.log2_self_le hnum_ne
  have h_num_hi : q.num.natAbs < 2 ^ (n + 1) := (Nat.log2_lt hnum_ne).mp (Nat.lt_succ_self _)
  have h_den_lo : (2 : ℕ) ^ d ≤ q.den := Nat.log2_self_le hden_ne
  have h_den_hi : q.den < 2 ^ (d + 1) := (Nat.log2_lt hden_ne).mp (Nat.lt_succ_self _)
  have h2_ne : (2 : ℚ) ≠ 0 := by norm_num
  have hden_pos_q : (0 : ℚ) < q.den := by exact_mod_cast hden_pos
  have hnum_pos_q : (0 : ℚ) < q.num.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hnum_ne
  have hq_eq : q = q.num / q.den := (Rat.num_div_den q).symm
  have hnum_eq : (q.num : ℚ) = q.num.natAbs := by simp only [Nat.cast_natAbs, abs_of_pos hnum_pos]
  have hexp : (-(↑n - ↑d) : ℤ) = (d : ℤ) - (n : ℤ) := by ring
  rw [hexp]
  have hpow_diff : (2 : ℚ) ^ ((d : ℤ) - (n : ℤ)) = 2 ^ d / 2 ^ n := by
    rw [zpow_sub₀ h2_ne, zpow_natCast, zpow_natCast]
  rw [hpow_diff, hq_eq, hnum_eq]
  have h_num_lo_q : (2 : ℚ) ^ n ≤ q.num.natAbs := by exact_mod_cast h_num_lo
  have h_num_hi_q : (q.num.natAbs : ℚ) < 2 ^ (n + 1) := by exact_mod_cast h_num_hi
  have h_den_lo_q : (2 : ℚ) ^ d ≤ q.den := by exact_mod_cast h_den_lo
  have h_den_hi_q : (q.den : ℚ) < 2 ^ (d + 1) := by exact_mod_cast h_den_hi
  constructor
  · -- Lower bound: 1/4 ≤ m
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, one_div, le_div_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    have key : (q.den : ℚ) * 2 ^ n / 4 < q.num.natAbs * 2 ^ d := by
      have h1 : (q.den : ℚ) * 2 ^ n / 4 < 2 ^ (d + 1) * 2 ^ n / 4 := by
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 4)
        exact mul_lt_mul_of_pos_right h_den_hi_q (by positivity)
      have h2 : (2 : ℚ) ^ (d + 1) * 2 ^ n / 4 = 2 ^ d * 2 ^ n / 2 := by rw [pow_succ]; ring
      have h3 : (2 : ℚ) ^ d * 2 ^ n / 2 ≤ 2 ^ n * 2 ^ d := by
        rw [mul_comm (2 ^ d : ℚ) (2 ^ n)]; apply div_le_self (by positivity) (by norm_num)
      have h4 : (2 : ℚ) ^ n * 2 ^ d ≤ q.num.natAbs * 2 ^ d := by
        apply mul_le_mul_of_nonneg_right h_num_lo_q (by positivity)
      linarith
    linarith
  · -- Upper bound: m ≤ 4
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, div_le_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    have h1 : (q.num.natAbs : ℚ) * 2 ^ d < 2 ^ (n + 1) * 2 ^ d := by
      apply mul_lt_mul_of_pos_right h_num_hi_q (by positivity)
    have h2 : (2 : ℚ) ^ (n + 1) * 2 ^ d = 2 * (2 ^ n * 2 ^ d) := by rw [pow_succ]; ring
    have h3 : (2 : ℚ) * (2 ^ n * 2 ^ d) ≤ 4 * (2 ^ n * 2 ^ d) := by
      have hp : (0 : ℚ) ≤ 2 ^ n * 2 ^ d := by positivity
      linarith
    have h4 : (4 : ℚ) * (2 ^ n * 2 ^ d) ≤ 4 * (q.den * 2 ^ n) := by
      have : (2 : ℚ) ^ n * 2 ^ d ≤ q.den * 2 ^ n := by
        calc (2 : ℚ) ^ n * 2 ^ d = 2 ^ d * 2 ^ n := by ring
          _ ≤ q.den * 2 ^ n := by apply mul_le_mul_of_nonneg_right h_den_lo_q (by positivity)
      linarith
    calc (q.num.natAbs : ℚ) * 2 ^ d ≤ 2 ^ (n + 1) * 2 ^ d := le_of_lt h1
      _ = 2 * (2 ^ n * 2 ^ d) := h2
      _ ≤ 4 * (2 ^ n * 2 ^ d) := h3
      _ ≤ 4 * (q.den * 2 ^ n) := h4

/-- Tighter bounds: 1 / 2 ≤ m ≤ 2 for most q > 0 -/
theorem reduced_bounds {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 2 ≤ m ∧ m ≤ 2 := by
  simp only [reduceMantissa, reductionExponent, not_le.mpr hq, ↓reduceIte]
  set n := q.num.natAbs.log2 with hn_def
  set d := q.den.log2 with hd_def
  have hnum_pos : q.num > 0 := Rat.num_pos.mpr hq
  have hnum_ne : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hnum_pos)
  have hden_pos := q.den_pos
  have hden_ne : q.den ≠ 0 := ne_of_gt hden_pos
  have h_num_lo : (2 : ℕ) ^ n ≤ q.num.natAbs := Nat.log2_self_le hnum_ne
  have h_num_hi : q.num.natAbs < 2 ^ (n + 1) := (Nat.log2_lt hnum_ne).mp (Nat.lt_succ_self _)
  have h_den_lo : (2 : ℕ) ^ d ≤ q.den := Nat.log2_self_le hden_ne
  have h_den_hi : q.den < 2 ^ (d + 1) := (Nat.log2_lt hden_ne).mp (Nat.lt_succ_self _)
  have h2_ne : (2 : ℚ) ≠ 0 := by norm_num
  have hden_pos_q : (0 : ℚ) < q.den := by exact_mod_cast hden_pos
  have hnum_pos_q : (0 : ℚ) < q.num.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hnum_ne
  have hq_eq : q = q.num / q.den := (Rat.num_div_den q).symm
  have hnum_eq : (q.num : ℚ) = q.num.natAbs := by simp only [Nat.cast_natAbs, abs_of_pos hnum_pos]
  have hexp : (-(↑n - ↑d) : ℤ) = (d : ℤ) - (n : ℤ) := by ring
  rw [hexp]
  have hpow_diff : (2 : ℚ) ^ ((d : ℤ) - (n : ℤ)) = 2 ^ d / 2 ^ n := by
    rw [zpow_sub₀ h2_ne, zpow_natCast, zpow_natCast]
  rw [hpow_diff, hq_eq, hnum_eq]
  have h_num_lo_q : (2 : ℚ) ^ n ≤ q.num.natAbs := by exact_mod_cast h_num_lo
  have h_num_hi_q : (q.num.natAbs : ℚ) < 2 ^ (n + 1) := by exact_mod_cast h_num_hi
  have h_den_lo_q : (2 : ℚ) ^ d ≤ q.den := by exact_mod_cast h_den_lo
  have h_den_hi_q : (q.den : ℚ) < 2 ^ (d + 1) := by exact_mod_cast h_den_hi
  constructor
  · -- Lower bound: 1 / 2 ≤ m
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, one_div, le_div_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    -- Goal: (1/2) * (den * 2^n) ≤ natAbs * 2^d, i.e., den * 2^n / 2 ≤ natAbs * 2^d
    have key : (q.den : ℚ) * 2 ^ n / 2 < q.num.natAbs * 2 ^ d := by
      have h1 : (q.den : ℚ) * 2 ^ n / 2 < 2 ^ (d + 1) * 2 ^ n / 2 := by
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 2)
        exact mul_lt_mul_of_pos_right h_den_hi_q (by positivity)
      have h2 : (2 : ℚ) ^ (d + 1) * 2 ^ n / 2 = 2 ^ d * 2 ^ n := by rw [pow_succ]; ring
      have h3 : (2 : ℚ) ^ d * 2 ^ n = 2 ^ n * 2 ^ d := by ring
      have h4 : (2 : ℚ) ^ n * 2 ^ d ≤ q.num.natAbs * 2 ^ d := by
        apply mul_le_mul_of_nonneg_right h_num_lo_q (by positivity)
      linarith
    linarith
  · -- Upper bound: m ≤ 2
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, div_le_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    -- Goal: natAbs * 2^d ≤ 2 * (den * 2^n)
    have h1 : (q.num.natAbs : ℚ) * 2 ^ d < 2 ^ (n + 1) * 2 ^ d := by
      apply mul_lt_mul_of_pos_right h_num_hi_q (by positivity)
    have h2 : (2 : ℚ) ^ (n + 1) * 2 ^ d = 2 * (2 ^ n * 2 ^ d) := by rw [pow_succ]; ring
    have h3 : (2 : ℚ) * (2 ^ n * 2 ^ d) ≤ 2 * (q.den * 2 ^ n) := by
      have : (2 : ℚ) ^ n * 2 ^ d ≤ q.den * 2 ^ n := by
        calc (2 : ℚ) ^ n * 2 ^ d = 2 ^ d * 2 ^ n := by ring
          _ ≤ q.den * 2 ^ n := by apply mul_le_mul_of_nonneg_right h_den_lo_q (by positivity)
      linarith
    calc (q.num.natAbs : ℚ) * 2 ^ d ≤ 2 ^ (n + 1) * 2 ^ d := le_of_lt h1
      _ = 2 * (2 ^ n * 2 ^ d) := h2
      _ ≤ 2 * (q.den * 2 ^ n) := h3

/-- The reduced mantissa is positive for positive input -/
theorem reduced_pos {q : ℚ} (hq : 0 < q) : 0 < reduceMantissa q := by
  simp only [reduceMantissa, not_le.mpr hq, ↓reduceIte]
  apply mul_pos hq
  apply zpow_pos
  norm_num

/-! ### Connection to Real.log -/

/-- Key algebraic identity for Real.log: log(q) = log(m) + k * log(2) -/
theorem log_reduction {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    Real.log q = Real.log m + k * Real.log 2 := by
  intro k m  -- Introduce let-bound variables
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast reduced_pos hq
  have h_recon := reconstruction_eq hq
  have hq_eq : (q : ℝ) = (m : ℝ) * (2 : ℝ) ^ k := by
    conv_lhs => rw [h_recon]
    push_cast
    rfl
  rw [hq_eq]
  have h2_pos : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num : (0 : ℝ) < 2) k
  rw [Real.log_mul (ne_of_gt hm_pos) (ne_of_gt h2_pos), Real.log_zpow]

/-- The transformation y = (m-1)/(m+1) maps m ∈ [1/2, 2] to y ∈ [-1/3, 1/3] -/
theorem atanh_arg_bounds {m : ℚ} (hlo : 1 / 2 ≤ m) (hhi : m ≤ 2) :
    let y := (m - 1) / (m + 1)
    (-1)/3 ≤ y ∧ y ≤ 1/3 := by
  intro y  -- Introduce let-bound variable
  have hden_pos : 0 < m + 1 := by linarith
  have hden_nonneg : 0 ≤ m + 1 := le_of_lt hden_pos
  constructor
  · -- Lower bound: (m-1)/(m+1) ≥ -1/3 when m ≥ 1/2
    -- Cross multiply: -1/3 ≤ (m-1)/(m+1) ↔ -(m+1) ≤ 3(m-1) ↔ 2 ≤ 4m
    have h : (-1 : ℚ) / 3 * (m + 1) ≤ m - 1 := by linarith
    have key := div_le_div_of_nonneg_right h hden_nonneg
    simp only [mul_div_assoc, div_self (ne_of_gt hden_pos), mul_one] at key
    exact key
  · -- Upper bound: (m-1)/(m+1) ≤ 1/3 when m ≤ 2
    -- Cross multiply: (m-1)/(m+1) ≤ 1/3 ↔ 3(m-1) ≤ m+1 ↔ 2m ≤ 4
    have h : m - 1 ≤ (1 : ℚ) / 3 * (m + 1) := by linarith
    have key := div_le_div_of_nonneg_right h hden_nonneg
    simp only [mul_div_assoc, div_self (ne_of_gt hden_pos), mul_one] at key
    exact key

/-- log(m) = 2 * atanh((m-1)/(m+1)) for m > 0 with m ≠ 1 -/
theorem log_via_atanh {m : ℚ} (hm_pos : 0 < m) :
    Real.log m = 2 * Real.atanh ((m - 1) / (m + 1)) := by
  have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hsum_pos : (0 : ℝ) < m + 1 := by linarith
  have hdiff_ne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hsum_pos
  -- atanh(y) = (1/2) * log((1+y)/(1-y))
  -- Setting y = (m-1)/(m+1):
  -- 1 + y = 1 + (m-1)/(m+1) = ((m+1) + (m-1))/(m+1) = 2m/(m+1)
  -- 1 - y = 1 - (m-1)/(m+1) = ((m+1) - (m-1))/(m+1) = 2/(m+1)
  -- (1+y)/(1-y) = (2m/(m+1)) / (2/(m+1)) = m
  rw [Real.atanh]
  have h1 : 1 + ((m : ℝ) - 1) / (m + 1) = 2 * m / (m + 1) := by field_simp; ring
  have h2 : 1 - ((m : ℝ) - 1) / (m + 1) = 2 / (m + 1) := by field_simp; ring
  rw [h1, h2]
  have h3 : 2 * (m : ℝ) / (m + 1) / (2 / (m + 1)) = m := by field_simp
  rw [h3]
  ring

end LeanCert.Core.LogReduction

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Rational Endpoint Intervals - Transcendental Functions

This file provides noncomputable interval bounds for transcendental functions
using floor/ceiling to obtain rational endpoints.

## Main definitions

* `ofRealEndpoints` - Create rational interval from real bounds using floor/ceil
* `expInterval` - Interval bound for exponential
* `logInterval` - Interval bound for logarithm (positive intervals)
* `atanhIntervalComputed` - Interval bound for atanh (intervals in (-1, 1))
* `sqrtInterval` - Interval bound for square root

## Main theorems

* `mem_expInterval` - FTIA for exp
* `mem_logInterval` - FTIA for log
* `mem_atanhIntervalComputed` - FTIA for atanh
* `mem_sqrtInterval` - FTIA for sqrt

## Design notes

All definitions in this file are noncomputable as they use `Real.exp`, `Real.log`,
etc. For computable versions, see `IntervalRat.Taylor`.
-/

/-! ### Rational enclosure of real intervals -/

public section

namespace LeanCert.Core

namespace IntervalRat

/-- Coarse rational enclosure of a real interval using floor/ceil.
    Given a real interval [lo, hi], returns a rational interval [⌊lo⌋, ⌈hi⌉]
    that is guaranteed to contain all points in the original interval. -/
noncomputable def ofRealEndpoints (lo hi : ℝ) (hle : lo ≤ hi) : IntervalRat where
  lo := ⌊lo⌋
  hi := ⌈hi⌉
  le := by
    have h1 : (⌊lo⌋ : ℝ) ≤ lo := Int.floor_le lo
    have h2 : hi ≤ (⌈hi⌉ : ℝ) := Int.le_ceil hi
    have h3 : (⌊lo⌋ : ℝ) ≤ (⌈hi⌉ : ℝ) := le_trans h1 (le_trans hle h2)
    exact_mod_cast h3

/-- Any point in [lo, hi] is in the rational enclosure [⌊lo⌋, ⌈hi⌉] -/
theorem mem_ofRealEndpoints {x lo hi : ℝ} (hle : lo ≤ hi) (hx : lo ≤ x ∧ x ≤ hi) :
    x ∈ ofRealEndpoints lo hi hle := by
  simp only [mem_def, ofRealEndpoints]
  constructor
  · have h := Int.floor_le lo
    exact le_trans h hx.1
  · have h := Int.le_ceil hi
    exact le_trans hx.2 h

/-! ### Exponential interval -/

/-- Interval bound for exp on rational intervals.
    Since exp is strictly increasing, exp([a,b]) ⊆ [⌊exp(a)⌋, ⌈exp(b)⌉].
    This uses Real.exp and floor/ceil to get rational bounds. -/
@[expose]
noncomputable def expInterval (I : IntervalRat) : IntervalRat :=
  ofRealEndpoints (Real.exp I.lo) (Real.exp I.hi)
    (Real.exp_le_exp.mpr (by exact_mod_cast I.le))

/-- FTIA for exp: if x ∈ I, then exp(x) ∈ expInterval(I) -/
theorem mem_expInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.exp x ∈ expInterval I := by
  simp only [expInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-! ### Positive interval check -/

/-- Check if an interval is strictly positive (lo > 0) -/
@[expose]
def isPositive (I : IntervalRat) : Prop := 0 < I.lo

/-- Decidable isPositive -/
instance (I : IntervalRat) : Decidable (isPositive I) :=
  inferInstanceAs (Decidable (0 < I.lo))

/-- An interval that is guaranteed to be strictly positive -/
structure IntervalRatPos extends IntervalRat where
  lo_pos : 0 < toIntervalRat.lo

/-! ### Logarithm interval (for positive intervals) -/

/-- Interval bound for log on positive rational intervals.
    Since log is strictly increasing on (0, ∞), log([a,b]) ⊆ [⌊log(a)⌋, ⌈log(b)⌉] for a > 0.
    This uses Real.log and floor/ceil to get rational bounds. -/
noncomputable def logInterval (I : IntervalRatPos) : IntervalRat :=
  ofRealEndpoints (Real.log I.lo) (Real.log I.hi)
    (Real.log_le_log (by exact_mod_cast I.lo_pos) (by exact_mod_cast I.le))

/-- FTIA for log: if x ∈ I with lo > 0, then log(x) ∈ logInterval(I) -/
theorem mem_logInterval {x : ℝ} {I : IntervalRatPos} (hx : x ∈ I.toIntervalRat) :
    Real.log x ∈ logInterval I := by
  simp only [logInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast I.lo_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  constructor
  · exact Real.log_le_log hlo_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-! ### Atanh interval (for intervals in (-1, 1)) -/

/-- An interval strictly contained in (-1, 1), suitable for atanh -/
structure IntervalRatInUnitBall where
  /-- Lower endpoint of the interval. -/
  lo : ℚ
  /-- Upper endpoint of the interval. -/
  hi : ℚ
  le : lo ≤ hi
  lo_gt : -1 < lo
  hi_lt : hi < 1

/-- Convert to standard interval -/
def IntervalRatInUnitBall.toIntervalRat (I : IntervalRatInUnitBall) : IntervalRat :=
  ⟨I.lo, I.hi, I.le⟩

/-- Membership in the underlying interval -/
instance : Membership ℝ IntervalRatInUnitBall where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

theorem IntervalRatInUnitBall.mem_def {x : ℝ} {I : IntervalRatInUnitBall} :
    x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := Iff.rfl

/-- Interval bound for atanh on intervals strictly inside (-1, 1).
    Since atanh is strictly increasing on (-1, 1), atanh([a,b]) ⊆ [⌊atanh(a)⌋, ⌈atanh(b)⌉]. -/
noncomputable def atanhIntervalComputed (I : IntervalRatInUnitBall) : IntervalRat :=
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  ofRealEndpoints (Real.atanh I.lo) (Real.atanh I.hi)
    (Real.atanh_mono
      (by rw [abs_lt]; constructor <;> linarith)
      (by rw [abs_lt]; constructor <;> linarith)
      hle)

/-- FTIA for atanh: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhIntervalComputed(I) -/
theorem mem_atanhIntervalComputed {x : ℝ} {I : IntervalRatInUnitBall} (hx : x ∈ I) :
    Real.atanh x ∈ atanhIntervalComputed I := by
  simp only [atanhIntervalComputed]
  apply mem_ofRealEndpoints
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  rw [IntervalRatInUnitBall.mem_def] at hx
  have hx_lo : -1 < x := by linarith [hx.1]
  have hx_hi : x < 1 := by linarith [hx.2]
  have habs_lo : |(I.lo : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_hi : |(I.hi : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_x : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  constructor
  · exact Real.atanh_mono habs_lo habs_x hx.1
  · exact Real.atanh_mono habs_x habs_hi hx.2

/-! ### Square Root Interval -/

/-- Integer square root (floor of sqrt).
    Satisfies: `(intSqrtNat n)^2 ≤ n < (intSqrtNat n + 1)^2` -/
def intSqrtNat (n : Nat) : Nat := Nat.sqrt n

/-- Key property of Nat.sqrt: `Nat.sqrt n ^ 2 ≤ n` -/
private theorem nat_sqrt_sq_le (n : Nat) : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n

/-- Key property of Nat.sqrt: `n < (Nat.sqrt n + 1) ^ 2` -/
private theorem nat_lt_succ_sqrt_sq (n : Nat) : n < (Nat.sqrt n + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  rw [sq]
  exact h

/-- Rational lower bound for sqrt.
    For q ≥ 0 with q = num/den, we compute floor(sqrt(num * den)) / den.
    This gives: sqrtRatLower q ≤ sqrt(q).

    The idea: sqrt(num/den) = sqrt(num*den)/den when properly scaled. -/
def sqrtRatLower (q : ℚ) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    -- Compute floor(sqrt(num * den)) / den
    let s := intSqrtNat (num * den)
    (s : ℚ) / den

/-- Rational upper bound for sqrt.
    For q ≥ 0, we compute ceil(sqrt(num * den)) / den.
    This gives: sqrt(q) ≤ sqrtRatUpper q. -/
def sqrtRatUpper (q : ℚ) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    let prod := num * den
    let s := intSqrtNat prod
    -- If s^2 = prod, return s/den; else (s+1)/den
    if s * s = prod then (s : ℚ) / den
    else ((s + 1) : ℚ) / den

/-- Scaling exponent for precise sqrt bounds (2^scaleBits = scaling factor for denominator) -/
def sqrtScaleBits : Nat := 20  -- gives about 6 decimal digits precision

/-- Rational lower bound for sqrt with high precision.
    For q ≥ 0, we scale by 4^k, compute integer sqrt, and scale back by 2^k.
    This gives: sqrtRatLowerPrec q ≤ sqrt(q) with precision ~2^(-k). -/
def sqrtRatLowerPrec (q : ℚ) (scaleBits : Nat := sqrtScaleBits) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    -- Scale up: multiply num by 4^scaleBits = 2^(2*scaleBits)
    let scaledNum := num * (2 ^ (2 * scaleBits))
    -- Compute floor(sqrt(scaledNum * den))
    let s := intSqrtNat (scaledNum * den)
    -- Scale back: divide by den * 2^scaleBits
    (s : ℚ) / (den * 2 ^ scaleBits)

/-- Rational upper bound for sqrt with high precision.
    For q ≥ 0, we scale by 4^k, compute ceil of integer sqrt, and scale back by 2^k.
    This gives: sqrt(q) ≤ sqrtRatUpperPrec q with precision ~2^(-k). -/
def sqrtRatUpperPrec (q : ℚ) (scaleBits : Nat := sqrtScaleBits) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    let scaledNum := num * (2 ^ (2 * scaleBits))
    let prod := scaledNum * den
    let s := intSqrtNat prod
    -- If s^2 = prod (perfect square), use s; else use s+1 (ceiling)
    let result := if s * s = prod then s else s + 1
    (result : ℚ) / (den * 2 ^ scaleBits)

/-- Helper: For non-negative q, q.num = q.num.natAbs -/
private theorem rat_num_of_nonneg {q : ℚ} (hq : 0 ≤ q) : (q.num : ℤ) = q.num.natAbs := by
  exact (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)).symm

/-- Helper: For positive q, num.natAbs > 0 -/
private theorem rat_num_natAbs_pos {q : ℚ} (hq : 0 < q) : 0 < q.num.natAbs := by
  have h := Rat.num_pos.mpr hq
  exact Int.natAbs_pos.mpr (ne_of_gt h)

/-- Soundness of sqrtRatLower: sqrtRatLower q ≤ Real.sqrt q for q ≥ 0 -/
theorem sqrtRatLower_le_sqrt {q : ℚ} (hq : 0 ≤ q) : (sqrtRatLower q : ℝ) ≤ Real.sqrt q := by
  simp only [sqrtRatLower]
  by_cases! hq0 : q ≤ 0
  · -- q = 0
    have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · -- q > 0
    simp only [not_le.mpr hq0, ↓reduceIte]
    -- Key insight: sqrtRatLower returns s/den where s = floor(sqrt(num*den))
    -- We want to show s/den ≤ sqrt(q) = sqrt(num/den)
    -- This follows because s^2 ≤ num*den, so s ≤ sqrt(num*den), hence s/den ≤ sqrt(num*den)/den =
    -- sqrt(num/den)
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hsqrt_den_pos : 0 < Real.sqrt q.den := Real.sqrt_pos.mpr hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    -- s^2 ≤ num * den
    have hsq : (intSqrtNat (q.num.natAbs * q.den))^2 ≤ q.num.natAbs * q.den := nat_sqrt_sq_le _
    -- s ≤ sqrt(num * den)
    have hs_le : (intSqrtNat (q.num.natAbs * q.den) : ℝ) ≤ Real.sqrt (q.num.natAbs * q.den) := by
      have h1 : ((intSqrtNat (q.num.natAbs * q.den) : ℕ) : ℝ) ^ 2 ≤ (q.num.natAbs * q.den : ℕ) := by
        exact_mod_cast hsq
      have h2 := Real.sqrt_sq (Nat.cast_nonneg (intSqrtNat (q.num.natAbs * q.den)))
      calc (intSqrtNat (q.num.natAbs * q.den) : ℝ)
          = Real.sqrt ((intSqrtNat (q.num.natAbs * q.den) : ℝ) ^ 2) := h2.symm
        _ ≤ Real.sqrt ((q.num.natAbs * q.den : ℕ) : ℝ) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) := by rw [Nat.cast_mul]
    -- q = num/den and sqrt(q) = sqrt(num)/sqrt(den) = sqrt(num*den)/den (after scaling)
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
      have habs : (q.num : ℤ) = q.num.natAbs := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
      simp only [Int.natAbs_natCast]
    simp only [Rat.cast_div, Rat.cast_natCast]
    rw [hq_eq, Real.sqrt_div hnum_real_nn, div_le_div_iff₀ hden_pos hsqrt_den_pos]
    -- Goal: s * sqrt(den) ≤ sqrt(num) * den
    calc (intSqrtNat (q.num.natAbs * q.den) : ℝ) * Real.sqrt q.den
        ≤ Real.sqrt (q.num.natAbs * q.den) * Real.sqrt q.den := by
            apply mul_le_mul_of_nonneg_right hs_le (le_of_lt hsqrt_den_pos)
      _ = Real.sqrt (q.num.natAbs) * Real.sqrt q.den * Real.sqrt q.den := by
            rw [Real.sqrt_mul hnum_real_nn]
      _ = Real.sqrt (q.num.natAbs) * (Real.sqrt q.den * Real.sqrt q.den) := by ring
      _ = Real.sqrt (q.num.natAbs) * q.den := by rw [Real.mul_self_sqrt hden_nn]

/-- Soundness of sqrtRatUpper: Real.sqrt q ≤ sqrtRatUpper q for q ≥ 0 -/
theorem sqrt_le_sqrtRatUpper {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ (sqrtRatUpper q : ℝ) := by
  simp only [sqrtRatUpper]
  by_cases! hq0 : q ≤ 0
  · -- q = 0
    have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · -- q > 0
    simp only [not_le.mpr hq0, ↓reduceIte]
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have hsqrt_den_pos : 0 < Real.sqrt q.den := Real.sqrt_pos.mpr hden_pos
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
      have habs : (q.num : ℤ) = q.num.natAbs := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
      simp only [Int.natAbs_natCast]
    set prod := q.num.natAbs * q.den
    set s := intSqrtNat prod
    rw [hq_eq, Real.sqrt_div hnum_real_nn]
    by_cases hperfect : s * s = prod
    · -- Perfect square case: s^2 = num * den, so sqrt(num*den) = s
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast]
      rw [div_le_div_iff₀ hsqrt_den_pos hden_pos]
      -- sqrt(num*den) = s since s^2 = num*den
      have heq_sqrt : Real.sqrt ((q.num.natAbs : ℝ) * q.den) = s := by
        have h : (s : ℝ) ^ 2 = (q.num.natAbs : ℝ) * q.den := by
          calc (s : ℝ) ^ 2 = ((s * s : ℕ) : ℝ) := by push_cast; ring
            _ = (prod : ℝ) := by exact_mod_cast hperfect
            _ = (q.num.natAbs : ℝ) * q.den := by simp only [prod, Nat.cast_mul]
        rw [← h, Real.sqrt_sq (Nat.cast_nonneg s)]
      calc Real.sqrt q.num.natAbs * q.den
          = Real.sqrt q.num.natAbs * (Real.sqrt q.den * Real.sqrt q.den) := by
              rw [Real.mul_self_sqrt hden_nn]
        _ = (Real.sqrt q.num.natAbs * Real.sqrt q.den) * Real.sqrt q.den := by ring
        _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) * Real.sqrt q.den := by
              rw [Real.sqrt_mul hnum_real_nn]
        _ = (s : ℝ) * Real.sqrt q.den := by rw [heq_sqrt]
        _ ≤ (s : ℝ) * Real.sqrt q.den := le_refl _
    · -- Non-perfect square case: prod < (s+1)^2
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast]
      rw [div_le_div_iff₀ hsqrt_den_pos hden_pos]
      have hlt : prod < (s + 1) ^ 2 := nat_lt_succ_sqrt_sq prod
      have hsqrt_le : Real.sqrt ((q.num.natAbs : ℝ) * q.den) ≤ (s + 1 : ℕ) := by
        have h1 : (q.num.natAbs : ℝ) * q.den < ((s + 1) ^ 2 : ℕ) := by
          calc (q.num.natAbs : ℝ) * q.den = (prod : ℕ) := by simp only [prod, Nat.cast_mul]
            _ < ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt
        have h2 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
        have h3 : Real.sqrt ((q.num.natAbs : ℝ) * q.den) < Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) :=
          Real.sqrt_lt_sqrt (mul_nonneg hnum_real_nn hden_nn) h1
        have h4 : Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) = (s + 1 : ℕ) := by
          have : (((s + 1) ^ 2 : ℕ) : ℝ) = ((s + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
          rw [this, Real.sqrt_sq h2]
        exact le_of_lt (h3.trans_eq h4)
      have hgoal : Real.sqrt q.num.natAbs * q.den ≤ ((s + 1 : ℕ) : ℝ) * Real.sqrt q.den := by
        calc Real.sqrt q.num.natAbs * q.den
            = Real.sqrt q.num.natAbs * (Real.sqrt q.den * Real.sqrt q.den) := by
                rw [Real.mul_self_sqrt hden_nn]
          _ = (Real.sqrt q.num.natAbs * Real.sqrt q.den) * Real.sqrt q.den := by ring
          _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) * Real.sqrt q.den := by
                rw [Real.sqrt_mul hnum_real_nn]
          _ ≤ ((s + 1 : ℕ) : ℝ) * Real.sqrt q.den := by
              exact mul_le_mul_of_nonneg_right hsqrt_le (le_of_lt hsqrt_den_pos)
      convert! hgoal using 2
      push_cast
      ring

/-- Square root interval with conservative bounds.
    For a non-negative interval [lo, hi], sqrt is monotone so:
    sqrt([lo, hi]) ⊆ [0, max(hi, 1)]

    The lower bound is 0 (always sound for sqrt).
    The upper bound uses max(hi, 1) which satisfies sqrt(x) ≤ max(x, 1) for x ≥ 0. -/
def sqrtInterval (I : IntervalRat) : IntervalRat :=
  ⟨0, max I.hi 1, le_sup_of_le_right rfl⟩

/-- Improved square root interval with tight lower bounds.
    For a non-negative interval [lo, hi] with lo ≥ 0:
    - Lower bound: sqrtRatLower(lo)
    - Upper bound: sqrtRatUpper(hi)

    For intervals crossing zero, we use 0 as lower bound. -/
def sqrtIntervalTight (I : IntervalRat) : IntervalRat :=
  if h : 0 ≤ I.lo then
    ⟨sqrtRatLower I.lo, max (sqrtRatUpper I.hi) 1,
     by
       simp only [le_max_iff]
       left
       have hlo_le_hi : I.lo ≤ I.hi := I.le
       -- sqrtRatLower I.lo ≤ sqrtRatUpper I.hi
       have h1 : (sqrtRatLower I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLower_le_sqrt h
       have h2 : Real.sqrt I.hi ≤ (sqrtRatUpper I.hi : ℝ) := sqrt_le_sqrtRatUpper (le_trans h
         hlo_le_hi)
       have h3 : Real.sqrt I.lo ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt (by exact_mod_cast hlo_le_hi)
       have h4 : (sqrtRatLower I.lo : ℝ) ≤ (sqrtRatUpper I.hi : ℝ) := le_trans h1 (le_trans h3 h2)
       exact_mod_cast h4⟩
  else
    ⟨0, max (sqrtRatUpper I.hi) 1, le_sup_of_le_right rfl⟩

/-- Soundness of sqrtRatLowerPrec: sqrtRatLowerPrec q k ≤ Real.sqrt q for q ≥ 0 -/
theorem sqrtRatLowerPrec_le_sqrt {q : ℚ} (hq : 0 ≤ q) (k : Nat) :
    (sqrtRatLowerPrec q k : ℝ) ≤ Real.sqrt q := by
  simp only [sqrtRatLowerPrec]
  by_cases! hq0 : q ≤ 0
  · have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · simp only [not_le.mpr hq0, ↓reduceIte]
    -- Setup: let num = q.num.natAbs, den = q.den, scaledNum = num * 4^k
    -- We compute s = floor(sqrt(scaledNum * den)) and return s / (den * 2^k)
    -- Goal: s / (den * 2^k) ≤ sqrt(q) = sqrt(num/den)
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have h2k_pos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
    have h2k_nn : (0 : ℝ) ≤ 2 ^ k := le_of_lt h2k_pos
    have hden2k_pos : (0 : ℝ) < q.den * 2 ^ k := mul_pos hden_pos h2k_pos
    set num := q.num.natAbs
    set den := q.den
    set scaledNum := num * 2 ^ (2 * k)
    set prod := scaledNum * den
    set s := intSqrtNat prod
    -- s^2 ≤ prod, so s ≤ sqrt(prod)
    have hsq : s ^ 2 ≤ prod := nat_sqrt_sq_le prod
    have hs_le_sqrt : (s : ℝ) ≤ Real.sqrt prod := by
      have h1 : (s : ℝ) ^ 2 ≤ prod := by exact_mod_cast hsq
      have h2 := Real.sqrt_sq (Nat.cast_nonneg s)
      calc (s : ℝ) = Real.sqrt ((s : ℝ) ^ 2) := h2.symm
        _ ≤ Real.sqrt prod := Real.sqrt_le_sqrt h1
    -- sqrt(prod) = sqrt(num * 4^k * den) = sqrt(num * den) * 2^k
    have h4k_eq : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by ring
    have hsqrt_prod : Real.sqrt (prod : ℕ) = Real.sqrt (num * den) * 2 ^ k := by
      calc Real.sqrt (prod : ℕ) = Real.sqrt ((scaledNum * den : ℕ) : ℝ) := by simp only [prod]
        _ = Real.sqrt ((num * 2 ^ (2 * k) * den : ℕ) : ℝ) := by simp only [scaledNum]
        _ = Real.sqrt ((num : ℝ) * 2 ^ (2 * k) * den) := by push_cast; ring_nf
        _ = Real.sqrt ((num : ℝ) * den * (2 ^ k) ^ 2) := by rw [h4k_eq]; ring_nf
        _ = Real.sqrt ((num : ℝ) * den) * Real.sqrt ((2 ^ k) ^ 2) := by
            rw [Real.sqrt_mul (mul_nonneg hnum_real_nn hden_nn)]
        _ = Real.sqrt ((num : ℝ) * den) * 2 ^ k := by rw [Real.sqrt_sq h2k_nn]
    -- q = num/den, so sqrt(q) = sqrt(num)/sqrt(den) = sqrt(num*den)/den
    have hq_eq : (q : ℝ) = (num : ℝ) / den := by
      have habs : (q.num : ℤ) = num := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
    -- Final calculation
    simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    rw [hq_eq, Real.sqrt_div hnum_real_nn]
    have hsqrt_den_pos : 0 < Real.sqrt den := Real.sqrt_pos.mpr hden_pos
    -- Key helper: sqrt(num * den) / den = sqrt(num) / sqrt(den)
    have hsqrt_conv : Real.sqrt (num * den) / den = Real.sqrt num / Real.sqrt den := by
      have hden_sqrt_mul : Real.sqrt den * Real.sqrt den = den := Real.mul_self_sqrt hden_nn
      calc Real.sqrt (num * den) / den
          = Real.sqrt num * Real.sqrt den / den := by rw [Real.sqrt_mul hnum_real_nn]
        _ = Real.sqrt num * Real.sqrt den / (Real.sqrt den * Real.sqrt den) := by rw [hden_sqrt_mul]
        _ = Real.sqrt num * (Real.sqrt den / (Real.sqrt den * Real.sqrt den)) := by rw
          [mul_div_assoc]
        _ = Real.sqrt num * (Real.sqrt den / Real.sqrt den / Real.sqrt den) := by rw
          [div_mul_eq_div_div]
        _ = Real.sqrt num * (1 / Real.sqrt den) := by rw [div_self (ne_of_gt hsqrt_den_pos)]
        _ = Real.sqrt num / Real.sqrt den := by rw [mul_one_div]
    calc (s : ℝ) / (den * 2 ^ k)
        ≤ Real.sqrt prod / (den * 2 ^ k) :=
          div_le_div_of_nonneg_right hs_le_sqrt (le_of_lt hden2k_pos)
      _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by rw [hsqrt_prod]
      _ = Real.sqrt (num * den) / den := by rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
      _ = Real.sqrt num / Real.sqrt den := hsqrt_conv

/-- Soundness of sqrtRatUpperPrec: Real.sqrt q ≤ sqrtRatUpperPrec q k for q ≥ 0 -/
theorem sqrt_le_sqrtRatUpperPrec {q : ℚ} (hq : 0 ≤ q) (k : Nat) :
    Real.sqrt q ≤ (sqrtRatUpperPrec q k : ℝ) := by
  simp only [sqrtRatUpperPrec]
  by_cases! hq0 : q ≤ 0
  · have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · simp only [not_le.mpr hq0, ↓reduceIte]
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have h2k_pos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
    have h2k_nn : (0 : ℝ) ≤ 2 ^ k := le_of_lt h2k_pos
    have hden2k_pos : (0 : ℝ) < q.den * 2 ^ k := mul_pos hden_pos h2k_pos
    set num := q.num.natAbs
    set den := q.den
    set scaledNum := num * 2 ^ (2 * k)
    set prod := scaledNum * den
    set s := intSqrtNat prod
    -- sqrt(prod) ≤ result (either s or s+1)
    have h4k_eq : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by ring
    have hsqrt_prod : Real.sqrt (prod : ℕ) = Real.sqrt (num * den) * 2 ^ k := by
      calc Real.sqrt (prod : ℕ) = Real.sqrt ((scaledNum * den : ℕ) : ℝ) := by simp only [prod]
        _ = Real.sqrt ((num * 2 ^ (2 * k) * den : ℕ) : ℝ) := by simp only [scaledNum]
        _ = Real.sqrt ((num : ℝ) * 2 ^ (2 * k) * den) := by push_cast; ring_nf
        _ = Real.sqrt ((num : ℝ) * den * (2 ^ k) ^ 2) := by rw [h4k_eq]; ring_nf
        _ = Real.sqrt ((num : ℝ) * den) * Real.sqrt ((2 ^ k) ^ 2) := by
            rw [Real.sqrt_mul (mul_nonneg hnum_real_nn hden_nn)]
        _ = Real.sqrt ((num : ℝ) * den) * 2 ^ k := by rw [Real.sqrt_sq h2k_nn]
    have hq_eq : (q : ℝ) = (num : ℝ) / den := by
      have habs : (q.num : ℤ) = num := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
    have hsqrt_den_pos : 0 < Real.sqrt den := Real.sqrt_pos.mpr hden_pos
    -- Key helper: sqrt(num * den) / den = sqrt(num) / sqrt(den)
    have hsqrt_conv : Real.sqrt (num * den) / den = Real.sqrt num / Real.sqrt den := by
      have hden_sqrt_mul : Real.sqrt den * Real.sqrt den = den := Real.mul_self_sqrt hden_nn
      calc Real.sqrt (num * den) / den
          = Real.sqrt num * Real.sqrt den / den := by rw [Real.sqrt_mul hnum_real_nn]
        _ = Real.sqrt num * Real.sqrt den / (Real.sqrt den * Real.sqrt den) := by rw [hden_sqrt_mul]
        _ = Real.sqrt num * (Real.sqrt den / (Real.sqrt den * Real.sqrt den)) := by rw
          [mul_div_assoc]
        _ = Real.sqrt num * (Real.sqrt den / Real.sqrt den / Real.sqrt den) := by rw
          [div_mul_eq_div_div]
        _ = Real.sqrt num * (1 / Real.sqrt den) := by rw [div_self (ne_of_gt hsqrt_den_pos)]
        _ = Real.sqrt num / Real.sqrt den := by rw [mul_one_div]
    by_cases hperfect : s * s = prod
    · -- Perfect square: result = s, and sqrt(prod) = s
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
                 Rat.cast_pow, Rat.cast_ofNat]
      have hsqrt_eq_s : Real.sqrt (prod : ℕ) = s := by
        have h : (s : ℝ) ^ 2 = prod := by
          calc (s : ℝ) ^ 2 = ((s * s : ℕ) : ℝ) := by push_cast; ring
            _ = prod := by exact_mod_cast hperfect
        rw [← h, Real.sqrt_sq (Nat.cast_nonneg s)]
      rw [hq_eq, Real.sqrt_div hnum_real_nn]
      calc Real.sqrt num / Real.sqrt den
          = Real.sqrt (num * den) / den := hsqrt_conv.symm
        _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by
            rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
        _ = Real.sqrt prod / (den * 2 ^ k) := by rw [hsqrt_prod]
        _ ≤ (s : ℝ) / (den * 2 ^ k) := by rw [hsqrt_eq_s]
    · -- Non-perfect square: result = s + 1, and sqrt(prod) < s + 1
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
                 Rat.cast_pow, Rat.cast_ofNat]
      have hlt : prod < (s + 1) ^ 2 := nat_lt_succ_sqrt_sq prod
      have hsqrt_lt : Real.sqrt (prod : ℕ) < (s + 1 : ℕ) := by
        have h1 : (prod : ℝ) < ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt
        have h2 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
        have h3 : Real.sqrt (prod : ℕ) < Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) :=
          Real.sqrt_lt_sqrt (Nat.cast_nonneg _) h1
        have h4 : Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) = (s + 1 : ℕ) := by
          have : (((s + 1) ^ 2 : ℕ) : ℝ) = ((s + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
          rw [this, Real.sqrt_sq h2]
        exact h3.trans_eq h4
      rw [hq_eq, Real.sqrt_div hnum_real_nn]
      calc Real.sqrt num / Real.sqrt den
          = Real.sqrt (num * den) / den := hsqrt_conv.symm
        _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by
            rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
        _ = Real.sqrt prod / (den * 2 ^ k) := by rw [hsqrt_prod]
        _ ≤ (s + 1 : ℕ) / (den * 2 ^ k) :=
            div_le_div_of_nonneg_right (le_of_lt hsqrt_lt) (le_of_lt hden2k_pos)

/-- High-precision square root interval.
    For a non-negative interval [lo, hi] with lo ≥ 0:
    - Lower bound: sqrtRatLowerPrec(lo)
    - Upper bound: sqrtRatUpperPrec(hi)

    Uses scaling to achieve ~6 decimal digits of precision. -/
def sqrtIntervalTightPrec (I : IntervalRat) : IntervalRat :=
  if h : 0 ≤ I.lo then
    ⟨sqrtRatLowerPrec I.lo, max (sqrtRatUpperPrec I.hi) 1,
     by
       simp only [le_max_iff]
       left
       have hlo_le_hi : I.lo ≤ I.hi := I.le
       have h1 : (sqrtRatLowerPrec I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLowerPrec_le_sqrt h
         sqrtScaleBits
       have h2 : Real.sqrt I.hi ≤ (sqrtRatUpperPrec I.hi : ℝ) :=
         sqrt_le_sqrtRatUpperPrec (le_trans h hlo_le_hi) sqrtScaleBits
       have h3 : Real.sqrt I.lo ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt (by exact_mod_cast hlo_le_hi)
       have h4 : (sqrtRatLowerPrec I.lo : ℝ) ≤ (sqrtRatUpperPrec I.hi : ℝ) := le_trans h1
         (le_trans h3 h2)
       exact_mod_cast h4⟩
  else
    ⟨0, max (sqrtRatUpperPrec I.hi) 1, le_sup_of_le_right rfl⟩

/-- Membership theorem for sqrtIntervalTightPrec -/
theorem mem_sqrtIntervalTightPrec' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtIntervalTightPrec I := by
  simp only [sqrtIntervalTightPrec, mem_def]
  split_ifs with h
  · -- lo ≥ 0: use tight bounds
    constructor
    · calc (sqrtRatLowerPrec I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLowerPrec_le_sqrt h sqrtScaleBits
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
    · simp only [Rat.cast_max, Rat.cast_one]
      calc Real.sqrt x ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt hx.2
        _ ≤ (sqrtRatUpperPrec I.hi : ℝ) := sqrt_le_sqrtRatUpperPrec (le_trans h I.le) sqrtScaleBits
        _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_left _ _
  · -- lo < 0: use 0 as lower bound
    push Not at h
    simp only [Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    constructor
    · exact Real.sqrt_nonneg x
    · -- sqrt(x) ≤ max(sqrtRatUpperPrec I.hi, 1)
      by_cases! hhi_neg : I.hi < 0
      · -- If hi < 0, then x ≤ I.hi < 0, but sqrt(x) ≥ 0, so sqrt(x) ≤ 1 ≤ max(_, 1)
        have hx_neg : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi_neg)
        have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hx_neg)
        rw [hsqrt_zero]
        calc (0 : ℝ) ≤ 1 := by norm_num
          _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_right _ _
      · calc Real.sqrt x ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt hx.2
          _ ≤ (sqrtRatUpperPrec I.hi : ℝ) := sqrt_le_sqrtRatUpperPrec hhi_neg sqrtScaleBits
          _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_left _ _

/-- Helper: sqrt(x) ≤ max(x, 1) for x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  rcases le_or_gt x 1 with hle | hgt
  · -- x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
      _ ≤ max x 1 := le_max_right x 1
  · -- x > 1: sqrt(x) < x ≤ max(x, 1)
    have hx_pos : 0 < x := lt_trans zero_lt_one hgt
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_gt_one : 1 < Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    have hsqrt_lt : Real.sqrt x < x := by
      have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
      have h2 : Real.sqrt x * 1 < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_left hsqrt_gt_one hsqrt_pos
      simp only [mul_one] at h2
      linarith
    calc Real.sqrt x ≤ x := le_of_lt hsqrt_lt
      _ ≤ max x 1 := le_max_left x 1

/-- Soundness of sqrt interval: if x ∈ I and x ≥ 0, then sqrt(x) ∈ sqrtInterval I -/
theorem mem_sqrtInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hx_nn : 0 ≤ x) :
    Real.sqrt x ∈ sqrtInterval I := by
  simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
  constructor
  · exact Real.sqrt_nonneg x
  · calc Real.sqrt x ≤ max x 1 := sqrt_le_max_one hx_nn
      _ ≤ max (I.hi : ℝ) 1 := max_le_max_right 1 hx.2

/-- General soundness of sqrt interval: works for any x ∈ I (including negative).
    When x < 0, Real.sqrt x = 0, which is always in [0, max(hi, 1)]. -/
theorem mem_sqrtInterval' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtInterval I := by
  rcases le_or_gt 0 x with hnn | hneg
  · -- x ≥ 0: use the standard soundness
    exact mem_sqrtInterval hx hnn
  · -- x < 0: sqrt(x) = 0, and 0 ∈ [0, max(hi, 1)]
    simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
    rw [hsqrt_zero]
    constructor
    · exact le_refl 0
    · calc (0 : ℝ) ≤ 1 := by norm_num
        _ ≤ max (I.hi : ℝ) 1 := le_max_right _ _

/-- Helper: upper bound for tight sqrt interval is valid -/
private theorem sqrt_le_sqrtRatUpper_max {x : ℝ} {q : ℚ} (hx : 0 ≤ x) (hxq : x ≤ q) :
    Real.sqrt x ≤ max (sqrtRatUpper q : ℝ) 1 := by
  by_cases! hq0 : q ≤ 0
  · -- q ≤ 0 means x ≤ 0, combined with hx gives x = 0
    have hx0 : x = 0 := le_antisymm (le_trans hxq (by exact_mod_cast hq0)) hx
    rw [hx0, Real.sqrt_zero]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right (sqrtRatUpper q : ℝ) (1 : ℝ))
  · -- q > 0
    calc Real.sqrt x
        ≤ Real.sqrt q := Real.sqrt_le_sqrt hxq
      _ ≤ sqrtRatUpper q := sqrt_le_sqrtRatUpper (le_of_lt hq0)
      _ ≤ max (sqrtRatUpper q : ℝ) 1 := le_max_left (sqrtRatUpper q : ℝ) (1 : ℝ)

/-- Soundness of tight sqrt interval: if x ∈ I and x ≥ 0, then sqrt(x) ∈ sqrtIntervalTight I -/
theorem mem_sqrtIntervalTight {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hx_nn : 0 ≤ x) :
    Real.sqrt x ∈ sqrtIntervalTight I := by
  simp only [sqrtIntervalTight]
  split_ifs with hlo
  · -- Case: I.lo ≥ 0 (positive interval)
    simp only [mem_def, Rat.cast_max, Rat.cast_one]
    constructor
    · -- Lower bound: sqrtRatLower I.lo ≤ sqrt(x)
      have h1 : (sqrtRatLower I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLower_le_sqrt hlo
      have h2 : Real.sqrt (I.lo : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
      exact le_trans h1 h2
    · -- Upper bound: sqrt(x) ≤ max (sqrtRatUpper I.hi) 1
      exact sqrt_le_sqrtRatUpper_max hx_nn hx.2
  · -- Case: I.lo < 0 (interval crosses zero)
    simp only [mem_def, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    constructor
    · exact Real.sqrt_nonneg x
    · exact sqrt_le_sqrtRatUpper_max hx_nn hx.2

/-- General soundness of tight sqrt interval: works for any x ∈ I (including negative).
    When x < 0, Real.sqrt x = 0, which is always in the result interval. -/
theorem mem_sqrtIntervalTight' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtIntervalTight I := by
  rcases le_or_gt 0 x with hnn | hneg
  · exact mem_sqrtIntervalTight hx hnn
  · -- x < 0: sqrt(x) = 0
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
    simp only [sqrtIntervalTight]
    split_ifs with hlo
    · -- I.lo ≥ 0, but x ∈ I and x < 0, contradiction
      have h : (I.lo : ℝ) ≤ x := hx.1
      have hlo_real : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
      have hx_nn : 0 ≤ x := le_trans hlo_real h
      exact absurd hx_nn (not_le.mpr hneg)
    · -- I.lo < 0
      simp only [mem_def, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
      rw [hsqrt_zero]
      constructor
      · exact le_refl 0
      · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right (sqrtRatUpper I.hi : ℝ) (1 : ℝ))

end IntervalRat

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Expression Support Predicates

This file defines predicates indicating which expressions are supported by
different interval evaluation strategies.

## Main definitions

* `ExprSupportedCore` - Predicate for expressions in the computable subset
  (const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi)

* `ADSupported` - Predicate for the noncomputable AD subset
  (const, var, add, mul, neg, sin, cos, exp)

## Design notes

`ADSupported` is the differentiable fragment used by automatic
differentiation. It is contained in `ExprSupportedCore` via
`ADSupported.toCore`. Checked evaluators accept arbitrary expressions and
encode domain failure in their result type, so they need no syntactic support
predicate.

The core subset is kept computable so that tactics can use `native_decide`
for interval bound checking. The extended subset uses `Real.exp` with
floor/ceil bounds, which requires noncomputability.
-/

/-! ### Core supported expression subset (computable) -/

public section

namespace LeanCert.Core

open LeanCert.Core

/-- Predicate indicating an expression is in the computable core subset.
    Supports: const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi

    Note: log requires positive domain for correctness. The correctness theorem
    `evalIntervalCore_correct` has an additional hypothesis `evalDomainValid`
    that ensures log arguments evaluate to positive intervals. -/
inductive ExprSupportedCore : Expr → Prop where
  | const (q : ℚ) : ExprSupportedCore (Expr.const q)
  | var (idx : Nat) : ExprSupportedCore (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.neg e)
  | sin {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sin e)
  | cos {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cos e)
  | exp {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.exp e)
  | log {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.log e)
  | sqrt {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sqrt e)
  | sinh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sinh e)
  | cosh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cosh e)
  | tanh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.tanh e)
  | erf {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.erf e)
  | namedConst (c : MathConst) : ExprSupportedCore (Expr.namedConst c)

/-! ### Extended supported expression subset (with exp) -/

/-- Predicate indicating an expression is in the fully-verified subset for AD.
    Supports: const, var, add, mul, neg, sin, cos, exp
    Does NOT support:
    - sqrt (not differentiable at 0 - use ExprSupportedCore for interval evaluation only)
    - inv (requires nonzero interval checks)
    - log (requires positive interval checks)
    - atan/arsinh/atanh (derivative proofs incomplete in the total AD evaluator) -/
inductive ADSupported : Expr → Prop where
  | const (q : ℚ) : ADSupported (Expr.const q)
  | var (idx : Nat) : ADSupported (Expr.var idx)
  | add {e₁ e₂ : Expr} : ADSupported e₁ → ADSupported e₂ → ADSupported (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ADSupported e₁ → ADSupported e₂ → ADSupported (Expr.mul e₁ e₂)
  | neg {e : Expr} : ADSupported e → ADSupported (Expr.neg e)
  | sin {e : Expr} : ADSupported e → ADSupported (Expr.sin e)
  | cos {e : Expr} : ADSupported e → ADSupported (Expr.cos e)
  | exp {e : Expr} : ADSupported e → ADSupported (Expr.exp e)

/-- ADSupported expressions are also in ExprSupportedCore -/
theorem ADSupported.toCore {e : Expr} (h : ADSupported e) : ExprSupportedCore e := by
  induction h with
  | const q => exact ExprSupportedCore.const q
  | var idx => exact ExprSupportedCore.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedCore.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedCore.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedCore.neg ih
  | sin _ ih => exact ExprSupportedCore.sin ih
  | cos _ ih => exact ExprSupportedCore.cos ih
  | exp _ ih => exact ExprSupportedCore.exp ih

/-- Computable recognition of the differentiable `ADSupported` subset used
by Newton/AD backends. -/
def Expr.checkADSupported : Expr → Bool
  | .const _ | .var _ => true
  | .add e₁ e₂ | .mul e₁ e₂ => e₁.checkADSupported && e₂.checkADSupported
  | .neg e | .exp e | .sin e | .cos e => e.checkADSupported
  | _ => false

/-- The executable support check recognizes exactly the differentiable
`ADSupported` fragment used by the checked AD/monotonicity backend. -/
theorem Expr.checkADSupported_eq_true_iff (e : Expr) :
    e.checkADSupported = true ↔ ADSupported e := by
  induction e with
  | const q => simp [Expr.checkADSupported, ADSupported.const]
  | var i => simp [Expr.checkADSupported, ADSupported.var]
  | add e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.checkADSupported, Bool.and_eq_true, ih₁, ih₂]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact .add h₁ h₂
      · intro h
        cases h
        exact ⟨by assumption, by assumption⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.checkADSupported, Bool.and_eq_true, ih₁, ih₂]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact .mul h₁ h₂
      · intro h
        cases h
        exact ⟨by assumption, by assumption⟩
  | neg e ih | exp e ih | sin e ih | cos e ih =>
      simp only [Expr.checkADSupported, ih]
      constructor
      · intro h
        first | exact .neg h | exact .exp h | exact .sin h | exact .cos h
      · intro h
        cases h
        assumption
  | inv e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | log e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | atan e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | arsinh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | atanh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sinc e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | erf e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sinh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | cosh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | tanh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sqrt e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | namedConst c =>
      constructor
      · simp [Expr.checkADSupported]
      · intro h
        cases h

/-- Computable recognition of `ExprSupportedCore`. -/
def Expr.checkSupportedCore : Expr → Bool
  | .const _ | .var _ | .namedConst _ => true
  | .add e₁ e₂ | .mul e₁ e₂ => e₁.checkSupportedCore && e₂.checkSupportedCore
  | .neg e | .exp e | .sin e | .cos e | .log e | .sqrt e |
      .sinh e | .cosh e | .tanh e | .erf e => e.checkSupportedCore
  | _ => false

/-- A successful computable core-support check produces the corresponding
proof object required by the tight Rational evaluator theorem. -/
theorem Expr.checkSupportedCore_correct {e : Expr}
    (h : e.checkSupportedCore = true) : ExprSupportedCore e := by
  induction e with
  | const q => exact .const q
  | var idx => exact .var idx
  | add left right ihLeft ihRight =>
      simp only [Expr.checkSupportedCore, Bool.and_eq_true] at h
      exact .add (ihLeft h.1) (ihRight h.2)
  | mul left right ihLeft ihRight =>
      simp only [Expr.checkSupportedCore, Bool.and_eq_true] at h
      exact .mul (ihLeft h.1) (ihRight h.2)
  | neg e ih => exact .neg (ih h)
  | exp e ih => exact .exp (ih h)
  | sin e ih => exact .sin (ih h)
  | cos e ih => exact .cos (ih h)
  | log e ih => exact .log (ih h)
  | erf e ih => exact .erf (ih h)
  | sinh e ih => exact .sinh (ih h)
  | cosh e ih => exact .cosh (ih h)
  | tanh e ih => exact .tanh (ih h)
  | sqrt e ih => exact .sqrt (ih h)
  | namedConst c => exact .namedConst c
  | inv _ _ | atan _ _ | arsinh _ _ | atanh _ _ | sinc _ _ =>
      simp [Expr.checkSupportedCore] at h

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Generic Taylor Series Abstractions

This file provides generic Taylor series machinery for verified numerics.
We wrap Mathlib's Taylor expansion theorems in forms convenient for our
interval arithmetic framework.

## Phase Status

**This module is now Phase 3 complete.** The main Taylor remainder bound theorem
`taylor_remainder_bound` is fully proved with no `sorry` markers.

The theorem provides rigorous bounds on Taylor polynomial approximation errors
using Lagrange's form of the remainder.

## Main definitions

* `TaylorApprox` - A Taylor approximation with explicit remainder bounds
* Generic theorems for composing Taylor approximations

## Design notes

This file provides the abstract theory. Specific Taylor expansions for
`exp`, `sin`, `cos`, etc. are built using this machinery in conjunction
with Mathlib's calculus lemmas.
-/

/-! ### Taylor approximation structure -/

public section

namespace LeanCert.Core

/-- A Taylor approximation of a function on an interval.

Given a function `f`, center `c`, and radius `r`, this represents:
- A polynomial approximation `poly` of degree `n`
- A remainder bound `R` such that for all `x` with `|x - c| ≤ r`:
  `|f(x) - poly(x - c)| ≤ R`
-/
structure TaylorApprox where
  /-- Degree of the polynomial -/
  degree : ℕ
  /-- Polynomial coefficients (Taylor coefficients at center) -/
  coeffs : Fin (degree + 1) → ℚ
  /-- Remainder bound -/
  remainder : ℚ
  /-- The remainder is non-negative -/
  remainder_nonneg : 0 ≤ remainder

namespace TaylorApprox

/-- Evaluate the polynomial part at a point -/
noncomputable def evalPoly (ta : TaylorApprox) (x : ℝ) : ℝ :=
  ∑ i : Fin (ta.degree + 1), (ta.coeffs i : ℝ) * x ^ (i : ℕ)

end TaylorApprox

/-! ### Derivative bounds -/

/-- A bound on the n-th derivative of a function on an interval -/
structure DerivBound where
  /-- The derivative order -/
  order : ℕ
  /-- Upper bound on |f^(n)(x)| for x in the interval -/
  bound : ℚ
  /-- The bound is non-negative -/
  bound_nonneg : 0 ≤ bound

/-! ### Taylor remainder bounds -/

/-! ### Helper lemmas for iteratedDerivWithin conversion -/

/-- Unique differentiability at the left endpoint of a closed interval. -/
lemma uniqueDiffWithinAt_Icc_left {c x : ℝ} (hcx : c < x) :
    UniqueDiffWithinAt ℝ (Set.Icc c x) c := by
  apply uniqueDiffWithinAt_convex (convex_Icc c x)
  · rw [interior_Icc]; exact Set.nonempty_Ioo.mpr hcx
  · rw [closure_Icc]; exact Set.left_mem_Icc.mpr (le_of_lt hcx)

/-- Unique differentiability at the right endpoint of a closed interval. -/
lemma uniqueDiffWithinAt_Icc_right {c x : ℝ} (hcx : c < x) :
    UniqueDiffWithinAt ℝ (Set.Icc c x) x := by
  apply uniqueDiffWithinAt_convex (convex_Icc c x)
  · rw [interior_Icc]; exact Set.nonempty_Ioo.mpr hcx
  · rw [closure_Icc]; exact Set.right_mem_Icc.mpr (le_of_lt hcx)

/-- At the left endpoint of [c, x], derivWithin equals deriv for differentiable functions. -/
lemma derivWithin_Icc_left_eq_deriv {f : ℝ → ℝ} {c x : ℝ}
    (hcx : c < x) (hf : DifferentiableAt ℝ f c) :
    derivWithin f (Set.Icc c x) c = deriv f c := by
  have hderiv := hf.hasDerivAt
  have hderiv_within : HasDerivWithinAt f (deriv f c) (Set.Icc c x) c := hderiv.hasDerivWithinAt
  exact hderiv_within.derivWithin (uniqueDiffWithinAt_Icc_left hcx)

/-- At the right endpoint of [c, x], derivWithin equals deriv for differentiable functions. -/
lemma derivWithin_Icc_right_eq_deriv {f : ℝ → ℝ} {c x : ℝ}
    (hcx : c < x) (hf : DifferentiableAt ℝ f x) :
    derivWithin f (Set.Icc c x) x = deriv f x := by
  have hderiv := hf.hasDerivAt
  have hderiv_within : HasDerivWithinAt f (deriv f x) (Set.Icc c x) x := hderiv.hasDerivWithinAt
  exact hderiv_within.derivWithin (uniqueDiffWithinAt_Icc_right hcx)

/-- Helper lemma: `iteratedDerivWithin` on `Icc a b` equals `iteratedDeriv` at interior points.

This bridges Mathlib's `iteratedDerivWithin`-based Taylor theorems with global `iteratedDeriv`. -/
lemma iteratedDerivWithin_Icc_interior_eq {f : ℝ → ℝ} {a b : ℝ} {x : ℝ} {n : ℕ}
    (_hab : a < b) (hx : x ∈ Set.Ioo a b) :
    iteratedDerivWithin n f (Set.Icc a b) x = iteratedDeriv n f x := by
  open Set Filter Topology in
  have h_nhds : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv]
  congr 1
  have heq : (Set.Icc a b : Set ℝ) =ᶠ[𝓝 x] (Set.univ : Set ℝ) := by
    filter_upwards [h_nhds] with y hy
    exact propext ⟨fun _ => trivial, fun _ => hy⟩
  rw [iteratedFDerivWithin_congr_set heq n, iteratedFDerivWithin_univ]

/-- At the left endpoint of [c, x], iteratedDerivWithin equals iteratedDeriv for ContDiff functions.
-/
lemma iteratedDerivWithin_Icc_left_eq_iteratedDeriv {f : ℝ → ℝ} {c x : ℝ} {n : ℕ}
    (hcx : c < x) (hf : ContDiff ℝ n f) :
    iteratedDerivWithin n f (Set.Icc c x) c = iteratedDeriv n f c := by
  open Set in
  induction n generalizing f with
  | zero => simp only [iteratedDerivWithin_zero, iteratedDeriv_zero]
  | succ n ih =>
    have hf_n : ContDiff ℝ n f := hf.of_le (by simp : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ))
    rw [iteratedDerivWithin_succ', iteratedDeriv_succ']
    have h_ne_zero : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0 := by simp
    have h_eq_derivWithin : EqOn (derivWithin f (Icc c x)) (deriv f) (Icc c x) := by
      intro y hy
      rcases eq_or_ne y c with rfl | hne_c
      · exact derivWithin_Icc_left_eq_deriv hcx
            ((hf.differentiable h_ne_zero).differentiableAt)
      · rcases eq_or_ne y x with rfl | hne_x
        · exact derivWithin_Icc_right_eq_deriv hcx
              ((hf.differentiable h_ne_zero).differentiableAt)
        · apply derivWithin_of_mem_nhds
          apply Icc_mem_nhds
          · exact lt_of_le_of_ne hy.1 (Ne.symm hne_c)
          · exact lt_of_le_of_ne hy.2 hne_x
    have h_congr : EqOn (iteratedDerivWithin n (derivWithin f (Icc c x)) (Icc c x))
                        (iteratedDerivWithin n (deriv f) (Icc c x)) (Icc c x) :=
      iteratedDerivWithin_congr (n := n) h_eq_derivWithin
    have hc_mem : c ∈ Icc c x := left_mem_Icc.mpr (le_of_lt hcx)
    rw [h_congr hc_mem]
    have hdf : ContDiff ℝ n (deriv f) := by
      have h := hf.iterate_deriv' n 1
      simp only [Function.iterate_one] at h
      exact h
    exact ih hdf

/-- At the left endpoint of [c, x], iteratedDerivWithin equals iteratedDeriv for functions
    that are ContDiffOn on an open set containing c.

    This is useful for functions like log that are only smooth on (0, ∞). -/
lemma iteratedDerivWithin_Icc_left_eq_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {c x : ℝ} {n : ℕ} {U :
  Set ℝ}
    (hU_open : IsOpen U) (hcU : c ∈ U) (hcx : c < x) (hI_sub : Set.Icc c x ⊆ U)
    (hf : ContDiffOn ℝ n f U) :
    iteratedDerivWithin n f (Set.Icc c x) c = iteratedDeriv n f c := by
  open Set in
  induction n generalizing f with
  | zero => simp only [iteratedDerivWithin_zero, iteratedDeriv_zero]
  | succ n ih =>
    have hf_n : ContDiffOn ℝ n f U := hf.of_le (by simp : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ))
    rw [iteratedDerivWithin_succ', iteratedDeriv_succ']
    have h_ne_zero : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0 := by simp
    -- For each y in Icc c x, derivWithin f = deriv f
    have h_eq_derivWithin : EqOn (derivWithin f (Icc c x)) (deriv f) (Icc c x) := by
      intro y hy
      rcases eq_or_ne y c with rfl | hne_c
      · -- At c: use that f is differentiable at c (from ContDiffOn on open U)
        exact derivWithin_Icc_left_eq_deriv hcx
            ((hf.differentiableOn h_ne_zero).differentiableAt (hU_open.mem_nhds hcU))
      · rcases eq_or_ne y x with rfl | hne_x
        · -- At x: use right endpoint lemma
          exact derivWithin_Icc_right_eq_deriv hcx
              ((hf.differentiableOn h_ne_zero).differentiableAt (hU_open.mem_nhds (hI_sub hy)))
        · -- Interior: Icc is a neighborhood
          apply derivWithin_of_mem_nhds
          apply Icc_mem_nhds
          · exact lt_of_le_of_ne hy.1 (Ne.symm hne_c)
          · exact lt_of_le_of_ne hy.2 hne_x
    have h_congr : EqOn (iteratedDerivWithin n (derivWithin f (Icc c x)) (Icc c x))
                        (iteratedDerivWithin n (deriv f) (Icc c x)) (Icc c x) :=
      iteratedDerivWithin_congr (n := n) h_eq_derivWithin
    have hc_mem : c ∈ Icc c x := left_mem_Icc.mpr (le_of_lt hcx)
    rw [h_congr hc_mem]
    have hdf : ContDiffOn ℝ n (deriv f) U := hf.deriv_of_isOpen hU_open le_rfl
    exact ih hdf
/-- Taylor remainder bound for c < x case with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the same Lagrange remainder bound as the global ContDiff version. -/
theorem taylor_remainder_bound_on_c_lt_x {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hca : a ≤ c)
    (hf : ContDiffOn ℝ (m + 1) f U)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hcx : c < x) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  have hcx_le : c ≤ x := le_of_lt hcx
  have hcI : c ∈ Icc a b := ⟨hca, le_trans hcx_le hx.2⟩
  have hI_sub' : Icc c x ⊆ Icc a b := Icc_subset_Icc hca hx.2
  have hI_sub_U : Icc c x ⊆ U := fun y hy => hI_sub (hI_sub' hy)
  have hcU : c ∈ U := hI_sub hcI
  have hf_on : ContDiffOn ℝ (m + 1) f (Icc c x) := hf.mono hI_sub_U
  have hf_on_m : ContDiffOn ℝ m f (Icc c x) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by simp
    exact hf_on.of_le hm_le
  have hf_diff : DifferentiableOn ℝ (iteratedDerivWithin m f (Icc c x)) (Ioo c x) := by
    have huniq := uniqueDiffOn_Icc hcx
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hf_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hf_on_m' : ContDiffOn ℝ m f (uIcc c x) := by rwa [uIcc_of_le hcx_le]
  have hf_diff' : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc c x)) (uIoo c x) := by
    rwa [uIcc_of_le hcx_le, uIoo_of_lt hcx]
  obtain ⟨ξ, hξ_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := x) hcx.ne hf_on_m' hf_diff'
  have hξ_mem_Ioo : ξ ∈ Ioo c x := by rwa [uIoo_of_lt hcx] at hξ_mem
  rw [uIcc_of_le hcx_le] at hLagrange
  have hξ_ab : ξ ∈ Icc a b := hI_sub' (Ioo_subset_Icc_self hξ_mem_Ioo)
  have hderiv_ξ : iteratedDerivWithin (m + 1) f (Icc c x) ξ = iteratedDeriv (m + 1) f ξ :=
    iteratedDerivWithin_Icc_interior_eq hcx hξ_mem_Ioo
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i =
                 taylorWithinEval f m (Icc c x) c x := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hderiv_c : iteratedDerivWithin i f (Icc c x) c = iteratedDeriv i f c := by
      have hi_lt : i < m + 1 := mem_range.mp hi
      have hi_le : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
        have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
        exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
      exact iteratedDerivWithin_Icc_left_eq_iteratedDeriv_of_isOpen hU_open hcU hcx hI_sub_U
        (hf.of_le hi_le)
    rw [hderiv_c]
    simp only [smul_eq_mul]
    ring
  rw [hsum_eq, hLagrange, hderiv_ξ]
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  have hxc_pos : 0 < x - c := sub_pos.mpr hcx
  rw [abs_pow, abs_of_pos hxc_pos]
  have hbound := hM ξ hξ_ab
  have h_pow_fact_pos : 0 < (x - c) ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · exact pow_pos hxc_pos _
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * (x - c) ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by ring

/-- Helper: translation invariance of iteratedDeriv for ContDiffOn on open sets. -/
private lemma iteratedDeriv_translate_of_contDiffOn {f : ℝ → ℝ} {k : ℝ} {n : ℕ} {U : Set ℝ}
    (hU_open : IsOpen U) (t : ℝ) (ht : t + k ∈ U)
    (hf : ContDiffOn ℝ n f U) :
    iteratedDeriv n (fun y => f (y + k)) t = iteratedDeriv n f (t + k) := by
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    -- Since t + k ∈ U and U is open, there's a neighborhood of t where y + k ∈ U for all y
    have h_nhds_mem : ∀ᶠ y in nhds t, y + k ∈ U := by
      have hcont : Continuous (fun y => y + k) := continuous_id.add continuous_const
      have hU_nhds : U ∈ nhds (t + k) := hU_open.mem_nhds ht
      exact hcont.continuousAt.preimage_mem_nhds hU_nhds
    -- Derivative equality in a neighborhood of t
    have h_deriv_eq_near : ∀ᶠ y in nhds t, deriv (fun z => f (z + k)) y = deriv f (y + k) := by
      filter_upwards [h_nhds_mem] with y hy_mem
      have hf' : ContDiffOn ℝ 1 f U := hf.of_le (by norm_cast; omega)
      have hdiff : DifferentiableAt ℝ f (y + k) :=
        (hf'.differentiableOn one_ne_zero).differentiableAt (hU_open.mem_nhds hy_mem)
      have hlin : DifferentiableAt ℝ (fun z => z + k) y :=
        differentiableAt_id.add (differentiableAt_const _)
      have h := deriv_comp y hdiff hlin
      simp only [deriv_add_const, deriv_id'', mul_one] at h
      exact h
    have h_iter_eq : iteratedDeriv n (deriv fun z => f (z + k)) t =
                     iteratedDeriv n (fun y => deriv f (y + k)) t :=
      Filter.EventuallyEq.iteratedDeriv_eq n h_deriv_eq_near
    rw [h_iter_eq]
    have hdf : ContDiffOn ℝ n (deriv f) U := hf.deriv_of_isOpen hU_open le_rfl
    exact ih hdf

/-- Key lemma for reflection: derivatives of g(t) = f(2c - t) when f is smooth on an open set.

This is a local version of `iteratedDeriv_reflect` that works with ContDiffOn on an open set
rather than global ContDiff. -/
lemma iteratedDeriv_reflect_of_contDiffOn {f : ℝ → ℝ} {c : ℝ} {n : ℕ} {U : Set ℝ}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ n f U) (t : ℝ) (ht : 2 * c - t ∈ U) :
    iteratedDeriv n (fun s => f (2 * c - s)) t = (-1 : ℝ) ^ n * iteratedDeriv n f (2 * c - t) := by
  -- Rewrite as f ∘ (· + 2c) ∘ (- ·)
  have heq : (fun s => f (2 * c - s)) = (fun s => (fun y => f (y + 2 * c)) (-s)) := by
    ext s; ring_nf
  rw [heq]
  rw [iteratedDeriv_comp_neg n (fun y => f (y + 2 * c)) t]
  simp only [smul_eq_mul]
  congr 1
  -- Use the translation helper
  have hmt : -t + 2 * c = 2 * c - t := by ring
  rw [← hmt] at ht
  convert iteratedDeriv_translate_of_contDiffOn hU_open (-t) ht hf using 1
  rw [hmt]
/-- Taylor remainder bound for x < c case with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the same Lagrange remainder bound as the global ContDiff version.

    The proof uses reflection: define g(t) = f(2c - t), apply Lagrange to g on [c, 2c-x],
    then convert back. -/
theorem taylor_remainder_bound_on_x_lt_c {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hcb : c ≤ b)
    (hf : ContDiffOn ℝ (m + 1) f U)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hxc : x < c) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  -- Define reflected function g(t) = f(2c - t)
  set g : ℝ → ℝ := fun t => f (2 * c - t) with hg_def
  -- Define V = preimage of U under reflection (the reflected open set)
  set V : Set ℝ := (fun t => 2 * c - t) ⁻¹' U with hV_def
  -- V is open (preimage of open set under continuous function)
  have hV_open : IsOpen V := by
    apply IsOpen.preimage _ hU_open
    exact continuous_const.sub continuous_id
  -- g is ContDiffOn V
  have hg_ContDiffOn : ContDiffOn ℝ (m + 1) g V := by
    have hlin : ContDiff ℝ ⊤ (fun t => 2 * c - t) := contDiff_const.sub contDiff_id
    -- g = f ∘ (2c - ·) and (2c - ·) maps V into U
    have hmaps : Set.MapsTo (fun t => 2 * c - t) V U := fun t ht => ht
    have hlin_on : ContDiffOn ℝ (m + 1) (fun t => 2 * c - t) V :=
      (hlin.contDiffOn.mono (Set.subset_univ _)).of_le le_top
    exact ContDiffOn.comp hf hlin_on hmaps
  -- The interval [c, 2c-x]
  have h_interval_lt : c < 2 * c - x := by linarith
  -- [c, 2c-x] maps under t ↦ 2c-t to [x, c] ⊆ [a,b] ⊆ U
  -- So [c, 2c-x] ⊆ V
  have hJ_sub_V : Icc c (2 * c - x) ⊆ V := by
    intro t ht
    -- 2c - t ∈ [x, c] ⊆ [a,b] ⊆ U
    have ht_lower : x ≤ 2 * c - t := by linarith [ht.2]
    have ht_upper : 2 * c - t ≤ c := by linarith [ht.1]
    have h2ct_in_ab : 2 * c - t ∈ Icc a b := by
      refine mem_Icc.mpr ⟨?_, ?_⟩
      · exact le_trans hx.1 ht_lower
      · exact le_trans ht_upper hcb
    exact hI_sub h2ct_in_ab
  -- c ∈ V since c maps to c ∈ [a,b] ⊆ U
  have hcV : c ∈ V := by
    have hc_ab : c ∈ Icc a b := ⟨le_trans hx.1 (le_of_lt hxc), hcb⟩
    -- Need to show c ∈ V, i.e., (fun t => 2 * c - t) c ∈ U, i.e., 2c - c = c ∈ U
    change c ∈ V
    simp only [hV_def, Set.mem_preimage]
    have h2cc : 2 * c - c = c := by ring
    rw [h2cc]
    exact hI_sub hc_ab
  -- Helper: map [c, 2c-x] to [a,b]
  have h_map_to_ab : ∀ t ∈ Icc c (2 * c - x), 2 * c - t ∈ Icc a b := by
    intro t ht
    have ht_lower : x ≤ 2 * c - t := by linarith [ht.2]
    have ht_upper : 2 * c - t ≤ c := by linarith [ht.1]
    exact ⟨le_trans hx.1 ht_lower, le_trans ht_upper hcb⟩
  -- Derivative bound for g using reflection formula
  have hg_deriv_bound : ∀ y ∈ Icc c (2 * c - x), ‖iteratedDeriv (m + 1) g y‖ ≤ M := by
    intro y hy
    have h2cy_ab : 2 * c - y ∈ Icc a b := h_map_to_ab y hy
    have h2cy_U : 2 * c - y ∈ U := hI_sub h2cy_ab
    -- Use the reflection formula
    have hg_deriv : iteratedDeriv (m + 1) g y = (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f (2 *
      c - y) :=
      iteratedDeriv_reflect_of_contDiffOn hU_open hf y h2cy_U
    rw [hg_deriv, norm_mul, Real.norm_eq_abs]
    have h_neg_one : |(-1 : ℝ) ^ (m + 1)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [h_neg_one, one_mul]
    exact hM (2 * c - y) h2cy_ab
  -- Now apply taylor_remainder_bound_on_c_lt_x to g
  have hcV' : a ≤ c := le_trans hx.1 (le_of_lt hxc)
  -- g is ContDiffOn V and Icc c (2c-x) ⊆ V
  have h_taylor_g := taylor_remainder_bound_on_c_lt_x hV_open hJ_sub_V (le_refl c)
      hg_ContDiffOn hg_deriv_bound (2 * c - x) ⟨le_of_lt h_interval_lt, le_refl _⟩ h_interval_lt
  -- g(2c-x) = f(x)
  have hg_at_2cmx : g (2 * c - x) = f x := by simp only [hg_def, sub_sub_cancel]
  -- g^(i)(c) = (-1)^i * f^(i)(c)
  have hg_deriv_c : ∀ i ≤ m + 1, iteratedDeriv i g c = (-1 : ℝ) ^ i * iteratedDeriv i f c := by
    intro i hi
    have hcU : c ∈ U := hI_sub ⟨le_trans hx.1 (le_of_lt hxc), hcb⟩
    have h2cc : 2 * c - c = c := by ring
    rw [← h2cc] at hcU
    have hfi : ContDiffOn ℝ i f U := hf.of_le (by exact_mod_cast hi)
    have hrefl := iteratedDeriv_reflect_of_contDiffOn hU_open hfi c hcU
    simp only [h2cc] at hrefl
    exact hrefl
  -- Now convert the Taylor sum
  -- ∑ (iteratedDeriv i g c / i!) * ((2c-x) - c)^i = ∑ (iteratedDeriv i f c / i!) * (x - c)^i
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i g c / i.factorial) * ((2 * c - x) - c) ^ i =
                 ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i := by
    apply sum_congr rfl
    intro i hi
    have hi_le : i ≤ m + 1 := le_of_lt (mem_range.mp hi)
    rw [hg_deriv_c i hi_le]
    have h_diff : (2 * c - x) - c = c - x := by ring
    rw [h_diff]
    have h_pow : (c - x : ℝ) ^ i = (-1 : ℝ) ^ i * (x - c) ^ i := by
      have : c - x = -(x - c) := by ring
      rw [this, neg_eq_neg_one_mul, mul_pow]
    rw [h_pow]
    -- Simplify: (-1)^i * f^(i)(c) / i! * ((-1)^i * (x-c)^i)
    have h_neg_sq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by rw [← pow_add]; norm_num
    -- Goal: (-1)^i * iteratedDeriv i f c / i! * ((-1)^i * (x-c)^i) = iteratedDeriv i f c / i! *
    -- (x-c)^i
    calc (-1 : ℝ) ^ i * iteratedDeriv i f c / ↑i.factorial * ((-1) ^ i * (x - c) ^ i)
        = ((-1 : ℝ) ^ i * (-1) ^ i) * (iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i) := by ring
      _ = 1 * (iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i) := by rw [h_neg_sq]
      _ = iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i := by ring
  -- Use h_taylor_g with the conversions
  rw [hg_at_2cmx, hsum_eq] at h_taylor_g
  -- The RHS: M * |(2c-x) - c|^(m+1) / (m+1)! = M * |x - c|^(m+1) / (m+1)!
  have h_abs_eq : |(2 * c - x) - c| = |x - c| := by
    have h : (2 * c - x) - c = c - x := by ring
    rw [h, abs_sub_comm]
  rw [h_abs_eq] at h_taylor_g
  exact h_taylor_g
/-- Combined Taylor remainder bound with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the Lagrange remainder bound for any x ∈ [a, b] and center c ∈ [a, b]. -/
theorem taylor_remainder_bound_on {f : ℝ → ℝ} {a b c : ℝ} {n : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hca : a ≤ c) (hcb : c ≤ b)
    (hf : ContDiffOn ℝ n f U)
    (hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ ≤ M)
    (_hMnonneg : 0 ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ‖f x - ∑ i ∈ Finset.range n, (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ n / n.factorial := by
  open Set Finset in
  intro x hx
  cases n with
  | zero =>
    simp only [range_zero, sum_empty, sub_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one]
    have h : f = iteratedDeriv 0 f := iteratedDeriv_zero.symm
    rw [h]
    exact hM x hx
  | succ m =>
    by_cases hxc : x = c
    · -- Case x = c: both sides are 0
      have hrhs : M * |x - c| ^ (m + 1) / ↑(m + 1).factorial = 0 := by
        rw [hxc, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_div]
      rw [hrhs]
      have hsum : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i = f c := by
        rw [hxc]
        simp only [sub_self]
        rw [sum_eq_single 0]
        · simp [iteratedDeriv_zero]
        · intro i _ hi
          have hpos : 0 < i := Nat.pos_of_ne_zero hi
          have : (0 : ℝ) ^ i = 0 := zero_pow hpos.ne'
          simp [this]
        · simp
      rw [hsum, hxc, sub_self, norm_zero]
    · rcases lt_or_gt_of_ne hxc with hxc_lt | hcx_lt
      · exact taylor_remainder_bound_on_x_lt_c hU_open hI_sub hcb hf hM x hx hxc_lt
      · exact taylor_remainder_bound_on_c_lt_x hU_open hI_sub hca hf hM x hx hcx_lt

/-- Key lemma: derivatives of reflected function g(t) = f(2c - t).

For the `x < c` case, we use reflection: define g(t) = f(2c - t), apply Lagrange
to g on [c, 2c-x], then convert back. This lemma shows how g's derivatives
relate to f's derivatives. -/
lemma iteratedDeriv_reflect {f : ℝ → ℝ} {c : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (t : ℝ) :
    iteratedDeriv n (fun s => f (2 * c - s)) t = (-1 : ℝ) ^ n * iteratedDeriv n f (2 * c - t) := by
  have heq : (fun s => f (2 * c - s)) = (fun s => (fun x => f (x + 2 * c)) (-s)) := by
    ext s; ring_nf
  rw [heq]
  rw [iteratedDeriv_comp_neg n (fun x => f (x + 2 * c)) t]
  simp only [smul_eq_mul]
  congr 1
  clear heq
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero]; ring_nf
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hf' : ContDiff ℝ (n + 1) f := hf
    have hderiv_eq : deriv (fun x => f (x + 2 * c)) = fun x => deriv f (x + 2 * c) := by
      ext x
      have hdiff : DifferentiableAt ℝ f (x + 2 * c) :=
        (hf'.differentiable (by simp : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      have hlin : DifferentiableAt ℝ (fun y => y + 2 * c) x :=
        differentiableAt_id.add (differentiableAt_const _)
      have h1 := deriv_comp x hdiff hlin
      simp only [deriv_add_const, deriv_id'', mul_one] at h1
      exact h1
    rw [hderiv_eq]
    have hdf : ContDiff ℝ n (deriv f) := by
      have h := hf'.iterate_deriv' n 1
      simp only [Function.iterate_one] at h
      exact h
    exact ih hdf

/-- Auxiliary lemma: (-1)^n * (-1)^n = 1 for any natural n. -/
lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add]
  norm_num
/-- Taylor remainder bound for c < x case (Lagrange form).

For `c < x`, we apply `taylor_mean_remainder_lagrange` on `[c, x]` and convert
`iteratedDerivWithin` to `iteratedDeriv` using the helper lemmas above. -/
theorem taylor_remainder_bound_c_lt_x {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ}
    (hca : a ≤ c)
    (hf : ContDiff ℝ (m + 1) f)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hcx : c < x) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  have hcx_le : c ≤ x := le_of_lt hcx
  have hI_sub : Icc c x ⊆ Icc a b := Icc_subset_Icc hca hx.2
  have hf_on : ContDiffOn ℝ (m + 1) f (Icc c x) := hf.contDiffOn.mono hI_sub
  have hf_on_m : ContDiffOn ℝ m f (Icc c x) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by simp
    exact hf_on.of_le hm_le
  have hf_diff : DifferentiableOn ℝ (iteratedDerivWithin m f (Icc c x)) (Ioo c x) := by
    have huniq := uniqueDiffOn_Icc hcx
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hf_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hf_on_m' : ContDiffOn ℝ m f (uIcc c x) := by rwa [uIcc_of_le hcx_le]
  have hf_diff' : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc c x)) (uIoo c x) := by
    rwa [uIcc_of_le hcx_le, uIoo_of_lt hcx]
  obtain ⟨ξ, hξ_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := x) hcx.ne hf_on_m' hf_diff'
  have hξ_mem_Ioo : ξ ∈ Ioo c x := by rwa [uIoo_of_lt hcx] at hξ_mem
  rw [uIcc_of_le hcx_le] at hLagrange
  have hξ_ab : ξ ∈ Icc a b := hI_sub (Ioo_subset_Icc_self hξ_mem_Ioo)
  have hderiv_ξ : iteratedDerivWithin (m + 1) f (Icc c x) ξ = iteratedDeriv (m + 1) f ξ :=
    iteratedDerivWithin_Icc_interior_eq hcx hξ_mem_Ioo
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i =
                 taylorWithinEval f m (Icc c x) c x := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hderiv_c : iteratedDerivWithin i f (Icc c x) c = iteratedDeriv i f c := by
      have hi_lt : i < m + 1 := mem_range.mp hi
      have hi_le : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
        have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
        exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
      exact iteratedDerivWithin_Icc_left_eq_iteratedDeriv hcx (hf.of_le hi_le)
    rw [hderiv_c]
    simp only [smul_eq_mul]
    ring
  rw [hsum_eq, hLagrange, hderiv_ξ]
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  have hxc_pos : 0 < x - c := sub_pos.mpr hcx
  rw [abs_pow, abs_of_pos hxc_pos]
  have hbound := hM ξ hξ_ab
  have h_pow_fact_pos : 0 < (x - c) ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · exact pow_pos hxc_pos _
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * (x - c) ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by ring
/-- Taylor remainder bound for x < c case (Lagrange form via reflection).

For `x < c`, we define g(t) = f(2c - t), apply `taylor_mean_remainder_lagrange` on `[c, 2c-x]`,
then use `iteratedDeriv_reflect` to convert back to f's derivatives. The key insight is that
g's Taylor expansion at c, evaluated at 2c-x, equals f's Taylor expansion at c, evaluated at x,
because the (-1)^i factors from the derivatives cancel with the (-1)^i factors from the powers. -/
theorem taylor_remainder_bound_x_lt_c {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ}
    (hcb : c ≤ b)
    (hf : ContDiff ℝ (m + 1) f)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hxc : x < c) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  -- Define reflected function g(t) = f(2c - t)
  set g : ℝ → ℝ := fun t => f (2 * c - t) with hg_def
  -- g is smooth
  have hg_smooth : ContDiff ℝ (m + 1) g := by
    have hlin : ContDiff ℝ ⊤ (fun t => 2 * c - t) := contDiff_const.sub contDiff_id
    exact hf.comp (hlin.of_le le_top)
  -- The interval [c, 2c - x]
  have h_interval_lt : c < 2 * c - x := by linarith
  -- Apply taylor_mean_remainder_lagrange to g on [c, 2c - x]
  have hg_on : ContDiffOn ℝ (m + 1) g (Icc c (2 * c - x)) := hg_smooth.contDiffOn
  have h_interval_le : c ≤ 2 * c - x := le_of_lt h_interval_lt
  have hg_on_m : ContDiffOn ℝ m g (Icc c (2 * c - x)) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by norm_cast; omega
    exact hg_on.of_le hm_le
  have hg_diff : DifferentiableOn ℝ (iteratedDerivWithin m g (Icc c (2 * c - x))) (Ioo c (2 * c -
    x)) := by
    have huniq := uniqueDiffOn_Icc h_interval_lt
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hg_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hg_on_m' : ContDiffOn ℝ m g (uIcc c (2 * c - x)) := by rwa [uIcc_of_le h_interval_le]
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin m g (uIcc c (2 * c - x))) (uIoo c (2 * c
    - x)) := by
    rwa [uIcc_of_le h_interval_le, uIoo_of_lt h_interval_lt]
  obtain ⟨ξ', hξ'_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := 2 * c - x)
      h_interval_lt.ne hg_on_m' hg_diff'
  have hξ'_mem_Ioo : ξ' ∈ Ioo c (2 * c - x) := by
    rwa [uIoo_of_lt h_interval_lt] at hξ'_mem
  rw [uIcc_of_le h_interval_le] at hLagrange
  -- ξ = 2c - ξ' ∈ (x, c)
  set ξ := 2 * c - ξ' with hξ_def
  have hξ'_lt_2cmx : ξ' < 2 * c - x := hξ'_mem_Ioo.2
  have hξ'_gt_c : c < ξ' := hξ'_mem_Ioo.1
  have hξ_gt_x : x < ξ := by simp only [hξ_def]; linarith
  have hξ_lt_c : ξ < c := by simp only [hξ_def]; linarith
  have hξ_ab : ξ ∈ Icc a b :=
    ⟨le_trans hx.1 (le_of_lt hξ_gt_x), le_trans (le_of_lt hξ_lt_c) hcb⟩
  have hg_at_2cmx : g (2 * c - x) = f x := by simp only [hg_def, sub_sub_cancel]
  -- g^{(k)}(c) = (-1)^k * f^{(k)}(c)
  have hg_deriv : ∀ k ≤ m + 1, iteratedDeriv k g c = (-1 : ℝ) ^ k * iteratedDeriv k f c := by
    intro k hk
    have hg_eq : g = fun s => f (2 * c - s) := hg_def
    rw [hg_eq]
    rw [iteratedDeriv_reflect (hf.of_le (by exact_mod_cast hk)) c]
    congr 1
    ring_nf
  -- Key: taylorWithinEval g m (Icc c (2c-x)) c (2c-x) = ∑ ... of f's Taylor coeffs
  have hTaylor_g_to_f : taylorWithinEval g m (Icc c (2 * c - x)) c (2 * c - x) =
                        ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hi_lt : i < m + 1 := mem_range.mp hi
    have hi_le : i ≤ m + 1 := le_of_lt hi_lt
    have hi_le' : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
      have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
      exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
    have hderiv_c : iteratedDerivWithin i g (Icc c (2 * c - x)) c = iteratedDeriv i g c :=
      iteratedDerivWithin_Icc_left_eq_iteratedDeriv h_interval_lt (hg_smooth.of_le hi_le')
    rw [hderiv_c, hg_deriv i hi_le]
    simp only [smul_eq_mul]
    have h_diff : (2 * c - x) - c = c - x := by ring
    rw [h_diff]
    have h_pow : (c - x : ℝ) ^ i = (-1 : ℝ) ^ i * (x - c) ^ i := by
      have : c - x = -(x - c) := by ring
      rw [this, neg_eq_neg_one_mul, mul_pow]
    rw [h_pow]
    have h_neg_sq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := neg_one_pow_mul_self i
    have hgoal : (↑i.factorial : ℝ)⁻¹ * ((-1 : ℝ) ^ i * (x - c) ^ i) * ((-1 : ℝ) ^ i *
      iteratedDeriv i f c)
               = iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i := by
      have h1 : (↑i.factorial : ℝ)⁻¹ * ((-1 : ℝ) ^ i * (x - c) ^ i) * ((-1 : ℝ) ^ i *
        iteratedDeriv i f c)
              = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ i) * ((↑i.factorial : ℝ)⁻¹ * (x - c) ^ i *
                iteratedDeriv i f c) := by ring
      rw [h1, h_neg_sq, one_mul]
      field_simp
    exact hgoal
  -- Now use Lagrange formula
  rw [hg_at_2cmx] at hLagrange
  rw [← hTaylor_g_to_f, hLagrange]
  have h_pow_rhs : ((2 * c - x) - c : ℝ) ^ (m + 1) = (c - x) ^ (m + 1) := by ring
  have hderiv_ξ' : iteratedDerivWithin (m + 1) g (Icc c (2 * c - x)) ξ' = iteratedDeriv (m + 1) g
    ξ' :=
    iteratedDerivWithin_Icc_interior_eq h_interval_lt hξ'_mem_Ioo
  -- iteratedDeriv (m+1) g ξ' = (-1)^(m+1) * iteratedDeriv (m+1) f ξ
  have hg_deriv_ξ' : iteratedDeriv (m + 1) g ξ' = (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ
    := by
    have hg_eq : g = fun s => f (2 * c - s) := hg_def
    have h := @iteratedDeriv_reflect f c (m + 1) hf ξ'
    simp only [hg_eq, hξ_def, h]
  rw [hderiv_ξ', hg_deriv_ξ', h_pow_rhs]
  have h_pow_eq : (c - x : ℝ) ^ (m + 1) = (-1 : ℝ) ^ (m + 1) * (x - c) ^ (m + 1) := by
    have : c - x = -(x - c) := by ring
    rw [this, neg_eq_neg_one_mul, mul_pow]
  rw [h_pow_eq]
  -- Simplify
  have h_simplify : (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ * ((-1 : ℝ) ^ (m + 1) * (x - c)
    ^ (m + 1)) / ↑(m + 1).factorial =
                   iteratedDeriv (m + 1) f ξ * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by
    have h_neg_sq := neg_one_pow_mul_self (m + 1)
    have h1 : (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ * ((-1 : ℝ) ^ (m + 1) * (x - c) ^ (m
      + 1)) / ↑(m + 1).factorial =
              ((-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1)) * (iteratedDeriv (m + 1) f ξ * (x - c) ^
                (m + 1)) / ↑(m + 1).factorial := by ring
    rw [h1, h_neg_sq, one_mul]
  rw [h_simplify]
  -- Bound the norm
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  rw [abs_pow]
  have hbound := hM ξ hξ_ab
  have hxc_ne : x - c ≠ 0 := by linarith
  have h_pow_fact_pos : 0 < |x - c| ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · apply pow_pos; exact abs_pos.mpr hxc_ne
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * |x - c| ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * (|x - c| ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * (|x - c| ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * |x - c| ^ (m + 1) / ↑(m + 1).factorial := by ring
/-- Lagrange form remainder bound for Taylor approximation.

If `|f^(n)(x)| ≤ M` for all x in [a, b], and `c ∈ [a, b]`, then the Taylor polynomial
of degree `n-1` (sum over range n) satisfies: for any `x ∈ [a, b]`:
  `|f(x) - T_{n-1}(x; c)| ≤ M * |x - c|^n / n!`

Note: The sum `∑ i ∈ Finset.range n` gives terms 0..n-1 (degree n-1 polynomial).
The remainder involves the n-th derivative, matching our bound on `iteratedDeriv n f`.

All cases are fully proved:
- **Case n = 0**: Direct bound. ✓
- **Case n > 0, x = c**: Trivial (both sides zero). ✓
- **Case n > 0, c < x**: Via `taylor_remainder_bound_c_lt_x`. ✓
- **Case n > 0, x < c**: Via `taylor_remainder_bound_x_lt_c` (reflection). ✓
-/
theorem taylor_remainder_bound {f : ℝ → ℝ} {a b c : ℝ} {n : ℕ} {M : ℝ}
    (_hab : a ≤ b) (hca : a ≤ c) (hcb : c ≤ b)
    (hf : ContDiff ℝ n f)
    (hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ ≤ M)
    (_hMnonneg : 0 ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ‖f x - ∑ i ∈ Finset.range n, (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ n / n.factorial := by
  open Set Finset in
  intro x hx
  cases n with
  | zero =>
    -- Case n = 0: sum is empty, need ‖f x‖ ≤ M
    simp only [range_zero, sum_empty, sub_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one]
    have h : f = iteratedDeriv 0 f := iteratedDeriv_zero.symm
    rw [h]
    exact hM x hx
  | succ m =>
    by_cases hxc : x = c
    · -- Case x = c: both sides are 0
      have hrhs : M * |x - c| ^ (m + 1) / ↑(m + 1).factorial = 0 := by
        rw [hxc, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_div]
      rw [hrhs]
      have hsum : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i = f c := by
        rw [hxc]
        simp only [sub_self]
        rw [sum_eq_single 0]
        · simp [iteratedDeriv_zero]
        · intro i _ hi
          have hpos : 0 < i := Nat.pos_of_ne_zero hi
          have : (0 : ℝ) ^ i = 0 := zero_pow hpos.ne'
          simp [this]
        · simp
      rw [hsum, hxc, sub_self, norm_zero]
    · -- Case x ≠ c
      rcases lt_or_gt_of_ne hxc with hxc_lt | hcx_lt
      · -- Case x < c: use reflection approach
        exact taylor_remainder_bound_x_lt_c hcb hf hM x hx hxc_lt
      · -- Case c < x: fully proved
        exact taylor_remainder_bound_c_lt_x hca hf hM x hx hcx_lt

/-! ### Common Taylor expansions -/

/-- Taylor coefficients for exp at 0: 1/n! -/
def expTaylorCoeff (n : ℕ) : ℚ := 1 / n.factorial

/-- Taylor coefficients for sin at 0 -/
def sinTaylorCoeff (n : ℕ) : ℚ :=
  if n % 2 = 0 then 0
  else if (n / 2) % 2 = 0 then 1 / n.factorial
  else -1 / n.factorial

/-- Taylor coefficients for cos at 0 -/
def cosTaylorCoeff (n : ℕ) : ℚ :=
  if n % 2 = 1 then 0
  else if (n / 2) % 2 = 0 then 1 / n.factorial
  else -1 / n.factorial

/-! ### Derivative bounds for common functions -/

/-- All derivatives of exp are bounded by exp on any bounded interval -/
theorem exp_deriv_bound {a b : ℝ} (_hab : a ≤ b) (n : ℕ) :
    ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n Real.exp x‖ ≤ Real.exp b := by
  intro x hx
  rw [iteratedDeriv_eq_iterate]
  rw [Real.iter_deriv_exp]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  exact Real.exp_le_exp.mpr hx.2

/-- All derivatives of sin and cos are bounded by 1.
    The derivatives cycle: sin → cos → -sin → -cos → sin → ... -/
theorem sin_cos_deriv_bound (n : ℕ) :
    ∀ x : ℝ, ‖iteratedDeriv n Real.sin x‖ ≤ 1 ∧ ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  intro x
  -- Prove by induction that both bounds hold together
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨Real.abs_sin_le_one x, Real.abs_cos_le_one x⟩
  | succ n ih =>
    constructor
    · -- sin case: d/dx sin = cos
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.sin = Real.cos := Real.deriv_sin
      rw [hderiv]
      exact ih.2
    · -- cos case: d/dx cos = -sin
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.cos = fun y => -Real.sin y := Real.deriv_cos'
      rw [hderiv]
      rw [iteratedDeriv_fun_neg n Real.sin x, norm_neg]
      exact ih.1

/-- cosh x ≤ exp |x| for all x -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have habs_neg : -x ≤ |x| := neg_le_abs x
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr habs_neg
  linarith

/-- |sinh x| ≤ cosh x for all x -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_sq : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := Real.cosh_sq x
  have hsinh_sq_le : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by linarith [sq_nonneg (Real.cosh x)]
  rw [abs_le]
  constructor
  · -- -cosh x ≤ sinh x
    have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    nlinarith [sq_nonneg (Real.cosh x + Real.sinh x), sq_nonneg (Real.cosh x - Real.sinh x)]
  · -- sinh x ≤ cosh x
    have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    nlinarith [sq_nonneg (Real.cosh x + Real.sinh x), sq_nonneg (Real.cosh x - Real.sinh x)]

/-- All derivatives of sinh and cosh are bounded by exp(max(|a|, |b|)) on [a, b].
    The derivatives cycle: sinh → cosh → sinh → cosh → ... -/
theorem sinh_cosh_deriv_bound {a b : ℝ} (_hab : a ≤ b) (n : ℕ) :
    ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n Real.sinh x‖ ≤ Real.exp (max (|a|) (|b|)) ∧
                       ‖iteratedDeriv n Real.cosh x‖ ≤ Real.exp (max (|a|) (|b|)) := by
  intro x hx
  set M := Real.exp (max (|a|) (|b|)) with hM_def
  have habs_x_le : |x| ≤ max (|a|) (|b|) := by
    rw [abs_le]
    constructor
    · calc -max (|a|) (|b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
        _ ≤ a := neg_abs_le a
        _ ≤ x := hx.1
    · calc x ≤ b := hx.2
        _ ≤ |b| := le_abs_self b
        _ ≤ max (|a|) (|b|) := le_max_right _ _
  have hcosh_bound : Real.cosh x ≤ M := by
    calc Real.cosh x ≤ Real.exp |x| := cosh_le_exp_abs x
      _ ≤ Real.exp (max (|a|) (|b|)) := Real.exp_le_exp.mpr habs_x_le
  have hsinh_bound : |Real.sinh x| ≤ M := by
    calc |Real.sinh x| ≤ Real.cosh x := abs_sinh_le_cosh x
      _ ≤ M := hcosh_bound
  -- Prove by induction that both bounds hold
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Real.norm_eq_abs]
    exact ⟨hsinh_bound, by rw [abs_of_pos (Real.cosh_pos x)]; exact hcosh_bound⟩
  | succ n ih =>
    constructor
    · -- sinh case: d/dx sinh = cosh
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.sinh = Real.cosh := by
        funext x
        exact LeanCert.Core.DerivativeIntervals.sinh_deriv_eq x
      rw [hderiv]
      exact ih.2
    · -- cosh case: d/dx cosh = sinh
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.cosh = Real.sinh := Real.deriv_cosh
      rw [hderiv]
      exact ih.1

/- The n-th iterated derivative of log at x > 0 is (-1)^(n-1) * (n-1)! * x^(-n) for n ≥ 1. -/
theorem iteratedDeriv_log {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.log x = (-1)^(n-1) * (n-1).factorial * x^(-(n : ℤ)) := by
    match n with
    | 1 =>
      -- n = 1: iteratedDeriv 1 log x = deriv log x = 1/x = x^(-1)
      simp only [iteratedDeriv_one, Real.deriv_log', tsub_self, pow_zero, Nat.factorial_zero,
        Nat.cast_one, mul_one, Int.reduceNeg, zpow_neg, zpow_one, one_mul]
    | n + 2 =>
      -- n + 2: use induction
      -- iteratedDeriv (n+2) log = deriv (iteratedDeriv (n+1) log)
      rw [iteratedDeriv_succ]
      -- By IH: iteratedDeriv (n+1) log y = (-1)^n * n! * y^(-(n+1)) for y > 0
      have h_eq : ∀ y : ℝ, 0 < y → iteratedDeriv (n + 1) Real.log y =
          (-1 : ℝ)^n * n.factorial * y^(-(n + 1 : ℤ)) := fun y hy => iteratedDeriv_log
            n.succ_ne_zero hy
      have h_deriv_eq : deriv (iteratedDeriv (n + 1) Real.log) x =
          deriv (fun y => (-1 : ℝ)^n * n.factorial * y^(-(n + 1 : ℤ))) x := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_gt_nhds hx] with y hy
        exact h_eq y hy
      rw [h_deriv_eq]
      have hdiff : DifferentiableAt ℝ (fun y => y ^ (-(n + 1 : ℤ))) x := by
        apply DifferentiableAt.zpow differentiableAt_id
        left; exact hx.ne'
      rw [deriv_const_mul _ hdiff, deriv_zpow (-(n + 1 : ℤ)) x]
      simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_ofNat]
      rw [pow_succ (-1 : ℝ) n, Nat.factorial_succ]
      push_cast
      calc
        (-1) ^ n * n.factorial * ((-1 + -(n : ℤ)) * x ^ (-1 + -(n : ℤ) - 1))
        _ = (-1) ^ n * n.factorial * ((-1 + -(n : ℤ)) * x ^ (-2 + -(n : ℤ))) := by congr 3; grind
        _ = (-1) ^ n * -1 * ((↑n + 1) * n.factorial) * x ^ (-2 + -(n : ℤ)) := by simp; ring

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Rational Endpoint Intervals - Computable Taylor Series

This file provides computable interval enclosures for transcendental functions
using Taylor series with rational coefficients and rigorous remainder bounds.

## Main definitions

* `ratFactorial` - Compute n! as a rational
* `pow` - Compute interval power
* `absInterval`, `maxAbs` - Absolute value helpers
* `evalTaylorSeries` - Evaluate Taylor polynomial on an interval
* `expComputable`, `sinComputable`, `cosComputable` - Computable transcendental functions
* `sinhComputable`, `coshComputable` - Computable hyperbolic functions

## Main theorems

* `mem_pow` - FTIA for interval power
* `mem_evalTaylorSeries` - General FTIA for Taylor series
* `mem_expComputable`, `mem_sinComputable`, `mem_cosComputable` - FTIA for computable functions

## Design notes

All definitions in this file use only rational arithmetic and are fully computable.
The proofs connect these to the real-valued functions via Taylor's theorem.
-/

/-! ### Computable Taylor series helpers -/

public section

namespace LeanCert.Core

namespace IntervalRat

/-- Compute n! as a Rational -/
@[expose]
def ratFactorial (n : ℕ) : ℚ := (Nat.factorial n : ℚ)

/-- Compute the integer power of an interval using exponentiation by squaring.
    O(log n) interval multiplications instead of O(n). -/
def pow (I : IntervalRat) : ℕ → IntervalRat
  | 0 => singleton 1
  | 1 => I
  | n + 2 =>
    let half := pow I ((n + 2) / 2)
    let sq := mul half half
    if (n + 2) % 2 == 0 then sq else mul I sq

/-- Compute the absolute value interval: |I| = [0, max(|lo|, |hi|)] if 0 ∈ I,
    or [min(|lo|,|hi|), max(|lo|,|hi|)] otherwise -/
def absInterval (I : IntervalRat) : IntervalRat :=
  if h1 : I.lo ≥ 0 then
    I
  else if h2 : I.hi ≤ 0 then
    neg I
  else
    ⟨0, max (-I.lo) I.hi, by
      apply le_max_of_le_right
      push Not at h1 h2
      linarith⟩

/-- Maximum absolute value of an interval -/
@[expose]
def maxAbs (I : IntervalRat) : ℚ := max (|I.lo|) (|I.hi|)

/-- Evaluate Taylor series ∑_{i=0}^{n} c_i * x^i at interval I using Horner's method.
    Computes c₀ + I * (c₁ + I * (c₂ + ... + I * cₙ)), which is mathematically
    equivalent to the direct sum but uses fewer operations and often gives tighter
    bounds by reducing the dependency problem in interval arithmetic. -/
@[expose]
def evalTaylorSeries (coeffs : List ℚ) (I : IntervalRat) : IntervalRat :=
  coeffs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0)

/-! ### Computable exp via Taylor series -/

/-- Tail-recursive exp coefficient generator.
    `expTaylorCoeffsAux n k c` produces `n+1` coefficients starting at index `k`,
    assuming `c = 1 / k!`. -/
def expTaylorCoeffsAux : ℕ → ℕ → ℚ → List ℚ
  | 0, _, c => [c]
  | (n + 1), k, c => c :: expTaylorCoeffsAux n (k + 1) (c / (k + 1))

/-- Taylor coefficients for exp: 1/i! for i = 0, 1, ..., n.
    Implemented iteratively to avoid repeated factorial recomputation. -/
def expTaylorCoeffs (n : ℕ) : List ℚ :=
  expTaylorCoeffsAux n 0 1

/-- `ratFactorial` unfolds factorial as a product. -/
private lemma ratFactorial_succ (k : ℕ) :
    ratFactorial (k + 1) = ratFactorial k * (k + 1) := by
  simp [ratFactorial, Nat.factorial_succ, Nat.cast_mul, mul_comm]

private lemma map_range_succ {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- range (n+2) = range (n+1) ++ [n+1]
      calc
        (List.range (n + 2)).map f
            = (List.range (n + 1) ++ [n + 1]).map f := by
                simp [List.range_succ]
        _ = (List.range (n + 1)).map f ++ [f (n + 1)] := by
                simp [List.map_append]
        _ = (f 0 :: (List.range n).map (fun i => f (i + 1))) ++ [f (n + 1)] := by
                simp [ih]
        _ = f 0 :: ((List.range n).map (fun i => f (i + 1)) ++ [f (n + 1)]) := by
                rfl
        _ = f 0 :: (List.range (n + 1)).map (fun i => f (i + 1)) := by
                simp [List.range_succ, List.map_append]

/-- Iterative exp coefficients match the standard `1 / i!` definition. -/
private lemma expTaylorCoeffsAux_eq_range (n k : ℕ) :
    expTaylorCoeffsAux n k (1 / ratFactorial k) =
      (List.range (n + 1)).map (fun i => 1 / ratFactorial (i + k)) := by
  induction n generalizing k with
  | zero =>
      simp [expTaylorCoeffsAux]
  | succ n ih =>
      have hstep : (ratFactorial k)⁻¹ / (k + 1) = (ratFactorial (k + 1))⁻¹ := by
        -- (1/k!) / (k+1) = 1/(k+1)!
        simp [ratFactorial_succ, div_eq_mul_inv, mul_comm]
      calc
        expTaylorCoeffsAux (n + 1) k (1 / ratFactorial k)
            = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) ((1 / ratFactorial k) / (k + 1)) := by
                  rfl
        _ = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) ((ratFactorial k)⁻¹ / (k + 1)) := by
                  simp [one_div]
        _ = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) (ratFactorial (k + 1))⁻¹ := by
                  simp [hstep]
        _ = (1 / ratFactorial k) ::
              (List.range (n + 1)).map (fun i => (ratFactorial (i + (k + 1)))⁻¹) := by
                  simpa [one_div] using (ih (k + 1))
        _ = (List.range (n + 2)).map (fun i => 1 / ratFactorial (i + k)) := by
            -- unfold the range map at the front
            have hmap := map_range_succ (fun i => 1 / ratFactorial (i + k)) (n + 1)
            -- rewrite and simplify
            simpa [one_div, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmap.symm

private lemma expTaylorCoeffs_eq_range_map (n : ℕ) :
    expTaylorCoeffs n = (List.range (n + 1)).map (fun i => 1 / ratFactorial i) := by
  have h0 : (1 / ratFactorial 0 : ℚ) = 1 := by simp [ratFactorial]
  simpa [expTaylorCoeffs, h0] using (expTaylorCoeffsAux_eq_range n 0)

/-- Computable exp remainder bound using rational arithmetic.
    The Lagrange remainder is exp(ξ) * x^{n+1} / (n+1)! where ξ is between 0 and x.
    We use e < 3, so e^r ≤ 3^(⌈r⌉+1) as a conservative bound.

    Returns an interval [-R, R] where R bounds the remainder. -/
def expRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Crude bound: e < 3, so e^r ≤ 3^(ceil(r)+1)
  let expBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  let xBound := r ^ (n + 1)
  let R := expBound * xBound / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; norm_num
        · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- The raw rational Taylor enclosure of the exponential at a point. -/
def expPointComputableRaw (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let I := singleton q
  let coeffs := expTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  add polyVal remainder

/-- Heuristic reduction factor for exp evaluation.
    We choose `k = log2(ceil(|q|) + 1)`, so `2^k` grows roughly with |q|.
    No correctness depends on the specific choice; it only affects performance. -/
def expReduceK (q : ℚ) : ℕ :=
  Nat.log2 (Nat.ceil |q| + 1)

/-- Computable interval enclosure for exp at a single rational point.
    Uses argument reduction: `exp(q) = exp(q/2^k)^(2^k)`. -/
def expPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let k := expReduceK q
  let m : ℕ := (2:ℕ)^k
  let q' : ℚ := q / m
  pow (expPointComputableRaw q' n) m

/-- Point exponential using Taylor coefficients prepared for depth `n`. -/
def expPointComputableWithCoeffs (q : ℚ) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let k := expReduceK q
  let m : ℕ := (2 : ℕ) ^ k
  let q' : ℚ := q / m
  let I := singleton q'
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  pow (add polyVal remainder) m

theorem expPointComputableWithCoeffs_eq (q : ℚ) (n : ℕ) :
    expPointComputableWithCoeffs q n (expTaylorCoeffs n) = expPointComputable q n := by
  simp [expPointComputableWithCoeffs, expPointComputable, expPointComputableRaw]

/-- Hull of two intervals: smallest interval containing both. -/
def hull (I J : IntervalRat) : IntervalRat :=
  ⟨min I.lo J.lo, max I.hi J.hi, le_trans (min_le_left _ _) (le_trans I.le (le_max_left _ _))⟩

/-- Membership in hull -/
theorem mem_hull_left {x : ℝ} {I J : IntervalRat} (hx : x ∈ I) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_left _ _) hx.1
  · exact le_trans hx.2 (le_max_left _ _)

theorem mem_hull_right {x : ℝ} {I J : IntervalRat} (hx : x ∈ J) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_right _ _) hx.1
  · exact le_trans hx.2 (le_max_right _ _)

/-- Computable interval enclosure for exp using Taylor series with monotonicity optimization.

    exp(x) = ∑_{i=0}^{n} x^i/i! + R where |R| ≤ exp(|x|) * |x|^{n+1} / (n+1)!

    For intervals not crossing 0, we use endpoint evaluation and take the hull,
    which is tighter than direct Taylor evaluation due to interval widening.

    This is fully computable using only rational arithmetic. -/
@[expose]
def expComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  if I.hi ≤ 0 ∨ 0 ≤ I.lo then
    -- Interval doesn't cross 0: use endpoint evaluation for tighter bounds
    let expLo := expPointComputable I.lo n
    let expHi := expPointComputable I.hi n
    hull expLo expHi
  else
    -- Interval crosses 0: use standard Taylor (can't avoid interval widening)
    let coeffs := expTaylorCoeffs n
    let polyVal := evalTaylorSeries coeffs I
    let remainder := expRemainderBoundComputable I n
    add polyVal remainder

/-- Interval exponential using Taylor coefficients prepared for depth `n`. -/
def expComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  if I.hi ≤ 0 ∨ 0 ≤ I.lo then
    let expLo := expPointComputableWithCoeffs I.lo n coeffs
    let expHi := expPointComputableWithCoeffs I.hi n coeffs
    hull expLo expHi
  else
    let polyVal := evalTaylorSeries coeffs I
    let remainder := expRemainderBoundComputable I n
    add polyVal remainder

theorem expComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    expComputableWithCoeffs I n (expTaylorCoeffs n) = expComputable I n := by
  simp [expComputableWithCoeffs, expComputable, expPointComputableWithCoeffs_eq]

/-! ### Computable sin via Taylor series -/

/-- Taylor coefficients for sin: 0, 1, 0, -1/6, 0, 1/120, ... -/
@[expose]
def sinTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / ratFactorial i
    else 0)

/-- Computable sin remainder bound.
    Since |sin^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
@[expose]
def sinRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for sin using Taylor series.

    sin(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k+1}/(2k+1)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of sin are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
@[expose]
def sinComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := sinTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-- Interval sine using Taylor coefficients prepared for depth `n`. -/
def sinComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw

theorem sinComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    sinComputableWithCoeffs I n (sinTaylorCoeffs n) = sinComputable I n := by
  simp [sinComputableWithCoeffs, sinComputable]

/-! ### Computable cos via Taylor series -/

/-- Taylor coefficients for cos: 1, 0, -1/2, 0, 1/24, 0, ... -/
@[expose]
def cosTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / ratFactorial i
    else 0)

/-- Computable cos remainder bound.
    Since |cos^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
@[expose]
def cosRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for cos using Taylor series.

    cos(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k}/(2k)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of cos are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
@[expose]
def cosComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := cosTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-- Interval cosine using Taylor coefficients prepared for depth `n`. -/
def cosComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw

theorem cosComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    cosComputableWithCoeffs I n (cosTaylorCoeffs n) = cosComputable I n := by
  simp [cosComputableWithCoeffs, cosComputable]

/-! ### Computable sinh and cosh via exp -/

/-- Computable interval enclosure for sinh at a single rational point.
    Uses the definition sinh(q) = (exp(q) - exp(-q)) / 2. -/
def sinhPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- sinh(q) = (exp(q) - exp(-q)) / 2
  -- Lower bound: (expPos.lo - expNeg.hi) / 2
  -- Upper bound: (expPos.hi - expNeg.lo) / 2
  let sinhLo := (expPos.lo - expNeg.hi) / 2
  let sinhHi := (expPos.hi - expNeg.lo) / 2
  if h : sinhLo ≤ sinhHi then
    ⟨sinhLo, sinhHi, h⟩
  else
    ⟨min sinhLo sinhHi, max sinhLo sinhHi, @min_le_max _ _ sinhLo sinhHi⟩

/-- Computable interval enclosure for cosh at a single rational point.
    Uses the definition cosh(q) = (exp(q) + exp(-q)) / 2. -/
def coshPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- cosh(q) = (exp(q) + exp(-q)) / 2
  -- Lower bound: (expPos.lo + expNeg.lo) / 2
  -- Upper bound: (expPos.hi + expNeg.hi) / 2
  let coshLo := (expPos.lo + expNeg.lo) / 2
  let coshHi := (expPos.hi + expNeg.hi) / 2
  -- cosh ≥ 1 always, so ensure lower bound is at least 1
  let safeLo := max 1 coshLo
  if h : safeLo ≤ coshHi then
    ⟨safeLo, coshHi, h⟩
  else
    ⟨1, max 2 coshHi, by
      have h1 : (1 : ℚ) ≤ 2 := by norm_num
      exact le_trans h1 (le_max_left _ _)⟩

/-- The lower bound of coshPointComputable is always at least 1. -/
theorem coshPointComputable_lo_ge_one (q : ℚ) (n : ℕ) : 1 ≤ (coshPointComputable q n).lo := by
  simp only [coshPointComputable]
  split_ifs with h
  · exact le_max_left 1 _
  · exact le_refl 1

/-- Computable interval enclosure for sinh using exp with endpoint evaluation.

    sinh(x) = (exp(x) - exp(-x)) / 2
    Since sinh is strictly monotone increasing, sinh([a,b]) = [sinh(a), sinh(b)].
    We use endpoint evaluation for tight bounds. -/
@[expose]
def sinhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- sinh is strictly monotone increasing, so evaluate at endpoints
  let sinhLo := sinhPointComputable I.lo n
  let sinhHi := sinhPointComputable I.hi n
  hull sinhLo sinhHi

/-- Computable interval enclosure for cosh using exp with endpoint evaluation.

    cosh(x) = (exp(x) + exp(-x)) / 2
    cosh has minimum 1 at x = 0, and is symmetric: cosh(-x) = cosh(x).
    - cosh is decreasing on (-∞, 0]
    - cosh is increasing on [0, ∞)

    We use endpoint evaluation with monotonicity for tight bounds. -/
@[expose]
def coshComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coshLo := coshPointComputable I.lo n
  let coshHi := coshPointComputable I.hi n
  if 0 ≤ I.lo then
    -- Interval is non-negative: cosh is increasing, so [cosh(lo), cosh(hi)]
    hull coshLo coshHi
  else if I.hi ≤ 0 then
    -- Interval is non-positive: cosh is decreasing, so [cosh(hi), cosh(lo)]
    hull coshHi coshLo
  else
    -- Interval contains 0: minimum is 1 at x=0, max is at whichever endpoint is farther
    let maxEndpoint := hull coshLo coshHi
    ⟨1, maxEndpoint.hi, by
      -- coshPointComputable ensures lower bound ≥ 1 via max 1 _
      have hlo_ge1 := coshPointComputable_lo_ge_one I.lo n
      have hhi_ge1 := coshPointComputable_lo_ge_one I.hi n
      calc (1 : ℚ) ≤ min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo :=
          le_min hlo_ge1 hhi_ge1
        _ = maxEndpoint.lo := rfl
        _ ≤ maxEndpoint.hi := maxEndpoint.le⟩

/-! ### FTIA for pow -/

/-- FTIA for interval power (binary exponentiation version) -/
theorem mem_pow {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    x ^ n ∈ pow I n := by
  match n with
  | 0 =>
    simp only [_root_.pow_zero, pow, mem_def, singleton]
    norm_num
  | 1 =>
    simp only [_root_.pow_one, pow]
    exact hx
  | n + 2 =>
    have ih_half := mem_pow hx ((n + 2) / 2)
    have h_sq := mem_mul ih_half ih_half
    change x ^ (n + 2) ∈ pow I (n + 2)
    unfold pow
    split
    · -- even case: x^(n+2) = (x^half)^2
      next heven =>
      have := beq_iff_eq.mp heven
      rw [show x ^ (n + 2) = x ^ ((n + 2) / 2) * x ^ ((n + 2) / 2) from by
        rw [← _root_.pow_add]; congr 1; omega]
      exact h_sq
    · -- odd case: x^(n+2) = x * (x^half)^2
      next heven =>
      have hodd : (n + 2) % 2 ≠ 0 := fun h => heven (beq_iff_eq.mpr h)
      rw [show x ^ (n + 2) = x * (x ^ ((n + 2) / 2) * x ^ ((n + 2) / 2)) from by
        rw [← _root_.pow_add, ← mul_comm, ← _root_.pow_succ]; congr 1; omega]
      exact mem_mul hx h_sq
termination_by n

/-! ### Helper lemmas for Taylor series membership -/

/-- Any x in I has |x| ≤ maxAbs I -/
theorem abs_le_maxAbs {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : |x| ≤ maxAbs I := by
  simp only [mem_def, maxAbs] at *
  have hlo : -(max |I.lo| |I.hi|) ≤ I.lo := by
    calc -(max |I.lo| |I.hi|) ≤ -|I.lo| := neg_le_neg (le_max_left _ _)
      _ ≤ I.lo := neg_abs_le _
  have hhi : I.hi ≤ max |I.lo| |I.hi| := le_trans (le_abs_self _) (le_max_right _ _)
  rw [abs_le]
  constructor
  · calc (-(max |I.lo| |I.hi| : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast hlo
      _ ≤ x := hx.1
  · calc x ≤ I.hi := hx.2
      _ ≤ max |I.lo| |I.hi| := by exact_mod_cast hhi

/-- If |x| ≤ R for nonnegative R, then x ∈ [-R, R].
    This is the key micro-lemma for embedding Lagrange remainder bounds into intervals. -/
theorem abs_le_mem_symmetric_interval {x : ℝ} {R : ℚ} (hR : 0 ≤ R) (h : |x| ≤ R) :
    x ∈ (⟨-R, R, by linarith⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  constructor
  · have := neg_abs_le x; linarith
  · exact le_trans (le_abs_self x) h

/-- Domain setup for Taylor theorem: if |x| ≤ r for nonnegative r,
    then x ∈ [-r, r] as an Icc with the required inequalities. -/
theorem domain_from_abs_bound {x : ℝ} {r : ℚ} (_hr : 0 ≤ r) (habs : |x| ≤ r) :
    x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) := by
  simp only [Set.mem_Icc, Rat.cast_neg]
  exact abs_le.mp habs

/-- Combined domain setup from interval membership. -/
theorem domain_from_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    let r := maxAbs I
    (0 : ℝ) ≤ r ∧ |x| ≤ r ∧ x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) ∧
    ((-r : ℚ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ (r : ℚ) ∧ ((-r : ℚ) : ℝ) ≤ r := by
  have hr_nonneg : 0 ≤ maxAbs I := le_max_of_le_left (abs_nonneg I.lo)
  have habs_x := abs_le_maxAbs hx
  have hr_nonneg_real : (0 : ℝ) ≤ maxAbs I := by exact_mod_cast hr_nonneg
  have hdom := domain_from_abs_bound hr_nonneg habs_x
  refine ⟨hr_nonneg_real, habs_x, hdom, ?_, hr_nonneg_real, ?_⟩
  · simp only [Rat.cast_neg]; linarith
  · simp only [Rat.cast_neg]; linarith

/-- Convert an absolute value bound |v| ≤ R to interval membership v ∈ [-R, R].
    This is the key micro-lemma for the final step of Taylor remainder bounds. -/
theorem remainder_to_interval {v : ℝ} {R : ℚ} (hbound : |v| ≤ R) :
    v ∈ (⟨-R, R, by
      have h1 : 0 ≤ |v| := abs_nonneg v
      have h2 : (0 : ℝ) ≤ (R : ℚ) := le_trans h1 hbound
      linarith [Rat.cast_nonneg.mp h2]⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  exact abs_le.mp hbound

/-- Key lemma: exp(ξ) ≤ 3^(⌈r⌉+1) for |ξ| ≤ r -/
theorem exp_bound_by_pow3 {r : ℚ} (_hr : 0 ≤ r) {ξ : ℝ} (hξ : |ξ| ≤ r) :
    Real.exp ξ ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
  -- e < 3, using Real.exp_one_lt_d9 which gives exp(1) < 2.7182818286
  have h3 : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9  -- exp(1) < 2.7182818286
    have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
    exact lt_trans h h2
  have hceil : (r : ℝ) ≤ Nat.ceil r := by
    have h : r ≤ (Nat.ceil r : ℚ) := Nat.le_ceil r
    exact_mod_cast h
  calc Real.exp ξ ≤ Real.exp |ξ| := Real.exp_le_exp.mpr (le_abs_self ξ)
    _ ≤ Real.exp r := Real.exp_le_exp.mpr hξ
    _ ≤ Real.exp (Nat.ceil r) := Real.exp_le_exp.mpr hceil
    _ = Real.exp 1 ^ (Nat.ceil r) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 3 ^ (Nat.ceil r) := by
        rcases Nat.eq_zero_or_pos (Nat.ceil r) with hr0 | hrpos
        · simp [hr0]
        · exact le_of_lt (pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (Nat.pos_iff_ne_zero.mp hrpos))
    _ ≤ 3 ^ (Nat.ceil r + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)

/-! ### Coefficient matching lemmas -/

/-- For exp, all iterated derivatives at 0 equal 1. -/
lemma iteratedDeriv_exp_zero (i : ℕ) : iteratedDeriv i Real.exp 0 = 1 := by
  simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-! ### Helper lemmas for Taylor series membership -/

/-- Polynomial sum starting at exponent `n`. -/
private def polySumFrom (coeffs : List ℚ) (x : ℝ) (n : ℕ) : ℝ :=
  ((coeffs.zipIdx n).map (fun (c, i) => (c : ℝ) * x ^ i)).sum

/-- Horner polynomial evaluation: the real value computed by Horner's method.
    `hornerVal [c₀, c₁, c₂] x = c₀ + x * (c₁ + x * (c₂ + x * 0)) = c₀ + c₁*x + c₂*x²` -/
private def hornerVal (coeffs : List ℚ) (x : ℝ) : ℝ :=
  coeffs.foldr (fun c acc => (c : ℝ) + x * acc) 0

/-- hornerVal equals polySumFrom at any starting index n, scaled by x^n.
    Specifically: x^n * hornerVal coeffs x = polySumFrom coeffs x n -/
private lemma hornerVal_mul_pow_eq_polySumFrom (coeffs : List ℚ) (x : ℝ) (n : ℕ) :
    x ^ n * hornerVal coeffs x = polySumFrom coeffs x n := by
  induction coeffs generalizing n with
  | nil => simp [hornerVal, polySumFrom]
  | cons c cs ih =>
    have hstep : hornerVal (c :: cs) x = (c : ℝ) + x * hornerVal cs x := by
      simp [hornerVal]
    have hunfold : polySumFrom (c :: cs) x n =
        (c : ℝ) * x ^ n + polySumFrom cs x (n + 1) := by
      simp [polySumFrom, List.zipIdx_cons]
    rw [hstep, mul_add, hunfold, ← ih (n + 1)]
    ring

/-- hornerVal equals polySumFrom at index 0. -/
private lemma hornerVal_eq_polySumFrom (coeffs : List ℚ) (x : ℝ) :
    hornerVal coeffs x = polySumFrom coeffs x 0 := by
  rw [← hornerVal_mul_pow_eq_polySumFrom coeffs x 0]
  simp

/-- Auxiliary lemma for Horner-style evaluation: the foldr contains hornerVal. -/
private lemma mem_horner_foldr {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (coeffs : List ℚ) :
    hornerVal coeffs x ∈
      coeffs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0) := by
  induction coeffs with
  | nil =>
      simp [hornerVal, mem_def, singleton]
  | cons c cs ih =>
      -- hornerVal (c :: cs) x = ↑c + x * hornerVal cs x
      -- foldr ... (c :: cs) = add (singleton c) (mul (foldr ... cs) I)
      change (c : ℝ) + x * hornerVal cs x ∈
        add (singleton c) (mul (cs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton
          0)) I)
      have hc : (c : ℝ) ∈ singleton c := by simp [mem_def, singleton]
      have hmul : hornerVal cs x * x ∈
        mul (cs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0)) I :=
        mem_mul ih hx
      have : (c : ℝ) + x * hornerVal cs x = (c : ℝ) + hornerVal cs x * x := by ring
      rw [this]
      exact mem_add hc hmul

/-- General FTIA for evalTaylorSeries (Horner version): if coeffs has length n+1, then
    ∑_{i=0}^{n} coeffs[i] * x^i ∈ evalTaylorSeries coeffs I for x ∈ I. -/
theorem mem_evalTaylorSeries {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (coeffs : List ℚ) :
    (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈ evalTaylorSeries coeffs I := by
  have hmem := mem_horner_foldr hx coeffs
  rw [hornerVal_eq_polySumFrom] at hmem
  simp only [evalTaylorSeries, polySumFrom] at *
  exact hmem

/-- Helper: (List.range n).map f).sum = ∑ i ∈ Finset.range n, f i -/
private lemma list_map_sum_eq_finset_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ]
    rw [ih, add_comm]

/-- Helper: zipIdx of List.range just pairs each element with its index (which is itself) -/
private lemma zipIdx_range_map {α : Type*} (f : ℕ → ℕ → α) (n : ℕ) :
    (List.range n).zipIdx.map (fun p => f p.1 p.2) = (List.range n).map (fun i => f i i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.zipIdx_append, List.map_append, List.length_range]
    rw [ih]
    simp only [List.zipIdx_singleton, List.map_singleton, zero_add]

/-- The exp Taylor polynomial value matches our evalTaylorSeries.
    The proof shows that our list-based polynomial evaluation produces the same
    sum as the Finset.sum form used in Mathlib's Taylor theorem. -/
theorem mem_evalTaylorSeries_exp {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i ∈
      evalTaylorSeries (expTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (expTaylorCoeffs n)
  have hmem' :
      (((List.range (n + 1)).map (fun i => 1 / ratFactorial i)).zipIdx.map
          (fun p => (p.1 : ℝ) * x ^ p.2)).sum ∈
        evalTaylorSeries (expTaylorCoeffs n) I := by
    simpa [expTaylorCoeffs_eq_range_map] using hmem
  convert hmem' using 1
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (1 / i.factorial : ℝ) * x ^ i) (n + 1)]
  -- The two list maps are equal: both compute [1/0! * x^0, 1/1! * x^1, ...]
  -- LHS: (List.range (n+1)).map (fun i => 1/i! * x^i)
  -- RHS: zipIdx.map with Prod.map composition
  -- For List.range, zipIdx gives [(0,0), (1,1), ...], so they match
  congr 1
  symm
  -- The RHS has type (ℚ × ℕ) from Prod.map applied to zipIdx pairs
  -- Step 1: Simplify the composition
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map (fun i => (1 : ℚ) / ratFactorial i) id) =
      (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / ratFactorial p.1 : ℝ) * x ^
        p.2) := by
    apply List.map_congr_left
    intro ⟨a, b⟩ _
    simp only [Function.comp_apply, Prod.map_apply, id_eq, Rat.cast_div, Rat.cast_one]
  -- Step 2: Use zipIdx_range_map to eliminate zipIdx
  have h2 : (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / ratFactorial p.1 : ℝ) * x
    ^ p.2) =
      (List.range (n + 1)).map (fun i => ((1 : ℚ) / ratFactorial i : ℝ) * x ^ i) := by
    convert! zipIdx_range_map (fun a b => ((1 : ℚ) / ratFactorial a : ℝ) * x ^ b) (n + 1) using 2
  -- Step 3: Simplify the casts
  have h3 : (List.range (n + 1)).map (fun i => ((1 : ℚ) / ratFactorial i : ℝ) * x ^ i) =
      (List.range (n + 1)).map (fun i => (1 / i.factorial : ℝ) * x ^ i) := by
    apply List.map_congr_left
    intro i _
    simp [ratFactorial]
  rw [h1, h2, h3]

/-- The iterated derivative of sin is sin, cos, -sin, -cos in a cycle of 4. -/
private lemma iteratedDeriv_sin (n : ℕ) : iteratedDeriv n Real.sin =
    if n % 4 = 0 then Real.sin
    else if n % 4 = 1 then Real.cos
    else if n % 4 = 2 then fun x => -Real.sin x
    else fun x => -Real.cos x := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv sin = cos
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte, Real.deriv_sin]; norm_num
    · -- n % 4 = 1: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of sin at 0 follows the pattern 0, 1, 0, -1, 0, 1, 0, -1, ... -/
private lemma iteratedDeriv_sin_zero (i : ℕ) : iteratedDeriv i Real.sin 0 =
    if i % 4 = 0 then 0
    else if i % 4 = 1 then 1
    else if i % 4 = 2 then 0
    else -1 := by
  rw [iteratedDeriv_sin]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.sin_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h3]; norm_num [Real.cos_zero]

/-- The sin Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i sin 0 = 0, 1, 0, -1, 0, 1, ... matches sinTaylorCoeffs. -/
theorem mem_evalTaylorSeries_sin {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (sinTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (sinTaylorCoeffs n)
  convert hmem using 1
  simp only [sinTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i)
    (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert! zipIdx_range_map
      (fun a b => ((if a % 2 = 1 then (-1 : ℚ) ^ ((a - 1) / 2) / a.factorial else 0 : ℚ) : ℝ) * x
        ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  -- Need: (iteratedDeriv i sin 0 / i!) * x^i = ((sinCoeff i) : ℝ) * x^i
  -- where sinCoeff i = if i % 2 = 1 then (-1)^((i-1)/2) / i! else 0
  congr 1
  -- Show iteratedDeriv i sin 0 / i! = sinCoeff i (as ℝ)
  rw [iteratedDeriv_sin_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h0, ↓reduceIte, zero_div, ite_eq_right hi_ne, Rat.cast_zero]
  · -- i % 4 = 1: i is odd, iteratedDeriv = 1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h1, ↓reduceIte, ite_eq_left hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    congr 1
    have heven : Even ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    exact heven.neg_one_pow
  · -- i % 4 = 2: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h2, ↓reduceIte, ite_eq_right hi_ne]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = -1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h3, ite_eq_left hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num

/-- The iterated derivative of cos is cos, -sin, -cos, sin in a cycle of 4. -/
private lemma iteratedDeriv_cos (n : ℕ) : iteratedDeriv n Real.cos =
    if n % 4 = 0 then Real.cos
    else if n % 4 = 1 then fun x => -Real.sin x
    else if n % 4 = 2 then fun x => -Real.cos x
    else Real.sin := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 1: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv sin = cos
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of cos at 0 follows the pattern 1, 0, -1, 0, 1, 0, ... -/
private lemma iteratedDeriv_cos_zero (i : ℕ) : iteratedDeriv i Real.cos 0 =
    if i % 4 = 0 then 1
    else if i % 4 = 1 then 0
    else if i % 4 = 2 then -1
    else 0 := by
  rw [iteratedDeriv_cos]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.cos_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h3]; norm_num [Real.sin_zero]

/-- The cos Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i cos 0 = 1, 0, -1, 0, 1, 0, ... matches cosTaylorCoeffs. -/
theorem mem_evalTaylorSeries_cos {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (cosTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (cosTaylorCoeffs n)
  convert hmem using 1
  simp only [cosTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i)
    (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert! zipIdx_range_map
      (fun a b => ((if a % 2 = 0 then (-1 : ℚ) ^ (a / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  congr 1
  -- Show iteratedDeriv i cos 0 / i! = cosCoeff i (as ℝ)
  rw [iteratedDeriv_cos_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h0, ↓reduceIte, one_div, ite_eq_left hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have heven : Even (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [heven.neg_one_pow]
    ring
  · -- i % 4 = 1: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h1, ↓reduceIte, ite_eq_right hi_ne]
    norm_num
  · -- i % 4 = 2: i is even, iteratedDeriv = -1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h2, ite_eq_left hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h3, ite_eq_right hi_ne]
    norm_num

/-! ### Taylor remainder micro-lemmas -/

/-- Unified Taylor remainder bound for exp: given x ∈ I with r = maxAbs I,
    the Taylor remainder |exp x - poly(x)| ≤ 3^(⌈r⌉+1) * r^(n+1) / (n+1)!.
    This encapsulates the domain setup and remainder calculation. -/
theorem exp_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
    ∈ expRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := ((3 : ℚ) ^ (Nat.ceil r + 1) * r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem
  have hexp_smooth : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.exp y‖ ≤ Real.exp r := by
    intro y hy
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos
      y)]
    exact Real.exp_le_exp.mpr hy.2
  have hTaylor := taylor_remainder_bound hab h0a h0b hexp_smooth hderiv_bound
    (Real.exp_pos (r : ℚ)).le x hdom
  -- Compute remainder bound
  have hr_nonneg_rat : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
  have hexp_r_bound : Real.exp (r : ℚ) ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
    apply exp_bound_by_pow3 hr_nonneg_rat
    rw [abs_of_nonneg hr_nonneg]
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : Real.exp (r : ℚ) * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero]
    calc Real.exp (r : ℚ) * |x| ^ (n + 1) / (n + 1).factorial
        ≤ (3 : ℝ) ^ (Nat.ceil r + 1) * (r : ℝ) ^ (n + 1) / (n + 1).factorial := by
          apply div_le_div_of_nonneg_right _ hfact_pos.le
          apply mul_le_mul hexp_r_bound hx_pow_bound (pow_nonneg (abs_nonneg x) _)
          apply pow_nonneg; norm_num
      _ = (R : ℝ) := by
          simp only [R, ratFactorial, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
            Rat.cast_natCast, Rat.cast_ofNat]
  -- Convert to interval membership
  simp only [expRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.exp x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for sin: given x ∈ I with r = maxAbs I,
    the Taylor remainder |sin x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |sin^(k)(x)| ≤ 1 for all k, x. -/
theorem sin_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
    ∈ sinRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem with M = 1
  have hsin_smooth : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.sin y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).1
  have hTaylor := taylor_remainder_bound hab h0a h0b hsin_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom
  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  -- Convert to interval membership
  simp only [sinRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.sin x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for cos: given x ∈ I with r = maxAbs I,
    the Taylor remainder |cos x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |cos^(k)(x)| ≤ 1 for all k, x. -/
theorem cos_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
    ∈ cosRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem with M = 1
  have hcos_smooth : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.cos y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).2
  have hTaylor := taylor_remainder_bound hab h0a h0b hcos_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom
  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  -- Convert to interval membership
  simp only [cosRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.cos x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-! ### FTIA for computable functions -/

private theorem mem_expPointComputableRaw (q : ℚ) (n : ℕ) :
    Real.exp q ∈ expPointComputableRaw q n := by
  simp only [expPointComputableRaw]
  have hq_mem : (q : ℝ) ∈ singleton q := mem_singleton q
  -- Strategy: exp q = poly(q) + remainder, with both in their respective intervals
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q :
    ℝ) ^ i
      ∈ evalTaylorSeries (expTaylorCoeffs n) (singleton q) := by
    have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q :
      ℝ) ^ i =
        ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * (q : ℝ) ^ i := by
      apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
    rw [hsum_eq]; exact mem_evalTaylorSeries_exp hq_mem n
  have hrem_mem := exp_taylor_remainder_in_interval hq_mem n
  have heq : Real.exp q = (∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) +
      (Real.exp q - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) := by ring
  rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for single-point exp: Real.exp q ∈ expPointComputable q n -/
theorem mem_expPointComputable (q : ℚ) (n : ℕ) :
    Real.exp q ∈ expPointComputable q n := by
  simp only [expPointComputable]
  set k := expReduceK q
  set m : ℕ := (2:ℕ)^k
  set q' : ℚ := q / m
  have hbase : Real.exp q' ∈ expPointComputableRaw q' n :=
    mem_expPointComputableRaw q' n
  have hpow : (Real.exp q') ^ m ∈ pow (expPointComputableRaw q' n) m :=
    mem_pow hbase m
  have hm : (m:ℝ) ≠ 0 := by
    -- m = 2^k > 0
    exact_mod_cast (pow_ne_zero k (by decide : (2:ℕ) ≠ 0))
  have hq : (q : ℝ) = (m:ℝ) * (q' : ℝ) := by
    -- q' = q / m
    have hm' : (m:ℝ) ≠ 0 := hm
    calc
      (q:ℝ) = (m:ℝ) * ((q:ℝ) / (m:ℝ)) := by
        field_simp [hm']
      _ = (m:ℝ) * (q' : ℝ) := by
        simp [q', Rat.cast_div, Rat.cast_natCast]
  have hexp : Real.exp q = (Real.exp q') ^ m := by
    calc
      Real.exp q = Real.exp ((m:ℝ) * (q' : ℝ)) := by simp [hq]
      _ = (Real.exp (q' : ℝ)) ^ m := by
            -- exp (m * q') = (exp q')^m
            simpa [mul_comm] using (Real.exp_nat_mul (q' : ℝ) m)
  -- rewrite and apply membership
  simpa [hexp]

theorem mem_expComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x ∈ expComputable I n := by
  simp only [expComputable]
  split_ifs with h
  · -- Interval doesn't cross 0: use endpoint evaluation and monotonicity
    -- exp is monotone increasing, so exp([lo, hi]) ⊆ hull(exp(lo), exp(hi))
    have hlo_mem := mem_expPointComputable I.lo n
    have hhi_mem := mem_expPointComputable I.hi n
    -- Since x ∈ [lo, hi] and exp is monotone, exp(x) ∈ [exp(lo), exp(hi)]
    -- The hull contains both exp(lo) and exp(hi), so it contains exp(x)
    rcases h with ⟨hhi_neg⟩ | ⟨hlo_pos⟩
    · -- Case: hi ≤ 0 (negative interval)
      -- exp(lo) ≤ exp(x) ≤ exp(hi) by monotonicity
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      -- exp(x) is between exp(lo) and exp(hi), both of which are in the hull
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · -- lower bound: min(expLo.lo, expHi.lo) ≤ exp(x)
        calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · -- upper bound: exp(x) ≤ max(expLo.hi, expHi.hi)
        calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) :=
            le_max_right _ _
    · -- Case: 0 ≤ lo (positive interval) - same argument
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) :=
            le_max_right _ _
  · -- Interval crosses 0: use standard Taylor
    -- Strategy: exp x = poly(x) + remainder, with both in their respective intervals
    have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
        ∈ evalTaylorSeries (expTaylorCoeffs n) I := by
      have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^
        i =
          ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
      rw [hsum_eq]; exact mem_evalTaylorSeries_exp hx n
    have hrem_mem := exp_taylor_remainder_in_interval hx n
    have heq : Real.exp x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) +
        (Real.exp x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for sinComputable: Real.sin x ∈ sinComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound sin ∈ [-1, 1]. -/
theorem mem_sinComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x ∈ sinComputable I n := by
  simp only [sinComputable]
  -- Strategy: sin x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (sinTaylorCoeffs n) I := mem_evalTaylorSeries_sin hx n
  -- Remainder part ∈ sinRemainderBoundComputable (via micro-lemma)
  have hrem_mem := sin_taylor_remainder_in_interval hx n
  -- Raw interval membership: sin x ∈ poly + remainder
  have hraw_mem : Real.sin x ∈ add (evalTaylorSeries (sinTaylorCoeffs n) I)
      (sinRemainderBoundComputable I n) := by
    have heq : Real.sin x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) +
        (Real.sin x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem
  -- Global bound: sin x ∈ [-1, 1]
  have hglobal_mem : Real.sin x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_sin x
    · simp only [Rat.cast_one]; exact Real.sin_le_one x
  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for cosComputable: Real.cos x ∈ cosComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound cos ∈ [-1, 1]. -/
theorem mem_cosComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x ∈ cosComputable I n := by
  simp only [cosComputable]
  -- Strategy: cos x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (cosTaylorCoeffs n) I := mem_evalTaylorSeries_cos hx n
  -- Remainder part ∈ cosRemainderBoundComputable (via micro-lemma)
  have hrem_mem := cos_taylor_remainder_in_interval hx n
  -- Raw interval membership: cos x ∈ poly + remainder
  have hraw_mem : Real.cos x ∈ add (evalTaylorSeries (cosTaylorCoeffs n) I)
      (cosRemainderBoundComputable I n) := by
    have heq : Real.cos x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) +
        (Real.cos x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem
  -- Global bound: cos x ∈ [-1, 1]
  have hglobal_mem : Real.cos x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_cos x
    · simp only [Rat.cast_one]; exact Real.cos_le_one x
  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for sinhPointComputable: Real.sinh q ∈ sinhPointComputable q n -/
theorem mem_sinhPointComputable (q : ℚ) (n : ℕ) :
    Real.sinh q ∈ sinhPointComputable q n := by
  simp only [sinhPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.sinh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  split_ifs with h
  · constructor <;> { simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]; linarith }
  · -- Fallback case: use min/max bounds
    constructor
    · simp only [Rat.cast_min, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply min_le_of_left_le; linarith
    · simp only [Rat.cast_max, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply le_max_of_le_right; linarith

/-- FTIA for coshPointComputable: Real.cosh q ∈ coshPointComputable q n -/
theorem mem_coshPointComputable (q : ℚ) (n : ℕ) :
    Real.cosh q ∈ coshPointComputable q n := by
  simp only [coshPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.cosh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  -- cosh q ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ (Real.exp q + Real.exp (-(q : ℝ))) / 2 := by
    have h1 : Real.exp q > 0 := Real.exp_pos q
    have h2 : Real.exp (-(q : ℝ)) > 0 := Real.exp_pos (-(q : ℝ))
    have hprod : Real.exp q * Real.exp (-(q : ℝ)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have ham : Real.exp q + Real.exp (-(q : ℝ)) ≥ 2 := by nlinarith [sq_nonneg (Real.exp q -
      Real.exp (-(q : ℝ))), hprod]
    linarith
  split_ifs with h
  · constructor
    · -- Lower bound: max 1 coshLo ≤ cosh q
      simp only [Rat.cast_max, Rat.cast_one, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      apply max_le
      · exact hcosh_ge_one
      · linarith
    · -- Upper bound
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      linarith
  · -- Fallback
    constructor
    · simp only [Rat.cast_one]
      exact hcosh_ge_one
    · simp only [Rat.cast_max, Rat.cast_ofNat, Rat.cast_div, Rat.cast_add]
      apply le_max_of_le_right
      linarith

/-- FTIA for sinhComputable: Real.sinh x ∈ sinhComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity of sinh. -/
theorem mem_sinhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sinh x ∈ sinhComputable I n := by
  simp only [sinhComputable]
  -- sinh is strictly monotone increasing
  have hsinh_mono : StrictMono Real.sinh := Real.sinh_strictMono
  have hlo_mem := mem_sinhPointComputable I.lo n
  have hhi_mem := mem_sinhPointComputable I.hi n
  -- x ∈ [lo, hi] implies sinh(lo) ≤ sinh(x) ≤ sinh(hi)
  have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
  have hx_le_hi : x ≤ (I.hi : ℝ) := hx.2
  have hsinh_lo_le : Real.sinh I.lo ≤ Real.sinh x :=
    hsinh_mono.monotone hlo_le_x
  have hsinh_x_le_hi : Real.sinh x ≤ Real.sinh I.hi :=
    hsinh_mono.monotone hx_le_hi
  -- sinh x is between sinh(lo) and sinh(hi), which are in the hull
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (sinhPointComputable I.lo n).lo (sinhPointComputable I.hi n).lo : ℝ)
        ≤ (sinhPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.sinh I.lo := hlo_mem.1
      _ ≤ Real.sinh x := hsinh_lo_le
  · calc Real.sinh x ≤ Real.sinh I.hi := hsinh_x_le_hi
      _ ≤ (sinhPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((sinhPointComputable I.lo n).hi : ℝ) ((sinhPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

/-- FTIA for coshComputable: Real.cosh x ∈ coshComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity properties of cosh. -/
theorem mem_coshComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cosh x ∈ coshComputable I n := by
  simp only [coshComputable]
  have hlo_mem := mem_coshPointComputable I.lo n
  have hhi_mem := mem_coshPointComputable I.hi n
  -- cosh x ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ Real.cosh x := Real.one_le_cosh x
  -- Key lemma: cosh a ≤ cosh b iff |a| ≤ |b|
  split_ifs with h1 h2
  · -- Case: 0 ≤ I.lo (non-negative interval, cosh is increasing)
    have hlo_nonneg : (0 : ℝ) ≤ I.lo := by exact_mod_cast h1
    have hx_nonneg : 0 ≤ x := le_trans hlo_nonneg hx.1
    have hhi_nonneg : (0 : ℝ) ≤ I.hi := le_trans hlo_nonneg (by exact_mod_cast I.le)
    -- For 0 ≤ a ≤ b: |a| = a ≤ b = |b|, so cosh(a) ≤ cosh(b)
    have hcosh_lo_le : Real.cosh I.lo ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hlo_nonneg, abs_of_nonneg hx_nonneg]
      exact hx.1
    have hcosh_x_le_hi : Real.cosh x ≤ Real.cosh I.hi := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hhi_nonneg]
      exact hx.2
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo : ℝ)
          ≤ (coshPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.lo := hlo_mem.1
        _ ≤ Real.cosh x := hcosh_lo_le
    · calc Real.cosh x ≤ Real.cosh I.hi := hcosh_x_le_hi
        _ ≤ (coshPointComputable I.hi n).hi := hhi_mem.2
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) :=
          le_max_right _ _
  · -- Case: I.hi ≤ 0 (non-positive interval, cosh is decreasing)
    have hhi_nonpos : I.hi ≤ (0 : ℝ) := by exact_mod_cast h2
    have hx_nonpos : x ≤ 0 := le_trans hx.2 hhi_nonpos
    have hlo_nonpos : (I.lo : ℝ) ≤ 0 := le_trans (by exact_mod_cast I.le) hhi_nonpos
    -- For a ≤ b ≤ 0: |a| = -a ≥ -b = |b|, so cosh(a) ≥ cosh(b)
    have hcosh_hi_le : Real.cosh I.hi ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hhi_nonpos, abs_of_nonpos hx_nonpos]
      linarith [hx.2]
    have hcosh_x_le_lo : Real.cosh x ≤ Real.cosh I.lo := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hlo_nonpos]
      linarith [hx.1]
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.hi n).lo (coshPointComputable I.lo n).lo : ℝ)
          ≤ (coshPointComputable I.hi n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.hi := hhi_mem.1
        _ ≤ Real.cosh x := hcosh_hi_le
    · calc Real.cosh x ≤ Real.cosh I.lo := hcosh_x_le_lo
        _ ≤ (coshPointComputable I.lo n).hi := hlo_mem.2
        _ ≤ max ((coshPointComputable I.hi n).hi : ℝ) ((coshPointComputable I.lo n).hi : ℝ) :=
          le_max_right _ _
  · -- Case: interval contains 0, minimum is 1
    simp only [mem_def, Rat.cast_one, hull, Rat.cast_max]
    constructor
    · exact hcosh_ge_one
    · -- Upper bound is max of endpoint cosh values
      push Not at h1 h2
      have hhi_pos : (0 : ℝ) < I.hi := by exact_mod_cast h2
      have hlo_neg : (I.lo : ℝ) < 0 := by exact_mod_cast h1
      have hmax_bound : Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := by
        -- x is between lo and hi, and interval contains 0
        by_cases! hx_nonneg : 0 ≤ x
        · -- x ≥ 0: cosh(x) ≤ cosh(hi) since 0 ≤ x ≤ hi means |x| ≤ |hi|
          apply le_max_of_le_right
          rw [Real.cosh_le_cosh]
          rw [abs_of_nonneg hx_nonneg, abs_of_nonneg (le_of_lt hhi_pos)]
          exact hx.2
        · -- x < 0: cosh(x) ≤ cosh(lo) since lo ≤ x < 0 means |x| ≤ |lo|
          apply le_max_of_le_left
          rw [Real.cosh_le_cosh]
          rw [abs_of_neg hx_nonneg, abs_of_neg hlo_neg]
          linarith [hx.1]
      calc Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := hmax_bound
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) := by
            apply max_le_max
            · exact hlo_mem.2
            · exact hhi_mem.2

/-! ### Computable atanh via Taylor series

For |y| < 1, atanh(y) = y + y³/3 + y⁵/5 + ...
We compute this series for y ∈ [-1/3, 1/3] where it converges rapidly.
-/

/-- Taylor coefficients for atanh: 0, 1, 0, 1/3, 0, 1/5, ...
    atanh(y) = Σ y^(2k+1)/(2k+1) = y + y³/3 + y⁵/5 + ... -/
def atanhTaylorCoeffs (n : ℕ) : List ℚ :=
  let f : ℕ → ℚ := fun i => if i % 2 = 1 then 1 / i else 0
  (List.range (n + 1)).map f

/-- Computable atanh remainder bound.
    For |y| ≤ r < 1, the remainder after n terms is bounded by r^(n+1)/(1 - r²).
    We use a conservative bound: r^(n+1) / ((n+1) * (1 - r)) for simplicity. -/
def atanhRemainderBoundComputable (r : ℚ) (n : ℕ) : IntervalRat :=
  let r' := |r|  -- Use absolute value to ensure non-negativity
  if h : r' ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for bad input
  else
    let R := r' ^ (n + 1) / (1 - r')
    ⟨-R, R, by
      have hr : r' < 1 := not_le.mp h
      have hr_nonneg : 0 ≤ r' := abs_nonneg r
      have hdenom_pos : 0 < 1 - r' := by linarith
      have hR_nonneg : 0 ≤ R := by
        apply div_nonneg
        · apply pow_nonneg hr_nonneg
        · linarith
      linarith⟩

/-- Computable interval enclosure for atanh at a single rational point.
    Requires |q| < 1 for convergence. For |q| ≤ 1/3, this is very accurate. -/
def atanhPointComputable (q : ℚ) (n : ℕ := 15) : IntervalRat :=
  let r := |q|
  if r ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback
  else
    let I := singleton q
    let coeffs := atanhTaylorCoeffs n
    let polyVal := evalTaylorSeries coeffs I
    let remainder := atanhRemainderBoundComputable r n
    add polyVal remainder

/-- Point `atanh` using Taylor coefficients prepared for depth `n`. -/
def atanhPointComputableWithCoeffs (q : ℚ) (n : ℕ)
    (coeffs : List ℚ) : IntervalRat :=
  let r := |q|
  if r ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let I := singleton q
    let polyVal := evalTaylorSeries coeffs I
    let remainder := atanhRemainderBoundComputable r n
    add polyVal remainder

theorem atanhPointComputableWithCoeffs_eq (q : ℚ) (n : ℕ) :
    atanhPointComputableWithCoeffs q n (atanhTaylorCoeffs n) =
      atanhPointComputable q n := by
  simp [atanhPointComputableWithCoeffs, atanhPointComputable]

/-- The atanh series: atanh(x) = Σ_{k=0}^∞ x^(2k+1)/(2k+1) for |x| < 1.
    Derived from Mathlib's hasSum_log_sub_log_of_abs_lt_one. -/
theorem Real.atanh_hasSum' {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / (2 * k + 1)) (Real.atanh x) := by
  have hlog := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have h1 : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have h2 : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have h_eq : Real.atanh x = (1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) := by
    rw [Real.atanh, Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
  rw [h_eq]
  convert! hlog.mul_left (1 / 2) using 1
  funext k
  field_simp

/-- The atanh Taylor polynomial membership: the partial sum of atanh coefficients at q
    is in evalTaylorSeries (atanhTaylorCoeffs n) (singleton q). -/
theorem mem_evalTaylorSeries_atanh {q : ℚ} (n : ℕ) :
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum ∈
      evalTaylorSeries (atanhTaylorCoeffs n) (singleton q) :=
  mem_evalTaylorSeries (mem_singleton q) (atanhTaylorCoeffs n)

/-- The atanh Taylor remainder bound: for |q| < 1, the remainder after n terms is bounded.
    The remainder is |Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)| ≤ |q|^(n+1)/(1-|q|). -/
private theorem atanhTaylorCoeffs_sum (q : ℚ) (n : ℕ) :
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) ↦ (c : ℝ) * (q : ℝ) ^ i)).sum =
      ∑ k ∈ Finset.range ((n + 1) / 2), (q : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  let term := fun k : ℕ ↦ (q : ℝ) ^ (2 * k + 1) / (2 * k + 1)
  let m := (n + 1) / 2
  -- Step 1: Convert the list sum to a Finset sum over indices.
  have hlist :
      ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum =
      ∑ i ∈ Finset.range (n + 1),
        ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i := by
    simp only [atanhTaylorCoeffs, one_div]
    rw [List.zipIdx_map]
    simp only [List.map_map]
    -- Simplify the composition after zipIdx_map.
    have h1 :
        (List.range (n + 1)).zipIdx.map
            ((fun p : ℚ × ℕ => (p.1 : ℝ) * (q : ℝ) ^ p.2) ∘
              Prod.map (fun i : ℕ => if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0) id) =
          (List.range (n + 1)).zipIdx.map
            (fun p : ℕ × ℕ =>
              ((if p.1 % 2 = 1 then ((p.1 : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ p.2) := by
      apply List.map_congr_left
      intro ⟨a, b⟩ _
      simp [Function.comp, Prod.map_apply]
    -- Replace zipIdx over range with a direct map on indices.
    have h2 :
        (List.range (n + 1)).zipIdx.map
            (fun p : ℕ × ℕ =>
              ((if p.1 % 2 = 1 then ((p.1 : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ p.2) =
          (List.range (n + 1)).map
            (fun i : ℕ =>
              ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i) := by
      convert! zipIdx_range_map
        (fun a b =>
          ((if a % 2 = 1 then ((a : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ b) (n + 1) using 2
    rw [h1, h2]
    exact list_map_sum_eq_finset_sum
      (fun i : ℕ =>
        ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i) (n + 1)
  -- Step 2: Filter to odd indices (even indices contribute zero).
  have hsum_filter :
      ∑ i ∈ Finset.range (n + 1),
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i =
        ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i := by
    have hterm :
        ∀ i : ℕ,
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i =
            if i % 2 = 1 then (q : ℝ) ^ i / i else 0 := by
      intro i
      by_cases hodd : i % 2 = 1
      · simp [hodd, div_eq_mul_inv, Rat.cast_inv, Rat.cast_natCast,
          mul_comm]
      · simp [hodd]
    calc
      ∑ i ∈ Finset.range (n + 1),
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i
          =
          ∑ i ∈ Finset.range (n + 1),
            (if i % 2 = 1 then (q : ℝ) ^ i / i else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hterm i
      _ =
          ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
            (q : ℝ) ^ i / i := by
              symm
              exact (Finset.sum_filter
                (s := Finset.range (n + 1))
                (f := fun i => (q : ℝ) ^ i / i)
                (p := fun i => i % 2 = 1))
  -- Step 3: Reindex odd indices by k with i = 2k+1.
  have hsum_reindex :
      ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i =
        ∑ k ∈ Finset.range m, term k := by
    refine (Finset.sum_nbij
      (s := Finset.range m)
      (t := (Finset.range (n + 1)).filter (fun i => i % 2 = 1))
      (i := fun k => 2 * k + 1)
      (f := term)
      (g := fun i => (q : ℝ) ^ i / i)
      ?_ ?_ ?_ ?_).symm
    · intro k hk
      apply Finset.mem_filter.2
      constructor
      · -- membership in range
        have hk' : k < m := Finset.mem_range.1 hk
        have hk_succ : Nat.succ k ≤ m := (Nat.succ_le_iff).2 hk'
        have hk_succ' : k + 1 ≤ (n + 1) / 2 := by simpa [m] using hk_succ
        have hk_mul : (k + 1) * 2 ≤ n + 1 :=
          (Nat.le_div_iff_mul_le Nat.zero_lt_two).1 hk_succ'
        have hk_mul' : 2 * k + 2 ≤ n + 1 := by
          simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk_mul
        have hk_lt : 2 * k + 1 < n + 1 := by
          have hlt : 2 * k + 1 < 2 * k + 2 := Nat.lt_succ_self (2 * k + 1)
          exact lt_of_lt_of_le hlt hk_mul'
        exact Finset.mem_range.2 hk_lt
      · -- oddness
        have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
        exact (Nat.odd_iff).1 hodd
    · intro a ha b hb hEq
      have hEq' : Nat.succ (2 * a) = Nat.succ (2 * b) := by
        simpa [Nat.succ_eq_add_one] using hEq
      have hEq'' : 2 * a = 2 * b := (Nat.succ_inj).1 hEq'
      exact Nat.mul_left_cancel Nat.zero_lt_two hEq''
    · intro i hi
      simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio, m]
      use (i - 1) / 2
      simp at hi
      grind only
    · intro k hk
      simp [term]
  -- Combine the steps.
  calc
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum
        = ∑ i ∈ Finset.range (n + 1),
            ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i := hlist
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i := hsum_filter
    _ = ∑ k ∈ Finset.range m, term k := hsum_reindex


theorem atanh_taylor_remainder_in_interval {q : ℚ} (hq : |(q : ℝ)| < 1) (n : ℕ) :
    Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum
    ∈ atanhRemainderBoundComputable |q| n := by
  -- The remainder is the tail of the series
  simp only [atanhRemainderBoundComputable, abs_abs]
  have hq_abs_lt : |q| < 1 := by
    have h := abs_lt.mp hq
    rw [abs_lt]; constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have h_not_ge : ¬(|q| ≥ 1) := not_le.mpr hq_abs_lt
  simp only [h_not_ge, mem_def]
  -- The bound R = |q|^(n+1)/(1-|q|) in ℚ
  set R_rat := |q| ^ (n + 1) / (1 - |q|) with hR_rat_def
  -- Key bounds: |q| < 1 in ℚ
  have hr_nonneg_rat : 0 ≤ |q| := abs_nonneg q
  have hdenom_pos_rat : 0 < 1 - |q| := by linarith
  have hR_nonneg_rat' : 0 ≤ R_rat := by
    apply div_nonneg
    · exact pow_nonneg hr_nonneg_rat (n + 1)
    · linarith
  have hR_nonneg : (0 : ℝ) ≤ R_rat := Rat.cast_nonneg.mpr hR_nonneg_rat'
  -- The absolute value of the remainder is bounded
  have habs : |Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map
      (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum| ≤ (R_rat : ℝ) := by
    -- Strategy: The atanh series is Σ_k q^(2k+1)/(2k+1)
    -- The polynomial computes Σ_{i≤n, i odd} q^i/i
    -- The remainder is Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)
    -- Bound: |remainder| ≤ Σ_{k: 2k+1 > n} |q|^(2k+1) ≤ |q|^(n+1)/(1-|q|)

    -- Get the series representation
    have hseries := Real.atanh_hasSum' hq
    -- The polynomial sum equals the partial series sum for terms with index ≤ n
    -- atanhTaylorCoeffs n = [0, 1, 0, 1/3, 0, 1/5, ...] for indices 0..n
    -- So the sum is Σ_{i odd, i ≤ n} q^i/i = Σ_{k: 2k+1 ≤ n} q^(2k+1)/(2k+1)

    -- For the bound, we use that each term |q^(2k+1)/(2k+1)| ≤ |q|^(2k+1)
    -- and the geometric series Σ_{m≥n+1} |q|^m ≤ |q|^(n+1)/(1-|q|)

    -- This is a non-trivial series argument - for now use the bound directly
    -- The remainder terms satisfy |term_k| ≤ |q|^(2k+1) for 2k+1 > n
    -- Summing: |remainder| ≤ |q|^(n+1) * (1 + |q| + |q|² + ...) = |q|^(n+1)/(1-|q|)
    have hq_real_lt : |(q : ℝ)| < 1 := hq
    have hq_abs_nonneg : 0 ≤ |(q : ℝ)| := abs_nonneg _
    -- The remainder is bounded by a geometric series tail
    -- |Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)| ≤ Σ_{k: 2k+1 > n} |q|^(2k+1)
    --                                    ≤ |q|^(n+1) + |q|^(n+2) + ...
    --                                    = |q|^(n+1) / (1 - |q|)
    -- Define the series term and the split point m
    let term := fun k : ℕ => (q : ℝ) ^ (2 * k + 1) / (2 * k + 1)
    -- m = number of terms with 2k+1 ≤ n, i.e., k ≤ (n-1)/2
    let m := (n + 1) / 2
    -- Key: 2m ≥ n (so 2m+1 ≥ n+1)
    have hm_bound : 2 * m ≥ n := by simp only [m]; omega
    -- Step 1: Show polynomial sum equals partial series sum up to m terms
    -- The polynomial atanhTaylorCoeffs n has coefficients:
    -- index i: 1/i if i is odd and i ≤ n, else 0
    -- So the sum gives Σ_{k: 2k+1 ≤ n} q^(2k+1)/(2k+1) = Σ_{k < m} term k
    have h_poly_eq_partial := atanhTaylorCoeffs_sum q n
    -- Step 2: The remainder is the tail of the series starting at m
    have h_summable := hseries.summable
    have h_tail_summable : Summable fun k => term (k + m) := (summable_nat_add_iff m).mpr h_summable
    have h_tail_eq : Real.atanh q - ∑ k ∈ Finset.range m, term k = ∑' k, term (k + m) := by
      have h_split := h_summable.sum_add_tsum_nat_add m
      have h_tsum_eq : ∑' i, term i = Real.atanh q := hseries.tsum_eq
      linarith [h_split, h_tsum_eq]
    rw [h_poly_eq_partial, h_tail_eq]
    -- Step 3: Bound the tail by geometric series
    have hz_abs_sq : |(q : ℝ)| ^ 2 < 1 := by
      have h1 : |(q : ℝ)| ^ 2 ≤ |(q : ℝ)| := by
        have hn : 0 ≤ |(q : ℝ)| := abs_nonneg _
        have hle : |(q : ℝ)| ≤ 1 := le_of_lt hq
        nlinarith [sq_nonneg (|(q : ℝ)| - 1)]
      linarith
    have hz_abs_nonneg : 0 ≤ |(q : ℝ)| := abs_nonneg _
    have hz_abs_le : |(q : ℝ)| ≤ 1 := le_of_lt hq
    -- Define the dominating geometric term
    let geo_term := fun k : ℕ => |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k
    have h_geo_summable : Summable geo_term := by
      apply Summable.mul_left
      exact summable_geometric_of_lt_one (sq_nonneg _) hz_abs_sq
    have h_term_bound : ∀ k, |term (k + m)| ≤ geo_term k := by
      intro k
      simp only [term, geo_term]
      rw [abs_div, abs_pow]
      have h_pow_eq : |(q : ℝ)| ^ (2 * (k + m) + 1) = |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^
        k := by
        have : 2 * (k + m) + 1 = 2 * m + 1 + 2 * k := by ring
        rw [this, pow_add, pow_mul]
      rw [h_pow_eq]
      have h_denom_pos' : (0 : ℝ) < 2 * (k + m : ℕ) + 1 := by positivity
      have h_denom_ge_one : (1 : ℝ) ≤ |(2 : ℝ) * (k + m : ℕ) + 1| := by
        rw [abs_of_pos h_denom_pos']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        push_cast; linarith
      calc |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k / |(2 : ℝ) * (k + m : ℕ) + 1|
          ≤ |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k / 1 := by
            apply div_le_div_of_nonneg_left _ (by positivity) h_denom_ge_one
            positivity
        _ = |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k := by ring
    have h_norm_sum : ‖∑' k, term (k + m)‖ ≤ ∑' k, ‖term (k + m)‖ :=
      norm_tsum_le_tsum_norm h_tail_summable.norm
    simp only [Real.norm_eq_abs] at h_norm_sum
    calc |∑' k, term (k + m)|
        ≤ ∑' k, |term (k + m)| := h_norm_sum
      _ ≤ ∑' k, geo_term k := h_tail_summable.abs.tsum_le_tsum h_term_bound h_geo_summable
      _ = |(q : ℝ)| ^ (2 * m + 1) * ∑' k, (|(q : ℝ)| ^ 2) ^ k := by
          simp only [geo_term]; rw [tsum_mul_left]
      _ = |(q : ℝ)| ^ (2 * m + 1) / (1 - |(q : ℝ)| ^ 2) := by
          rw [tsum_geometric_of_lt_one (sq_nonneg _) hz_abs_sq]; ring
      _ ≤ |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)| ^ 2) := by
          -- 2m + 1 ≥ n + 1 since 2m ≥ n
          have h_exp_le : n + 1 ≤ 2 * m + 1 := by omega
          have h_pow_le : |(q : ℝ)| ^ (2 * m + 1) ≤ |(q : ℝ)| ^ (n + 1) :=
            pow_le_pow_of_le_one hz_abs_nonneg hz_abs_le h_exp_le
          have h_denom_pos : 0 < 1 - |(q : ℝ)| ^ 2 := by nlinarith [sq_nonneg (q : ℝ), sq_abs (q :
            ℝ)]
          exact div_le_div_of_nonneg_right h_pow_le h_denom_pos.le
      _ ≤ |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)|) := by
          -- 1 - |q|² ≥ 1 - |q| since |q|² ≤ |q| for |q| ≤ 1
          have h1 : |(q : ℝ)| ^ 2 ≤ |(q : ℝ)| := by nlinarith [sq_nonneg (|(q : ℝ)| - 1)]
          have h2 : 1 - |(q : ℝ)| ≤ 1 - |(q : ℝ)| ^ 2 := by linarith
          have h3 : 0 < 1 - |(q : ℝ)| := by linarith
          have h4 : 0 ≤ |(q : ℝ)| ^ (n + 1) := pow_nonneg hz_abs_nonneg _
          exact div_le_div_of_nonneg_left h4 h3 h2
      _ = (R_rat : ℝ) := by
          -- R_rat = |q|^(n+1)/(1-|q|) in ℚ
          simp only [hR_rat_def]
          -- Show: |(q:ℝ)|^(n+1)/(1-|(q:ℝ)|) = (|q|^(n+1)/(1-|q|) : ℚ)
          rw [← Rat.cast_abs q]
          push_cast
          ring
  have h := abs_le.mp habs
  constructor
  · calc ((-R_rat : ℚ) : ℝ) = -((R_rat : ℚ) : ℝ) := by push_cast; ring
      _ ≤ _ := h.1
  · exact h.2

/-- FTIA for atanhPointComputable: Real.atanh q ∈ atanhPointComputable q n for |q| < 1. -/
theorem mem_atanhPointComputable (q : ℚ) (n : ℕ) (hq : |(q : ℝ)| < 1) :
    Real.atanh q ∈ atanhPointComputable q n := by
  simp only [atanhPointComputable]
  -- Since |q| < 1, the condition |q| ≥ 1 is false
  have hq_rat : |q| < 1 := by
    have h := abs_lt.mp hq
    rw [abs_lt]
    constructor
    · have : (-1 : ℝ) < q := h.1
      exact_mod_cast this
    · have : (q : ℝ) < 1 := h.2
      exact_mod_cast this
  have h_not_ge : ¬(|q| ≥ 1) := not_le.mpr hq_rat
  simp only [h_not_ge, ↓reduceIte]
  -- Polynomial part: the partial sum is in evalTaylorSeries
  have hpoly := mem_evalTaylorSeries_atanh n (q := q)
  -- Remainder part: the tail is in atanhRemainderBoundComputable
  have hrem := atanh_taylor_remainder_in_interval hq n
  -- Combine: atanh q = partial_sum + remainder
  have heq : Real.atanh q = ((atanhTaylorCoeffs n).zipIdx.map
      (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum +
      (Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map
        (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum) := by ring
  rw [heq]
  exact mem_add hpoly hrem

/-! ### Computable ln(2) via atanh

ln(2) = 2 * atanh(1/3), since:
  2 = (1 + 1/3) / (1 - 1/3) = (4/3) / (2/3)
  So atanh(1/3) = (1/2) * ln(2), giving ln(2) = 2 * atanh(1/3)
-/

/-- Compute ln(2) as an interval using 2 * atanh(1/3).
    This converges rapidly since atanh series at 1/3 has |y| = 1/3. -/
def ln2Computable (n : ℕ := 20) : IntervalRat :=
  let atanh_third := atanhPointComputable (1/3) n
  scale 2 atanh_third

/-- FTIA for ln2Computable: Real.log 2 ∈ ln2Computable n.
    Uses the identity log(2) = 2 * atanh(1/3) from log_via_atanh. -/
theorem mem_ln2Computable (n : ℕ) : Real.log 2 ∈ ln2Computable n := by
  simp only [ln2Computable]
  -- log(2) = 2 * atanh(1/3) via log_via_atanh
  have hlog_eq : Real.log 2 = 2 * Real.atanh (↑(1/3 : ℚ)) := by
    have h := LogReduction.log_via_atanh (by norm_num : (0 : ℚ) < 2)
    -- Convert: ((↑2 : ℝ) - 1) / ((↑2 : ℝ) + 1) = ↑(1/3 : ℚ)
    have h_arg : ((↑(2 : ℚ) : ℝ) - 1) / (↑(2 : ℚ) + 1) = ↑(1/3 : ℚ) := by
      simp only [Rat.cast_ofNat]
      norm_num
    rw [h_arg] at h
    convert! h using 1
  rw [hlog_eq]
  -- atanh(1/3) ∈ atanhPointComputable (1/3) n by mem_atanhPointComputable
  have h_third_lt : |(↑(1/3 : ℚ) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  exact mem_scale 2 (mem_atanhPointComputable (1/3) n h_third_lt)

/-! ### Computable log via argument reduction

For q > 0, we compute:
  1. Reduce q to m * 2^k where m ∈ [1/2, 2]
  2. Compute log(m) = 2 * atanh((m-1)/(m+1)), which has |arg| ≤ 1/3
  3. Result = log(m) + k * ln(2)
-/

/-- Reduction exponent k such that q * 2^(-k) ≈ 1 -/
def logReductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- Reduced mantissa m = q * 2^(-k) -/
def logReduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1
  else q * (2 : ℚ) ^ (-logReductionExponent q)

/-- Computable log at a single rational point q > 0.
    Returns log(q) = log(m) + k * ln(2) where m = q * 2^(-k). -/
def logPointComputable (q : ℚ) (n : ℕ := 20) : IntervalRat :=
  if q ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive
  else
    let k := logReductionExponent q
    let m := logReduceMantissa q
    -- log(m) = 2 * atanh((m-1)/(m+1))
    let y := (m - 1) / (m + 1)
    let atanh_y := atanhPointComputable y n
    let log_m := scale 2 atanh_y
    -- k * ln(2)
    let k_ln2 := scale k (ln2Computable n)
    add log_m k_ln2

/-- Logarithm evaluation using all configuration-dependent data prepared for depth `n`. -/
def logPointComputablePrepared (q : ℚ) (n : ℕ) (ln2 : IntervalRat)
    (atanhCoeffs : List ℚ) : IntervalRat :=
  if q ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let k := logReductionExponent q
    let m := logReduceMantissa q
    let y := (m - 1) / (m + 1)
    let atanh_y := atanhPointComputableWithCoeffs y n atanhCoeffs
    let log_m := scale 2 atanh_y
    let k_ln2 := scale k ln2
    add log_m k_ln2

theorem logPointComputablePrepared_eq (q : ℚ) (n : ℕ) :
    logPointComputablePrepared q n (ln2Computable n) (atanhTaylorCoeffs n) =
      logPointComputable q n := by
  simp [logPointComputablePrepared, logPointComputable,
    atanhPointComputableWithCoeffs_eq]

/-- Computable interval enclosure for log using endpoint evaluation.
    Since log is strictly increasing on (0, ∞), we evaluate at endpoints. -/
def logComputable (I : IntervalRat) (n : ℕ := 20) : IntervalRat :=
  if I.lo ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive interval
  else
    -- log is monotone increasing, so log([lo, hi]) = [log(lo), log(hi)]
    let logLo := logPointComputable I.lo n
    let logHi := logPointComputable I.hi n
    hull logLo logHi

/-- Interval logarithm using all data prepared for depth `n`. -/
def logComputablePrepared (I : IntervalRat) (n : ℕ) (ln2 : IntervalRat)
    (atanhCoeffs : List ℚ) : IntervalRat :=
  if I.lo ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let logLo := logPointComputablePrepared I.lo n ln2 atanhCoeffs
    let logHi := logPointComputablePrepared I.hi n ln2 atanhCoeffs
    hull logLo logHi

theorem logComputablePrepared_eq (I : IntervalRat) (n : ℕ) :
    logComputablePrepared I n (ln2Computable n) (atanhTaylorCoeffs n) =
      logComputable I n := by
  simp [logComputablePrepared, logComputable, logPointComputablePrepared_eq]

/-- The local logReductionExponent equals LogReduction.reductionExponent for positive q -/
private theorem logReductionExponent_eq {q : ℚ} (hq : 0 < q) :
    logReductionExponent q = LogReduction.reductionExponent q := by
  simp only [logReductionExponent, LogReduction.reductionExponent, not_le.mpr hq, ↓reduceIte]

/-- The local logReduceMantissa equals LogReduction.reduceMantissa for positive q -/
private theorem logReduceMantissa_eq {q : ℚ} (hq : 0 < q) :
    logReduceMantissa q = LogReduction.reduceMantissa q := by
  simp only [logReduceMantissa, LogReduction.reduceMantissa, not_le.mpr hq, ↓reduceIte,
             logReductionExponent_eq hq]

/-- FTIA for logPointComputable -/
theorem mem_logPointComputable {q : ℚ} (hq : 0 < q) (n : ℕ) :
    Real.log q ∈ logPointComputable q n := by
  unfold logPointComputable
  simp only [not_le.mpr hq, ↓reduceIte]
  -- Get the reduced mantissa and exponent
  set k := logReductionExponent q with hk_def
  set m := logReduceMantissa q with hm_def
  -- Show they equal the LogReduction definitions
  have hk_eq : k = LogReduction.reductionExponent q := logReductionExponent_eq hq
  have hm_eq : m = LogReduction.reduceMantissa q := logReduceMantissa_eq hq
  -- Get bounds on m from LogReduction.reduced_bounds
  have hm_bounds : 1/2 ≤ m ∧ m ≤ 2 := by rw [hm_eq]; exact LogReduction.reduced_bounds hq
  have hm_pos : 0 < m := by rw [hm_eq]; exact LogReduction.reduced_pos hq
  -- Compute y = (m-1)/(m+1) and get bounds from atanh_arg_bounds
  set y := (m - 1) / (m + 1) with hy_def
  have hy_bounds : (-1)/3 ≤ y ∧ y ≤ 1/3 := LogReduction.atanh_arg_bounds hm_bounds.1 hm_bounds.2
  -- Key: |y| ≤ 1/3 < 1, so we can use mem_atanhPointComputable
  have hy_abs_lt : |(y : ℝ)| < 1 := by
    rw [abs_lt]
    have hlo : ((-1 : ℚ) / 3 : ℝ) ≤ y := by exact_mod_cast hy_bounds.1
    have hhi : (y : ℝ) ≤ (1 : ℚ) / 3 := by exact_mod_cast hy_bounds.2
    constructor <;> linarith
  -- Step 1: atanh(y) ∈ atanhPointComputable y n
  have h_atanh := mem_atanhPointComputable y n hy_abs_lt
  -- Step 2: log(m) = 2 * atanh(y), so log(m) ∈ scale 2 (atanhPointComputable y n)
  have h_log_m_eq : Real.log m = 2 * Real.atanh y := by
    have h := LogReduction.log_via_atanh hm_pos
    -- h : Real.log m = 2 * Real.atanh ((m - 1) / (m + 1))
    -- Need to show: ((m - 1) / (m + 1) : ℚ) : ℝ = ((m : ℝ) - 1) / ((m : ℝ) + 1)
    have hcast : (y : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
      simp only [hy_def]
      push_cast
      ring
    rw [hcast]
    exact h
  have h_log_m := mem_scale 2 h_atanh
  -- h_log_m : (2 : ℚ) * Real.atanh y ∈ scale 2 (atanhPointComputable y n)
  -- h_log_m_eq : Real.log m = 2 * Real.atanh y
  have h_log_m' : Real.log m ∈ scale 2 (atanhPointComputable y n) := by
    rw [h_log_m_eq]
    exact h_log_m
  -- Step 3: log(2) ∈ ln2Computable n
  have h_ln2 := mem_ln2Computable n
  -- Step 4: k * log(2) ∈ scale k (ln2Computable n)
  have h_k_ln2 := mem_scale k h_ln2
  -- Step 5: log(q) = log(m) + k * log(2) by log_reduction
  have h_log_eq : Real.log q = Real.log m + k * Real.log 2 := by
    have h := LogReduction.log_reduction hq
    exact h
  -- Step 6: Combine using mem_add
  rw [h_log_eq]
  exact mem_add h_log_m' h_k_ln2

/-- FTIA for logComputable: if x ∈ I and I.lo > 0, then log(x) ∈ logComputable I n -/
theorem mem_logComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hpos : 0 < I.lo) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  simp only [logComputable, not_le.mpr hpos, ↓reduceIte]
  -- Since log is strictly monotone and x ∈ [lo, hi] with lo > 0:
  -- log(lo) ≤ log(x) ≤ log(hi)
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  have hlo_mem := mem_logPointComputable hpos n
  have hhi_pos : 0 < I.hi := lt_of_lt_of_le hpos I.le
  have hhi_mem := mem_logPointComputable hhi_pos n
  -- x ∈ [lo, hi] implies log(lo) ≤ log(x) ≤ log(hi) by monotonicity
  have hlog_lo_le : Real.log I.lo ≤ Real.log x :=
    Real.log_le_log hlo_pos hx.1
  have hlog_x_le_hi : Real.log x ≤ Real.log I.hi :=
    Real.log_le_log hx_pos hx.2
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (logPointComputable I.lo n).lo (logPointComputable I.hi n).lo : ℝ)
        ≤ (logPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.log I.lo := hlo_mem.1
      _ ≤ Real.log x := hlog_lo_le
  · calc Real.log x ≤ Real.log I.hi := hlog_x_le_hi
      _ ≤ (logPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((logPointComputable I.lo n).hi : ℝ) ((logPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

/-- Conditional version of mem_logComputable for use in correctness proofs.
    Requires I.lo > 0 so the log interval is well-defined and monotone. -/
theorem mem_logComputable' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hpos : 0 < I.lo) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  exact mem_logComputable hx hpos n

/-! ### Computable erf via Taylor series -/

/-- Interval containing 2/√π ≈ 1.128379...
    Used for erf calculations. 2/√π is in (1.128, 1.129). -/
def twoDivSqrtPi : IntervalRat :=
  ⟨1128/1000, 1129/1000, by norm_num⟩

/-- Taylor coefficients for erf (without the 2/√π factor):
    erf(x) = (2/√π) * Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (n! * (2n+1))

    So the coefficient of x^k is:
    - 0 if k is even
    - (-1)^((k-1)/2) / (((k-1)/2)! * k) if k is odd -/
def erfTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only: x, x³, x⁵, ...
      let m : ℕ := (i - 1) / 2  -- for x^(2m+1), m = (i-1)/2
      ((-1 : ℚ) ^ m) / (ratFactorial m * (i : ℚ))
    else 0)

/-- Computable erf remainder bound.
    Since |erf^{(k)}(x)| ≤ (2/√π) * 2^k for all x (rough bound),
    and erf is bounded by 1, we use a combination.

    For the Taylor remainder centered at 0, we use:
    |R_n(x)| ≤ sup|f^{(n+1)}(ξ)| * |x|^{n+1} / (n+1)!

    A conservative bound: |erf^{(k)}(x)| ≤ (2/√π) * k! / (k/2)! ≤ 2 * k^{k/2}
    But since |erf| ≤ 1, we can intersect with [-1, 1].

    We use: remainder ≤ 2 * |x|^{n+1} / (n+1)! (very conservative). -/
def erfRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Conservative bound: use 2 as the derivative bound (since 2/√π ≈ 1.13)
  let R := 2 * r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hfact : (0 : ℚ) ≤ ratFactorial (n + 1) := by
      simp only [ratFactorial]; exact Nat.cast_nonneg _
    have hpow : (0 : ℚ) ≤ r ^ (n + 1) := pow_nonneg hr _
    have hR : 0 ≤ R := div_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) hpow) hfact
    linarith⟩

/-- Computable interval enclosure for erf at a single rational point.
    Uses sign-aware clipped linear bounds:
    `|erf(q)| ≤ min(1, (2257/2000)*|q|)`.

    Cases:
    - `q < 0  => erf(q) ∈ [-1, 0]`
    - `q = 0  => erf(q) = 0`
    - `q > 0  => erf(q) ∈ [0, 1]`

    with tighter near-zero magnitude via `(2257/2000)*|q|`. -/
def erfPointComputable (q : ℚ) (n : ℕ := 15) : IntervalRat :=
  let _ := n
  let b : ℚ := min 1 ((2257 / 2000) * |q|)
  if hq : q < 0 then
    ⟨-b, 0, by
      unfold b
      have hb_nonneg : (0 : ℚ) ≤ min 1 ((2257 / 2000) * |q|) := by
        apply le_min
        · norm_num
        · exact mul_nonneg (by norm_num) (abs_nonneg q)
      linarith⟩
  else if h0 : q = 0 then
    ⟨0, 0, by norm_num⟩
  else
    ⟨0, b, by
      unfold b
      have hb_nonneg : (0 : ℚ) ≤ min 1 ((2257 / 2000) * |q|) := by
        apply le_min
        · norm_num
        · exact mul_nonneg (by norm_num) (abs_nonneg q)
      exact hb_nonneg⟩

/-- Computable interval enclosure for erf using Taylor series with monotonicity.

    erf(x) = (2/√π) * Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (n! * (2n+1))

    Since erf is strictly monotone increasing (erf'(x) = (2/√π)e^{-x²} > 0),
    we use endpoint evaluation: erf([a,b]) ⊆ [erf(a), erf(b)].

    We intersect with [-1, 1] for safety. -/
def erfComputable (I : IntervalRat) (n : ℕ := 15) : IntervalRat :=
  -- erf is strictly monotone increasing, so evaluate at endpoints
  let erfLo := erfPointComputable I.lo n
  let erfHi := erfPointComputable I.hi n
  let raw := hull erfLo erfHi
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => globalBound

/-- 2/√π is in the interval twoDivSqrtPi.
    2/√π ≈ 1.1283791670955126, which is in (1.128, 1.129).

    This is a helper theorem for correctness proofs. The computation of
    erfComputable is independent of this theorem. -/
theorem two_div_sqrt_pi_mem : 2 / Real.sqrt Real.pi ∈ twoDivSqrtPi := by
  simp only [twoDivSqrtPi, mem_def]
  -- From π bounds: 3.1415 < π < 3.1416 (Real.pi_gt_d4, Real.pi_lt_d4)
  -- So √π is between √3.1415 ≈ 1.7724 and √3.1416 ≈ 1.7725
  -- Thus 2/√π is between 2/1.7725 ≈ 1.1283 and 2/1.7724 ≈ 1.1285
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_hi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hsqrt_lo : (1.7724 : ℝ) < Real.sqrt Real.pi := by
    have h1 : (1.7724 : ℝ) ^ 2 < Real.pi := by
      have : (1.7724 : ℝ) ^ 2 = 3.14140176 := by ring
      linarith
    have h2 : (0 : ℝ) ≤ 1.7724 := by norm_num
    have h3 : (0 : ℝ) ≤ 1.7724 ^ 2 := by positivity
    calc (1.7724 : ℝ) = Real.sqrt (1.7724 ^ 2) := (Real.sqrt_sq h2).symm
      _ < Real.sqrt Real.pi := Real.sqrt_lt_sqrt h3 h1
  have hsqrt_hi : Real.sqrt Real.pi < (1.7725 : ℝ) := by
    have h1 : Real.pi < (1.7725 : ℝ) ^ 2 := by
      have : (1.7725 : ℝ) ^ 2 = 3.14175625 := by ring
      linarith
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [← Real.sqrt_sq (le_of_lt (by norm_num : (0 : ℝ) < 1.7725))]
    exact Real.sqrt_lt_sqrt (le_of_lt hpi_pos) h1
  constructor
  · -- Goal: ↑(1128 / 1000) ≤ 2 / √π
    have h1 : ((1128 / 1000 : ℚ) : ℝ) < 2 / 1.7725 := by norm_num
    have h2 : (2 : ℝ) / 1.7725 < 2 / Real.sqrt Real.pi := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
      · exact Real.sqrt_pos.mpr Real.pi_pos
      · exact hsqrt_hi
    exact le_of_lt (lt_trans h1 h2)
  · -- Goal: 2 / √π ≤ ↑(1129 / 1000)
    have h1 : 2 / Real.sqrt Real.pi < (2 : ℝ) / 1.7724 := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
      · norm_num
      · exact hsqrt_lo
    have h2 : (2 : ℝ) / 1.7724 < ((1129 / 1000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt (lt_trans h1 h2)

/-- The "inner" erf function without the 2/√π factor:
    erfInner(x) = ∫₀ˣ exp(-t²) dt = (√π/2) * erf(x)

    This is the function whose Taylor series coefficients are erfTaylorCoeffs. -/
noncomputable def erfInner (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (-(t^2))

/-- erf(x) = (2/√π) * erfInner(x) -/
theorem erf_eq_factor_mul_inner (x : ℝ) : Real.erf x = (2 / Real.sqrt Real.pi) * erfInner x := by
  unfold Real.erf erfInner
  ring

/-- The derivatives of erfInner(x) = ∫₀ˣ exp(-t²) dt.
    erfInner'(x) = exp(-x²)
    erfInner''(x) = -2x * exp(-x²)
    etc. -/
theorem erfInner_deriv : deriv erfInner = fun x => Real.exp (-(x^2)) := by
  ext x
  unfold erfInner
  have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
    Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
  exact hcont.integral_hasStrictDerivAt 0 x |>.hasDerivAt.deriv

/-- exp(-x²) is smooth. -/
theorem contDiff_exp_neg_sq : ContDiff ℝ ⊤ (fun x => Real.exp (-(x^2))) :=
  Real.contDiff_exp.comp (contDiff_neg.comp (contDiff_id.pow 2))

/-- exp(-x²) is analytic everywhere. -/
theorem analyticAt_exp_neg_sq (x : ℝ) : AnalyticAt ℝ (fun t => Real.exp (-(t^2))) x := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => t^2) x := analyticAt_id.pow 2
  have h2 : AnalyticAt ℝ (fun t : ℝ => -(t^2)) x := h1.neg
  exact h2.rexp

/-- exp(-x²) is analytic on ℝ. -/
theorem analyticOnNhd_exp_neg_sq : AnalyticOnNhd ℝ (fun t => Real.exp (-(t^2))) Set.univ :=
  fun x _ => analyticAt_exp_neg_sq x

/-- Helper: erfInner is C^n for all n. -/
private theorem erfInner_contDiff_nat (n : ℕ) : ContDiff ℝ n erfInner := by
  induction n with
  | zero =>
    -- C^0 = continuous
    refine contDiff_zero.mpr ?_
    have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
      Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
    have h_int : ∀ a b : ℝ, IntervalIntegrable (fun t => Real.exp (-(t^2))) MeasureTheory.volume a
      b :=
      fun a b => hcont.intervalIntegrable a b
    exact intervalIntegral.continuous_primitive h_int 0
  | succ n _ih =>
    -- C^(n+1) from C^n of derivative
    have hdiff : Differentiable ℝ erfInner := fun x =>
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow
        2))).integral_hasStrictDerivAt 0 x
        |>.hasStrictFDerivAt.differentiableAt
    have hderiv_smooth : ContDiff ℝ n (deriv erfInner) := by
      simp only [erfInner_deriv]
      exact contDiff_exp_neg_sq.of_le le_top
    exact contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, hderiv_smooth⟩

/-! ### Computable atanh interval via endpoint evaluation -/

/-- Computable interval enclosure for atanh using endpoint evaluation.
    Since atanh is strictly increasing on (-1, 1), we evaluate at endpoints.
    Requires the interval to be strictly inside (-1, 1); returns a wide fallback otherwise. -/
def atanhComputable (I : IntervalRat) (n : ℕ := 15) : IntervalRat :=
  if I.lo ≤ -1 then
    ⟨-1000, 1000, by norm_num⟩
  else if 1 ≤ I.hi then
    ⟨-1000, 1000, by norm_num⟩
  else
    let atanhLo := atanhPointComputable I.lo n
    let atanhHi := atanhPointComputable I.hi n
    hull atanhLo atanhHi

/-- Interval `atanh` using Taylor coefficients prepared for depth `n`. -/
def atanhComputableWithCoeffs (I : IntervalRat) (n : ℕ)
    (coeffs : List ℚ) : IntervalRat :=
  if I.lo ≤ -1 then
    ⟨-1000, 1000, by norm_num⟩
  else if 1 ≤ I.hi then
    ⟨-1000, 1000, by norm_num⟩
  else
    let atanhLo := atanhPointComputableWithCoeffs I.lo n coeffs
    let atanhHi := atanhPointComputableWithCoeffs I.hi n coeffs
    hull atanhLo atanhHi

theorem atanhComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    atanhComputableWithCoeffs I n (atanhTaylorCoeffs n) = atanhComputable I n := by
  simp [atanhComputableWithCoeffs, atanhComputable, atanhPointComputableWithCoeffs_eq]

/-- FTIA for atanhComputable: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhComputable I n. -/
theorem mem_atanhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (hlo : -1 < I.lo) (hhi : I.hi < 1) (n : ℕ) :
    Real.atanh x ∈ atanhComputable I n := by
  simp only [atanhComputable, not_le.mpr hlo, ↓reduceIte, not_le.mpr hhi, ↓reduceIte]
  -- x ∈ I ⊂ (-1, 1), so |lo|, |hi|, |x| < 1
  have hlo_real : (-1 : ℝ) < I.lo := by exact_mod_cast hlo
  have hhi_real : (I.hi : ℝ) < 1 := by exact_mod_cast hhi
  have hx_lo : -1 < x := by linarith [hx.1]
  have hx_hi : x < 1 := by linarith [hx.2]
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have habs_lo : |(I.lo : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_hi : |(I.hi : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_x : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- atanh at endpoints
  have hlo_abs_rat : |(I.lo : ℝ)| < 1 := habs_lo
  have hhi_abs_rat : |(I.hi : ℝ)| < 1 := habs_hi
  have hlo_mem := mem_atanhPointComputable I.lo n hlo_abs_rat
  have hhi_mem := mem_atanhPointComputable I.hi n hhi_abs_rat
  -- Monotonicity: atanh(lo) ≤ atanh(x) ≤ atanh(hi)
  have hatanh_lo_le : Real.atanh I.lo ≤ Real.atanh x :=
    Real.atanh_mono habs_lo habs_x hx.1
  have hatanh_x_le_hi : Real.atanh x ≤ Real.atanh I.hi :=
    Real.atanh_mono habs_x habs_hi hx.2
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (atanhPointComputable I.lo n).lo (atanhPointComputable I.hi n).lo : ℝ)
        ≤ (atanhPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.atanh I.lo := hlo_mem.1
      _ ≤ Real.atanh x := hatanh_lo_le
  · calc Real.atanh x ≤ Real.atanh I.hi := hatanh_x_le_hi
      _ ≤ (atanhPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((atanhPointComputable I.lo n).hi : ℝ) ((atanhPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

end IntervalRat

end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Rational Endpoint Intervals

This file defines `IntervalRat`, a concrete interval type with rational endpoints
suitable for computation. We prove the Fundamental Theorem of Interval Arithmetic
(FTIA) for each operation.

## Module Structure

* `IntervalRat.Basic` - Core types: `IntervalRat`, membership, basic operations
* `IntervalRat.Transcendental` - Noncomputable transcendental bounds (exp, log, sqrt, atanh)
* `IntervalRat.Taylor` - Computable Taylor series evaluators

## Main definitions

* `LeanCert.Core.IntervalRat` - Intervals with rational endpoints
* `LeanCert.Core.IntervalRat.toSet` - Semantic interpretation as a subset of ℝ
* Operations: `add`, `neg`, `sub`, `mul`, `inv`, `div`
* Computable: `expComputable`, `sinComputable`, `cosComputable`

## Main theorems

* `mem_add` - FTIA for addition
* `mem_neg` - FTIA for negation
* `mem_sub` - FTIA for subtraction
* `mem_mul` - FTIA for multiplication
* `mem_expComputable`, `mem_sinComputable`, `mem_cosComputable` - FTIA for computable functions

## Design notes

All operations maintain the invariant `lo ≤ hi`. Domain restrictions for partial
operations (like `inv`) are encoded via separate types or explicit hypotheses.
-/

public section

end

end

section

/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Dyadic Intervals

Intervals with Dyadic endpoints. These support "Outward Rounding", ensuring
mathematical soundness even when we limit numerical precision.

## Main definitions

* `IntervalDyadic` - Interval with Dyadic endpoints
* `IntervalDyadic.add`, `mul`, `neg` - Interval arithmetic operations
* `IntervalDyadic.roundOut` - Outward rounding to control precision
* `IntervalDyadic.toIntervalRat` - Convert to rational interval for verification

## Design notes

The key feature is `roundOut`: after each operation, we can enforce a minimum
exponent to prevent precision explosion. When rounding:
- Lower bounds are shifted down (toward -∞)
- Upper bounds are shifted up (toward +∞)

This maintains the containment invariant: the rounded interval always contains
the original interval, which contains the true mathematical value.

## Performance

In v1.0, `Rat` multiplication of `1/3 * 1/3 * ... * 1/3` (10 times) creates
a denominator of 3^10 = 59049. Each operation requires GCD computation.

In v1.1, with `precision = -10`, the denominator stays fixed at 2^10 = 1024.
The result is slightly less tight but computed significantly faster.
-/

public section

namespace LeanCert.Core

/-- An interval with Dyadic endpoints.

Maintains invariant: `lo.toRat ≤ hi.toRat` -/
structure IntervalDyadic where
  /-- Lower bound -/
  lo : Dyadic
  /-- Upper bound -/
  hi : Dyadic
  /-- Invariant: lower bound ≤ upper bound -/
  le : lo.toRat ≤ hi.toRat
  deriving Repr

namespace IntervalDyadic

/-! ### Membership and Sets -/

/-- The set of reals contained in this interval -/
def toSet (I : IntervalDyadic) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in a Dyadic interval -/
instance : Membership ℝ IntervalDyadic where
  mem I x := (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalDyadic) :
    x ∈ I ↔ (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ) := Iff.rfl

/-! ### Conversion to IntervalRat -/

/-- Convert to IntervalRat for verification with existing theorems -/
@[expose]
def toIntervalRat (I : IntervalDyadic) : IntervalRat :=
  ⟨I.lo.toRat, I.hi.toRat, I.le⟩

/-- Membership is preserved by conversion to IntervalRat -/
theorem mem_toIntervalRat {x : ℝ} {I : IntervalDyadic} :
    x ∈ I ↔ x ∈ I.toIntervalRat := by
  simp only [mem_def, toIntervalRat, IntervalRat.mem_def]

/-! ### Construction -/

/-- Create a singleton interval from a Dyadic -/
@[expose]
def singleton (d : Dyadic) : IntervalDyadic := ⟨d, d, le_refl _⟩

/-- A Dyadic value is in its singleton interval -/
theorem mem_singleton (d : Dyadic) : (d.toRat : ℝ) ∈ singleton d := by
  simp only [mem_def, singleton]
  exact ⟨le_refl _, le_refl _⟩

/-- Default interval [0, 0] -/
instance : Inhabited IntervalDyadic where
  default := singleton Dyadic.zero

/-- Create an interval, checking the invariant -/
def mk? (lo hi : Dyadic) : Option IntervalDyadic :=
  if h : lo.toRat ≤ hi.toRat then some ⟨lo, hi, h⟩ else none

/-- The width of an interval -/
def width (I : IntervalDyadic) : Dyadic := I.hi.sub I.lo

/-- The dyadic width denotes endpoint subtraction exactly. -/
@[simp]
theorem width_toRat (I : IntervalDyadic) :
    I.width.toRat = I.hi.toRat - I.lo.toRat := by
  simp only [width, Dyadic.sub, Dyadic.toRat_add, Dyadic.toRat_neg]
  ring

/-- Exact midpoint of a dyadic interval.

Dyadics are closed under division by two, so midpoint construction must lower
the exponent rather than shift (and potentially round) the mantissa. -/
def midpoint (I : IntervalDyadic) : Dyadic :=
  (I.lo.add I.hi).scale2 (-1)

/-- The dyadic midpoint denotes the ordinary rational midpoint exactly. -/
@[simp]
theorem midpoint_toRat (I : IntervalDyadic) :
    I.midpoint.toRat = (I.lo.toRat + I.hi.toRat) / 2 := by
  simp only [midpoint, Dyadic.toRat_scale2, Dyadic.toRat_add]
  norm_num [div_eq_mul_inv]

/-- The lower endpoint is at most the exact midpoint. -/
theorem lo_le_midpoint (I : IntervalDyadic) : I.lo.toRat ≤ I.midpoint.toRat := by
  rw [midpoint_toRat]
  linarith [I.le]

/-- The exact midpoint is at most the upper endpoint. -/
theorem midpoint_le_hi (I : IntervalDyadic) : I.midpoint.toRat ≤ I.hi.toRat := by
  rw [midpoint_toRat]
  linarith [I.le]

/-- Split a dyadic interval into two exact closed halves. -/
def bisect (I : IntervalDyadic) : IntervalDyadic × IntervalDyadic :=
  (⟨I.lo, I.midpoint, I.lo_le_midpoint⟩,
   ⟨I.midpoint, I.hi, I.midpoint_le_hi⟩)

/-- A point in the original interval and left of the midpoint is in the left half. -/
theorem mem_bisect_left {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hm : x ≤ (I.midpoint.toRat : ℝ)) : x ∈ (I.bisect).1 := by
  exact ⟨hx.1, hm⟩

/-- A point in the original interval and right of the midpoint is in the right half. -/
theorem mem_bisect_right {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hm : (I.midpoint.toRat : ℝ) ≤ x) : x ∈ (I.bisect).2 := by
  exact ⟨hm, hx.2⟩

/-- Membership in the left half implies membership in the original interval. -/
theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ (I.bisect).1) : x ∈ I := by
  refine ⟨hx.1, hx.2.trans ?_⟩
  exact_mod_cast I.midpoint_le_hi

/-- Membership in the right half implies membership in the original interval. -/
theorem mem_of_mem_bisect_right {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ (I.bisect).2) : x ∈ I := by
  refine ⟨?_, hx.2⟩
  exact (by exact_mod_cast I.lo_le_midpoint : (I.lo.toRat : ℝ) ≤ I.midpoint.toRat) |>.trans hx.1

/-- The two closed halves cover the original interval, including their shared seam. -/
theorem mem_bisect_or {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    x ∈ (I.bisect).1 ∨ x ∈ (I.bisect).2 := by
  by_cases hm : x ≤ (I.midpoint.toRat : ℝ)
  · exact Or.inl (mem_bisect_left hx hm)
  · exact Or.inr (mem_bisect_right hx (le_of_lt (not_le.mp hm)))

/-- Both closed halves contain the midpoint seam. -/
theorem midpoint_mem_bisect_both (I : IntervalDyadic) :
    (I.midpoint.toRat : ℝ) ∈ (I.bisect).1 ∧
      (I.midpoint.toRat : ℝ) ∈ (I.bisect).2 := by
  constructor
  · exact ⟨by exact_mod_cast I.lo_le_midpoint, le_rfl⟩
  · exact ⟨le_rfl, by exact_mod_cast I.midpoint_le_hi⟩

/-- The overlap of the two closed children is exactly their midpoint seam. -/
theorem bisect_intersection (I : IntervalDyadic) :
    I.bisect.1.toSet ∩ I.bisect.2.toSet = {I.midpoint.toReal} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hx' :
        ((I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.midpoint.toRat : ℝ)) ∧
          ((I.midpoint.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ)) := by
      simpa [toSet, bisect, Dyadic.toReal] using hx
    exact le_antisymm hx'.1.2 hx'.2.1
  · rintro rfl
    simpa [toSet, bisect, Dyadic.toReal] using I.midpoint_mem_bisect_both

/-- The left child has exactly half the semantic width of its parent. -/
theorem bisect_left_width_toRat (I : IntervalDyadic) :
    I.bisect.1.width.toRat = I.width.toRat / 2 := by
  simp only [width_toRat, bisect, midpoint_toRat]
  ring

/-- The right child has exactly half the semantic width of its parent. -/
theorem bisect_right_width_toRat (I : IntervalDyadic) :
    I.bisect.2.width.toRat = I.width.toRat / 2 := by
  simp only [width_toRat, bisect, midpoint_toRat]
  ring

/-! ### Outward Rounding -/

/-- Outward rounding: enforces a maximum precision (minimum exponent).

This is the key operation for preventing precision explosion.
`minExp` is the minimum allowed exponent (higher = coarser precision).

For example, `minExp = -10` ensures all values are multiples of 2^(-10) ≈ 0.001.
-/
def roundOut (I : IntervalDyadic) (minExp : Int) : IntervalDyadic :=
  let newLo := I.lo.shiftDown minExp
  let newHi := I.hi.shiftUp minExp
  ⟨newLo, newHi, by
    -- Proof: newLo ≤ I.lo ≤ I.hi ≤ newHi
    have h1 : newLo.toRat ≤ I.lo.toRat := Dyadic.toRat_shiftDown_le I.lo minExp
    have h2 : I.lo.toRat ≤ I.hi.toRat := I.le
    have h3 : I.hi.toRat ≤ newHi.toRat := Dyadic.toRat_shiftUp_ge I.hi minExp
    linarith⟩

/-- roundOut produces an interval containing the original -/
theorem roundOut_contains {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (minExp : Int) :
    x ∈ I.roundOut minExp := by
  simp only [mem_def] at *
  constructor
  · have h := Dyadic.toRat_shiftDown_le I.lo minExp
    have h' : ((I.lo.shiftDown minExp).toRat : ℝ) ≤ (I.lo.toRat : ℝ) := by exact_mod_cast h
    calc ((I.roundOut minExp).lo.toRat : ℝ) = ((I.lo.shiftDown minExp).toRat : ℝ) := by rfl
      _ ≤ (I.lo.toRat : ℝ) := h'
      _ ≤ x := hx.1
  · have h := Dyadic.toRat_shiftUp_ge I.hi minExp
    have h' : (I.hi.toRat : ℝ) ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := by exact_mod_cast h
    calc x ≤ (I.hi.toRat : ℝ) := hx.2
      _ ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := h'
      _ = ((I.roundOut minExp).hi.toRat : ℝ) := by rfl

/-! ### Interval Negation -/

/-- Negate an interval -/
def neg (I : IntervalDyadic) : IntervalDyadic where
  lo := I.hi.neg
  hi := I.lo.neg
  le := by
    simp only [Dyadic.toRat_neg]
    linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Dyadic.toRat_neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval Addition -/

/-- Add two intervals -/
def add (I J : IntervalDyadic) : IntervalDyadic where
  lo := I.lo.add J.lo
  hi := I.hi.add J.hi
  le := by
    simp only [Dyadic.toRat_add]
    linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Dyadic.toRat_add, Rat.cast_add]
  constructor <;> linarith

/-- Add with precision control -/
@[expose]
def addRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (add I J).roundOut prec

/-! ### Interval Subtraction -/

/-- Subtract two intervals -/
def sub (I J : IntervalDyadic) : IntervalDyadic := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval Multiplication -/

/-- Multiply two intervals.

Uses min/max of all four endpoint products to handle signs correctly.
This is the exact multiplication - mantissas may grow. Use `mulRounded` or
`mulNormalized` for controlled precision.

Correctness: For x ∈ [a,b] and y ∈ [c,d], the product x*y lies in the interval
[min(ac,ad,bc,bd), max(ac,ad,bc,bd)]. -/
def mul (I J : IntervalDyadic) : IntervalDyadic :=
  let v1 := I.lo.mul J.lo
  let v2 := I.lo.mul J.hi
  let v3 := I.hi.mul J.lo
  let v4 := I.hi.mul J.hi
  ⟨Dyadic.min4 v1 v2 v3 v4, Dyadic.max4 v1 v2 v3 v4, Dyadic.min4_le_max4 v1 v2 v3 v4⟩

/-- Fast interval multiplication using sign-based case splitting.
    Reduces from 4 multiplications + 12 comparisons to 2 multiplications
    in the common case (both intervals positive or both negative).
    Falls back to the full 4-way product for mixed-sign intervals. -/
def mulFast (I J : IntervalDyadic) : IntervalDyadic :=
  if hI : Dyadic.le 0 I.lo then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.hi.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else if hI2 : Dyadic.le I.hi 0 then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.lo.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      mul I J

/- We intentionally do not attach `mulFast` as a native replacement here.
   Native certificate checking should execute the same definition that the
   kernel proofs reason about. Keep `mulFast` available only as an internal
   candidate for future explicitly-audited runtime backends. -/

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  -- Use IntervalRat.mem_mul and translate the bounds
  have hxI := mem_toIntervalRat.mp hx
  have hyJ := mem_toIntervalRat.mp hy
  have hmul := IntervalRat.mem_mul hxI hyJ
  simp only [mem_def, mul] at *
  -- hmul has bounds from IntervalRat.mul which are min/max of 4 products
  -- Our Dyadic.min4/max4 has the same structure with toRat preserving the products
  constructor
  · -- Lower bound: Dyadic.min4.toRat equals the rational min4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.min4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = min (min (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (min (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.min4, Dyadic.toRat_mul, Dyadic.min_toRat]
    rw [heq]
    exact_mod_cast hmul.1
  · -- Upper bound: Dyadic.max4.toRat equals the rational max4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.max4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = max (max (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (max (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.max4, Dyadic.toRat_mul, Dyadic.max_toRat]
    rw [heq]
    exact_mod_cast hmul.2

/-- Dyadic.min4 converts to rational min4 -/
private theorem min4_toRat (a b c d : Dyadic) :
    (Dyadic.min4 a b c d).toRat = IntervalRat.min4 a.toRat b.toRat c.toRat d.toRat := by
  simp only [Dyadic.min4, IntervalRat.min4, Dyadic.min_toRat]

/-- Dyadic.max4 converts to rational max4 -/
private theorem max4_toRat (a b c d : Dyadic) :
    (Dyadic.max4 a b c d).toRat = IntervalRat.max4 a.toRat b.toRat c.toRat d.toRat := by
  simp only [Dyadic.max4, IntervalRat.max4, Dyadic.max_toRat]

/-- Extract 0 ≤ toRat from Dyadic.le 0 d -/
private theorem toRat_nonneg_of_le {d : Dyadic} (h : Dyadic.le 0 d) : 0 ≤ d.toRat := by
  have := (Dyadic.le_iff_toRat_le 0 d).mp h; rwa [Dyadic.toRat_zero] at this

/-- Extract toRat ≤ 0 from Dyadic.le d 0 -/
private theorem toRat_nonpos_of_le {d : Dyadic} (h : Dyadic.le d 0) : d.toRat ≤ 0 := by
  have := (Dyadic.le_iff_toRat_le d 0).mp h; rwa [Dyadic.toRat_zero] at this

/-- Extract toRat < 0 from ¬ Dyadic.le 0 d -/
private theorem toRat_neg_of_not_le {d : Dyadic} (h : ¬ Dyadic.le 0 d) : d.toRat < 0 := by
  exact lt_of_not_ge fun h' => h ((Dyadic.le_iff_toRat_le 0 d).mpr (by rwa [Dyadic.toRat_zero]))

/-- Extract 0 < toRat from ¬ Dyadic.le d 0 -/
private theorem toRat_pos_of_not_le {d : Dyadic} (h : ¬ Dyadic.le d 0) : 0 < d.toRat := by
  exact lt_of_not_ge fun h' => h ((Dyadic.le_iff_toRat_le d 0).mpr (by rwa [Dyadic.toRat_zero]))

/-- mulFast endpoints match mul endpoints: lo -/
private theorem mulFast_lo (I J : IntervalDyadic) : (mulFast I J).lo.toRat = (mul I J).lo.toRat :=
  by
  have hrhs : (mul I J).lo.toRat = IntervalRat.min4
      (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat)
      (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat) := by
    simp only [mul, Dyadic.toRat_mul, min4_toRat]
  rw [hrhs]; unfold mulFast
  split
  · rename_i hI
    have hIlo := toRat_nonneg_of_le hI
    split
    · rename_i hJ
      have hJlo := toRat_nonneg_of_le hJ
      simp only [Dyadic.toRat_mul]
      exact IntervalRat.eq_min4_of_le (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · rename_i _ hJ2
        have hJhi := toRat_nonpos_of_le hJ2
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · rename_i hJ hJ2
        have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
        have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · rename_i _ hI2
      have hIhi := toRat_nonpos_of_le hI2
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rename_i hJ hJ2
          have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
          have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · rename_i hI hI2
      have hIlo := le_of_lt (toRat_neg_of_not_le hI)
      have hIhi := le_of_lt (toRat_pos_of_not_le hI2)
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact hrhs

/-- mulFast endpoints match mul endpoints: hi -/
private theorem mulFast_hi (I J : IntervalDyadic) : (mulFast I J).hi.toRat = (mul I J).hi.toRat :=
  by
  have hrhs : (mul I J).hi.toRat = IntervalRat.max4
      (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat)
      (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat) := by
    simp only [mul, Dyadic.toRat_mul, max4_toRat]
  rw [hrhs]; unfold mulFast
  split
  · rename_i hI
    have hIlo := toRat_nonneg_of_le hI
    split
    · rename_i hJ
      have hJlo := toRat_nonneg_of_le hJ
      simp only [Dyadic.toRat_mul]
      exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · rename_i _ hJ2
        have hJhi := toRat_nonpos_of_le hJ2
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · rename_i hJ hJ2
        have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
        have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · rename_i _ hI2
      have hIhi := toRat_nonpos_of_le hI2
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rename_i hJ hJ2
          have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
          have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · rename_i hI hI2
      have hIlo := le_of_lt (toRat_neg_of_not_le hI)
      have hIhi := le_of_lt (toRat_pos_of_not_le hI2)
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact hrhs

/-- `mulFast` preserves the containment property of `mul`.
    This is retained as documentation and a future audited optimization hook;
    production certificate checking currently uses `mul` directly. -/
theorem mem_mulFast {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulFast I J := by
  simp only [mem_def]
  constructor
  · rw [mulFast_lo]; exact (mem_mul hx hy).1
  · rw [mulFast_hi]; exact (mem_mul hx hy).2

/-- Multiply with precision control (outward rounding) -/
@[expose]
def mulRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (mul I J).roundOut prec

/-- Multiply with mantissa normalization (prevents bit explosion) -/
def mulNormalized (I J : IntervalDyadic) (maxBits : Nat := 256) : IntervalDyadic :=
  let result := mul I J
  ⟨result.lo.normalizeDown maxBits, result.hi.normalizeUp maxBits, by
    -- Normalization preserves ordering: lo.normalizeDown ≤ lo ≤ hi ≤ hi.normalizeUp
    calc (result.lo.normalizeDown maxBits).toRat
        ≤ result.lo.toRat := Dyadic.toRat_normalizeDown_le _ _
      _ ≤ result.hi.toRat := result.le
      _ ≤ (result.hi.normalizeUp maxBits).toRat := Dyadic.toRat_normalizeUp_ge _ _⟩

/-! ### Interval Scaling -/

/-- Scale an interval by a constant Dyadic -/
def scale (I : IntervalDyadic) (c : Dyadic) : IntervalDyadic :=
  if hc : Dyadic.le Dyadic.zero c then
    ⟨I.lo.mul c, I.hi.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcnn : 0 ≤ c.toRat := by
        have := Dyadic.le_iff_toRat_le Dyadic.zero c |>.mp hc
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at this; exact this
      exact mul_le_mul_of_nonneg_right I.le hcnn⟩
  else
    ⟨I.hi.mul c, I.lo.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcneg : c.toRat < 0 := by
        have hf := Dyadic.le_iff_toRat_le Dyadic.zero c
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at hf
        by_contra! hge
        exact hc (hf.mpr hge)
      exact mul_le_mul_of_nonpos_right I.le (le_of_lt hcneg)⟩

/-- Scale by a power of 2 (very efficient: just adjusts exponents) -/
def scale2 (I : IntervalDyadic) (n : Int) : IntervalDyadic :=
  ⟨I.lo.scale2 n, I.hi.scale2 n, Dyadic.toRat_scale2_le_scale2 I.lo I.hi n I.le⟩

/-! ### Square Root -/

/-- Square root of an interval.
    Returns a conservative bound [0, max(hi, 1)].
    This is sound because:
    - sqrt(x) = 0 for x < 0 (by definition in Mathlib)
    - sqrt(x) ≥ 0 for all x
    - sqrt(x) ≤ max(x, 1) for x ≥ 0
    Therefore for any x ∈ [lo, hi], sqrt(x) ∈ [0, max(hi, 1)]. -/
def sqrt (I : IntervalDyadic) (_prec : Int := -53) : IntervalDyadic :=
  -- Conservative bound: [0, max(hi, 1)]
  -- sqrt(x) ≥ 0 for all x (including negative where sqrt returns 0)
  -- sqrt(x) ≤ max(x, 1) for x ≥ 0
  -- sqrt(x) = 0 ≤ max(hi, 1) for x < 0
  let one := Dyadic.ofInt 1
  let hi_bound := Dyadic.max I.hi one
  ⟨Dyadic.zero, hi_bound, by
    have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
    rw [Dyadic.max_toRat, Dyadic.toRat_ofInt, hz]
    exact le_max_of_le_right (by norm_num : (0 : ℚ) ≤ 1)⟩

/-- sqrt(x) ≤ max(x, 1) for all x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  by_cases! h : x ≤ 1
  · -- Case x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    -- sqrt(x) ≤ 1 when x ≤ 1 because sqrt(x)^2 = x ≤ 1 and sqrt(x) ≥ 0
    have hsqrt_le_one : Real.sqrt x ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h
    calc Real.sqrt x ≤ 1 := hsqrt_le_one
      _ ≤ max x 1 := le_max_right x 1
  · -- Case x > 1: sqrt(x) ≤ x = max(x, 1)
    -- sqrt(x) ≤ x for x ≥ 1 follows from sqrt(x) * sqrt(x) = x and sqrt(x) ≥ 1
    have h1 : 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (le_of_lt h)
    have hsqrt_le_x : Real.sqrt x ≤ x := by
      calc Real.sqrt x = Real.sqrt x * 1 := by ring
        _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
        _ = x := by rw [← sq, Real.sq_sqrt hx]
    calc Real.sqrt x ≤ x := hsqrt_le_x
      _ ≤ max x 1 := le_max_left x 1

/-- Soundness of interval sqrt: if x ∈ I, x ≥ 0, then Real.sqrt x ∈ sqrt I -/
theorem mem_sqrt {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (hx_nn : 0 ≤ x) (prec : Int) :
    Real.sqrt x ∈ sqrt I prec := by
  simp only [sqrt, mem_def, Dyadic.max_toRat, Dyadic.toRat_ofInt]
  have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
  constructor
  · -- Lower bound: 0 ≤ sqrt(x)
    simp only [hz, Rat.cast_zero]
    exact Real.sqrt_nonneg x
  · -- Upper bound: sqrt(x) ≤ max(hi, 1)
    have hhi_ge : x ≤ (I.hi.toRat : ℝ) := hx.2
    calc Real.sqrt x
        ≤ max x 1 := sqrt_le_max_one hx_nn
      _ ≤ max (I.hi.toRat : ℝ) 1 := max_le_max_right 1 hhi_ge
      _ = (↑(max I.hi.toRat 1) : ℝ) := by simp [Rat.cast_max]

/-- General soundness of interval sqrt for any real input.
    Handles both non-negative inputs and negative inputs (where Real.sqrt returns 0). -/
theorem mem_sqrt' {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (prec : Int) :
    Real.sqrt x ∈ sqrt I prec := by
  rcases le_or_gt 0 x with hx_nn | hx_neg
  · -- Non-negative case
    exact mem_sqrt hx hx_nn prec
  · -- Negative case: sqrt(x) = 0 for x < 0
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hx_neg)
    simp only [sqrt, mem_def, Dyadic.max_toRat, Dyadic.toRat_ofInt, hsqrt_zero]
    have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
    simp only [hz, Rat.cast_zero, Rat.cast_max]
    constructor
    · norm_num
    · apply le_max_of_le_right
      norm_num

/-! ### Comparison and Containment -/

/-- Check if interval contains zero -/
def containsZero (I : IntervalDyadic) : Bool :=
  Dyadic.le I.lo Dyadic.zero && Dyadic.le Dyadic.zero I.hi

/-- Check if entire interval is positive -/
def isPositive (I : IntervalDyadic) : Bool :=
  Dyadic.lt Dyadic.zero I.lo

/-- Check if entire interval is negative -/
def isNegative (I : IntervalDyadic) : Bool :=
  Dyadic.lt I.hi Dyadic.zero

/-- Check if I ⊆ J -/
def subset (I J : IntervalDyadic) : Bool :=
  Dyadic.le J.lo I.lo && Dyadic.le I.hi J.hi

/-- Check if the upper bound is ≤ a rational -/
def upperBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  I.hi.toRat ≤ q

/-- Check if a rational is ≤ the lower bound -/
def lowerBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  q ≤ I.lo.toRat

/-- Upper bound extraction from membership -/
theorem le_hi_of_mem {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    x ≤ (I.hi.toRat : ℝ) := hx.2

/-- Lower bound extraction from membership -/
theorem lo_le_of_mem {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    (I.lo.toRat : ℝ) ≤ x := hx.1

/-- What upperBoundedBy means: the interval's hi endpoint is ≤ q -/
theorem upperBoundedBy_spec {I : IntervalDyadic} {q : ℚ}
    (h : I.upperBoundedBy q = true) : (I.hi.toRat : ℝ) ≤ q := by
  simp only [upperBoundedBy, decide_eq_true_eq] at h
  exact_mod_cast h

/-- What lowerBoundedBy means: q is ≤ the interval's lo endpoint -/
theorem lowerBoundedBy_spec {I : IntervalDyadic} {q : ℚ}
    (h : I.lowerBoundedBy q = true) : (q : ℝ) ≤ I.lo.toRat := by
  simp only [lowerBoundedBy, decide_eq_true_eq] at h
  exact_mod_cast h

/-! ### Helper for Transcendentals -/

/-- Convert from IntervalRat (for transcendental results) -/
def ofIntervalRat (I : IntervalRat) (prec : Int := -53) : IntervalDyadic :=
  -- Convert Rat endpoints to Dyadic with outward rounding
  -- For simplicity, we use a conservative conversion
  let lo := Dyadic.ofInt (Int.floor (I.lo * (2 ^ (-prec).toNat)))
  let loD := lo.scale2 prec
  let hi := Dyadic.ofInt (Int.ceil (I.hi * (2 ^ (-prec).toNat)))
  let hiD := hi.scale2 prec
  ⟨loD, hiD, by
    -- Need: loD.toRat ≤ hiD.toRat
    -- loD.toRat = floor(I.lo * 2^n) * 2^prec
    -- hiD.toRat = ceil(I.hi * 2^n) * 2^prec
    -- This follows from: floor(I.lo * 2^n) ≤ ceil(I.hi * 2^n)
    -- Which is: floor(I.lo * 2^n) ≤ I.lo * 2^n ≤ I.hi * 2^n ≤ ceil(I.hi * 2^n)
    apply Dyadic.toRat_scale2_le_scale2
    rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    have hle : I.lo ≤ I.hi := I.le
    have hscale_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num : (0 : ℚ) < 2) _
    calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ)
        ≤ I.lo * (2 : ℚ) ^ (-prec).toNat := Int.floor_le _
      _ ≤ I.hi * (2 : ℚ) ^ (-prec).toNat := mul_le_mul_of_nonneg_right hle (le_of_lt hscale_pos)
      _ ≤ ⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ := Int.le_ceil _⟩

/-- If x ∈ IntervalRat I, then x ∈ ofIntervalRat I prec (outward rounding preserves membership).
    Requires precision ≤ 0 (e.g. -53). -/
theorem mem_ofIntervalRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (prec : Int)
    (hprec : prec ≤ 0 := by norm_num) :
    x ∈ ofIntervalRat I prec := by
  -- The conversion uses floor/ceil which provides outward rounding:
  -- floor(lo * 2^n) * 2^(-n) ≤ lo ≤ x ≤ hi ≤ ceil(hi * 2^n) * 2^(-n)
  -- This follows from floor(a) ≤ a and a ≤ ceil(a), combined with
  -- the fact that multiplying by 2^(-n) when prec = -n cancels the 2^n factor.
  simp only [mem_def, ofIntervalRat, IntervalRat.mem_def] at *
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num) _
  have hfloor : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) ≤ I.lo * (2 : ℚ) ^ (-prec).toNat :=
    Int.floor_le _
  have hceil : I.hi * (2 : ℚ) ^ (-prec).toNat ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) :=
    Int.le_ceil _
  have hzpow_pos : (0 : ℚ) < (2 : ℚ) ^ prec := zpow_pos (by norm_num) _
  -- Key: 2^(-prec).toNat * 2^prec = 1 when prec ≤ 0 (so (-prec).toNat = -prec)
  have hcancel : (2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec = 1 := by
    set n := (-prec).toNat with hn_def
    have hprec_eq : prec = -(n : ℤ) := by omega
    rw [hprec_eq, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (ne_of_gt h2n_pos)
  constructor
  · -- Lower bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec ≤ I.lo := by
      calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec
          ≤ (I.lo * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hfloor (le_of_lt hzpow_pos)
        _ = I.lo * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by ring
        _ = I.lo * 1 := by rw [hcancel]
        _ = I.lo := by ring
    exact le_trans (by exact_mod_cast hle) hx.1
  · -- Upper bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : I.hi ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
      calc I.hi = I.hi * 1 := by ring
        _ = I.hi * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by rw [hcancel]
        _ = (I.hi * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by ring
        _ ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hceil (le_of_lt hzpow_pos)
    exact le_trans hx.2 (by exact_mod_cast hle)

end IntervalDyadic
end LeanCert.Core

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Intervals with Real Endpoints

This file defines `IntervalReal`, an interval type with real (ℝ) endpoints.
Unlike `IntervalRat` (which has rational endpoints and is suitable for computation),
`IntervalReal` allows us to represent intervals involving transcendental values
like `[1, Real.exp 1]` or `[Real.log 2, π]`.

## Main definitions

* `IntervalReal` - Intervals with real endpoints
* `expInterval` - Interval bound for exp
* `logInterval` - Interval bound for log (on positive intervals)

## Main theorems

* `mem_expInterval` - FTIA for exp: if x ∈ I, then exp(x) ∈ expInterval(I)

## Design notes

This type complements `IntervalRat` for proving facts about transcendental functions.
While `IntervalRat` is used for numerical computation (since rationals are computable),
`IntervalReal` is used for correctness proofs involving exp, log, etc.

Typical workflow:
1. Use `IntervalRat` for actual interval arithmetic computations
2. Convert to `IntervalReal` when proving facts about transcendental functions
3. Use mathlib's analysis lemmas directly on real intervals
-/

public section

namespace LeanCert.Core

/-- An interval with real endpoints -/
structure IntervalReal where
  /-- Lower endpoint of the interval. -/
  lo : ℝ
  /-- Upper endpoint of the interval. -/
  hi : ℝ
  le : lo ≤ hi

namespace IntervalReal

/-- The set of reals contained in this interval -/
def toSet (I : IntervalReal) : Set ℝ := Set.Icc I.lo I.hi

/-- Membership in an interval -/
instance : Membership ℝ IntervalReal where
  mem I x := I.lo ≤ x ∧ x ≤ I.hi

@[simp]
theorem mem_def (x : ℝ) (I : IntervalReal) : x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi :=
  Iff.rfl

theorem mem_toSet_iff (x : ℝ) (I : IntervalReal) : x ∈ I.toSet ↔ x ∈ I := by
  simp only [toSet, Set.mem_Icc, mem_def]

/-- Create an interval from a single real -/
def singleton (r : ℝ) : IntervalReal := ⟨r, r, le_refl r⟩

theorem mem_singleton (r : ℝ) : r ∈ singleton r := ⟨le_refl r, le_refl r⟩

/-- Convert from IntervalRat to IntervalReal -/
def ofRat (I : IntervalRat) : IntervalReal where
  lo := I.lo
  hi := I.hi
  le := by exact_mod_cast I.le

theorem mem_ofRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : x ∈ ofRat I := by
  simp only [mem_def, ofRat] at *
  exact hx

/-! ### Interval addition -/

/-- Add two intervals -/
def add (I J : IntervalReal) : IntervalReal where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le := by linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalReal} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add]
  constructor <;> linarith

/-! ### Interval negation -/

/-- Negate an interval -/
def neg (I : IntervalReal) : IntervalReal where
  lo := -I.hi
  hi := -I.lo
  le := by linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalReal} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg]
  constructor <;> linarith

/-! ### Interval multiplication -/

/-- The minimum of four real endpoints, used for interval multiplication. -/
def min4 (a b c d : ℝ) : ℝ := min (min a b) (min c d)
/-- The maximum of four real endpoints, used for interval multiplication. -/
def max4 (a b c d : ℝ) : ℝ := max (max a b) (max c d)

/-- Multiply two intervals -/
def mul (I J : IntervalReal) : IntervalReal where
  lo := min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  hi := max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  le := by
    simp only [min4, max4]
    exact le_trans (min_le_of_left_le (min_le_left _ _))
                   (le_max_of_le_left (le_max_left _ _))

/-! ### Exponential interval -/

/-- Interval bound for exp.
    Since exp is strictly increasing, exp([a,b]) = [exp(a), exp(b)]. -/
noncomputable def expInterval (I : IntervalReal) : IntervalReal where
  lo := Real.exp I.lo
  hi := Real.exp I.hi
  le := Real.exp_le_exp.mpr I.le

/-- FTIA for exp: if x ∈ [a,b], then exp(x) ∈ [exp(a), exp(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_expInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.exp x ∈ expInterval I := by
  simp only [mem_def] at *
  simp only [expInterval]
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-! ### Logarithm interval (for positive intervals) -/

/-- An interval that is strictly positive -/
structure IntervalRealPos extends IntervalReal where
  lo_pos : 0 < toIntervalReal.lo

/-- Interval bound for log on positive intervals.
    Since log is strictly increasing on (0, ∞), log([a,b]) = [log(a), log(b)] for a > 0. -/
noncomputable def logInterval (I : IntervalRealPos) : IntervalReal where
  lo := Real.log I.lo
  hi := Real.log I.hi
  le := Real.log_le_log I.lo_pos I.le

/-- FTIA for log: if x ∈ [a,b] with a > 0, then log(x) ∈ [log(a), log(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_logInterval {x : ℝ} {I : IntervalRealPos} (hx : x ∈ I.toIntervalReal) :
    Real.log x ∈ logInterval I := by
  simp only [mem_def] at *
  simp only [logInterval]
  have hx_pos : 0 < x := lt_of_lt_of_le I.lo_pos hx.1
  constructor
  · exact Real.log_le_log I.lo_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-! ### Trigonometric intervals (global bounds) -/

/-- Interval bound for sin. Since |sin x| ≤ 1 for all x, we use [-1, 1]. -/
def sinInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-1, 1, by norm_num⟩

/-- FTIA for sin -/
theorem mem_sinInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.sin x ∈ sinInterval I := by
  simp only [mem_def, sinInterval]
  have h := Real.sin_mem_Icc x
  simp only [Set.mem_Icc] at h
  exact h

/-- Interval bound for cos. Since |cos x| ≤ 1 for all x, we use [-1, 1]. -/
def cosInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-1, 1, by norm_num⟩

/-- FTIA for cos -/
theorem mem_cosInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.cos x ∈ cosInterval I := by
  simp only [mem_def, cosInterval]
  have h := Real.cos_mem_Icc x
  simp only [Set.mem_Icc] at h
  exact h

/-- Interval bound for atan. Since arctan x ∈ (-π/2, π/2) ⊂ [-2, 2] for all x. -/
def atanInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-2, 2, by norm_num⟩

/-- FTIA for atan -/
theorem mem_atanInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.arctan x ∈ atanInterval I := by
  simp only [mem_def, atanInterval]
  constructor
  · have := Real.neg_pi_div_two_lt_arctan x
    have hpi : Real.pi < 4 := Real.pi_lt_four
    linarith
  · have := Real.arctan_lt_pi_div_two x
    have hpi : Real.pi < 4 := Real.pi_lt_four
    linarith

/-- The derivative of arsinh is bounded by 1: |arsinh'(x)| = 1/√(1+x²) ≤ 1 -/
private theorem arsinh_deriv_abs_le_one (x : ℝ) : |deriv Real.arsinh x| ≤ 1 := by
  have hderiv : deriv Real.arsinh x = (Real.sqrt (1 + x ^ 2))⁻¹ :=
    (Real.hasDerivAt_arsinh x).deriv
  rw [hderiv]
  have hsqrt_ge_one : Real.sqrt (1 + x ^ 2) ≥ 1 := by
    have h1 : 1 + x ^ 2 ≥ 1 := by nlinarith [sq_nonneg x]
    calc Real.sqrt (1 + x ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hsqrt_pos : 0 < Real.sqrt (1 + x ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg x]
  rw [abs_inv, abs_of_pos hsqrt_pos]
  exact inv_le_one_of_one_le₀ hsqrt_ge_one

/-- |arsinh x| ≤ |x| for all x. This follows from MVT and |arsinh'| ≤ 1. -/
theorem abs_arsinh_le_abs (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · -- Case x ≥ 0: arsinh x ≥ 0 by monotonicity of arsinh
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · -- x = 0
      simp [Real.arsinh_zero]
    · -- x > 0
      have harsinh_nonneg : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr (le_of_lt hx_pos)
      have hcont : ContinuousOn Real.arsinh (Set.Icc 0 x) :=
        Real.continuous_arsinh.continuousOn
      have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 x) :=
        Real.differentiable_arsinh.differentiableOn
      obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_pos hcont hdiff
      simp only [Real.arsinh_zero, sub_zero] at hc_eq
      have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
      rw [abs_of_nonneg harsinh_nonneg, abs_of_pos hx_pos]
      have heq : Real.arsinh x = deriv Real.arsinh c * x := by rw [hc_eq]; field_simp
      calc Real.arsinh x = deriv Real.arsinh c * x := heq
        _ ≤ |deriv Real.arsinh c * x| := le_abs_self _
        _ = |deriv Real.arsinh c| * |x| := abs_mul _ _
        _ ≤ 1 * x := by rw [abs_of_pos hx_pos]; nlinarith [abs_nonneg x, hderiv_bound]
        _ = x := one_mul _
  · -- Case x < 0: use oddness arsinh(-x) = -arsinh(x)
    have hx_neg : -x > 0 := by linarith
    -- For x < 0, arsinh x < 0 (arsinh is strictly increasing, arsinh 0 = 0)
    have harsinh_neg : Real.arsinh x < 0 := Real.arsinh_neg_iff.mpr hx
    have harsinh_neg_nonneg : 0 ≤ Real.arsinh (-x) := Real.arsinh_nonneg_iff.mpr (by linarith)
    -- Use the positive case on -x
    have hcont : ContinuousOn Real.arsinh (Set.Icc 0 (-x)) :=
      Real.continuous_arsinh.continuousOn
    have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 (-x)) :=
      Real.differentiable_arsinh.differentiableOn
    obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_neg hcont hdiff
    simp only [Real.arsinh_zero, sub_zero] at hc_eq
    have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
    rw [abs_of_neg harsinh_neg, abs_of_neg hx]
    have heq : Real.arsinh (-x) = deriv Real.arsinh c * (-x) := by
      have hne : (-x) ≠ 0 := ne_of_gt hx_neg
      have : deriv Real.arsinh c * (-x) = (Real.arsinh (-x) / (-x)) * (-x) := by rw [hc_eq]
      rw [this, div_mul_cancel₀ _ hne]
    calc -Real.arsinh x = Real.arsinh (-x) := by rw [Real.arsinh_neg]
      _ = deriv Real.arsinh c * (-x) := heq
      _ ≤ |deriv Real.arsinh c * (-x)| := le_abs_self _
      _ = |deriv Real.arsinh c| * |-x| := abs_mul _ _
      _ ≤ 1 * (-x) := by rw [abs_of_pos hx_neg]; nlinarith [abs_nonneg (-x), hderiv_bound]
      _ = -x := one_mul _

/-- Interval bound for arsinh. Uses a conservative bound based on input interval. -/
def arsinhInterval (I : IntervalReal) : IntervalReal :=
  -- arsinh is monotonic, so we just apply it to endpoints
  -- Using conservative bound: |arsinh x| ≤ |x|, plus margin of 1 for safety
  let bound := max (|I.lo|) (|I.hi|) + 1
  ⟨-bound, bound, by
    have h3 : (0 : ℝ) ≤ max (|I.lo|) (|I.hi|) := le_max_of_le_left (abs_nonneg I.lo)
    change -(max (|I.lo|) (|I.hi|) + 1) ≤ max (|I.lo|) (|I.hi|) + 1
    linarith⟩

/-- FTIA for arsinh -/
theorem mem_arsinhInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.arsinh x ∈ arsinhInterval I := by
  unfold arsinhInterval
  simp only [mem_def]
  have habs : |Real.arsinh x| ≤ max (|I.lo|) (|I.hi|) + 1 := by
    have h1 : |Real.arsinh x| ≤ |x| := abs_arsinh_le_abs x
    have h2 : |x| ≤ max (|I.lo|) (|I.hi|) := by
      simp only [IntervalReal.mem_def] at hx
      rcases le_or_gt x 0 with hxneg | hxpos
      · rw [abs_of_nonpos hxneg]
        calc -x ≤ -I.lo := by linarith [hx.1]
          _ ≤ |I.lo| := neg_le_abs I.lo
          _ ≤ max (|I.lo|) (|I.hi|) := le_max_left _ _
      · rw [abs_of_pos hxpos]
        calc x ≤ I.hi := hx.2
          _ ≤ |I.hi| := le_abs_self I.hi
          _ ≤ max (|I.lo|) (|I.hi|) := le_max_right _ _
    linarith
  constructor
  · have := neg_abs_le (Real.arsinh x)
    linarith
  · have := le_abs_self (Real.arsinh x)
    linarith

/-! ### Hyperbolic function intervals -/

/-- Interval bound for sinh.
    Since sinh is strictly monotonic increasing, sinh([a,b]) = [sinh(a), sinh(b)]. -/
noncomputable def sinhInterval (I : IntervalReal) : IntervalReal where
  lo := Real.sinh I.lo
  hi := Real.sinh I.hi
  le := Real.sinh_le_sinh.mpr I.le

/-- FTIA for sinh: if x ∈ [a,b], then sinh(x) ∈ [sinh(a), sinh(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_sinhInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.sinh x ∈ sinhInterval I := by
  simp only [mem_def] at *
  simp only [sinhInterval]
  exact ⟨Real.sinh_le_sinh.mpr hx.1, Real.sinh_le_sinh.mpr hx.2⟩

/-- Interval bound for cosh.
    cosh is convex with minimum at 0:
    - If interval is all non-negative: cosh is increasing
    - If interval is all non-positive: cosh is decreasing
    - If interval contains 0: minimum is cosh(0) = 1, max is at endpoints -/
noncomputable def coshInterval (I : IntervalReal) : IntervalReal :=
  if h1 : 0 ≤ I.lo then
    -- Interval is [a,b] with 0 ≤ a: cosh increasing, so [cosh(a), cosh(b)]
    -- Since 0 ≤ a ≤ b, we have |a| ≤ |b|, so cosh(a) ≤ cosh(b)
    ⟨Real.cosh I.lo, Real.cosh I.hi, by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 I.le)]
      exact I.le⟩
  else if h2 : I.hi ≤ 0 then
    -- Interval is [a,b] with b ≤ 0: cosh decreasing, so [cosh(b), cosh(a)]
    -- Since a ≤ b ≤ 0, we have |b| ≤ |a|, so cosh(b) ≤ cosh(a)
    ⟨Real.cosh I.hi, Real.cosh I.lo, by
      rw [Real.cosh_le_cosh]
      have hlo_neg : I.lo < 0 := not_le.mp h1
      rw [abs_of_nonpos h2, abs_of_nonpos (le_of_lt hlo_neg)]
      linarith [I.le]⟩
  else
    -- Interval contains 0: min is 1, max is max(cosh(lo), cosh(hi))
    ⟨1, max (Real.cosh I.lo) (Real.cosh I.hi), by
      have h := Real.one_le_cosh I.lo
      exact le_trans h (le_max_left _ _)⟩

/-- FTIA for cosh: if x ∈ [a,b], then cosh(x) ∈ coshInterval([a,b]).
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_coshInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.cosh x ∈ coshInterval I := by
  simp only [mem_def] at hx
  unfold coshInterval
  split_ifs with h1 h2
  · -- Case: 0 ≤ I.lo (cosh increasing on [0, ∞))
    simp only [mem_def]
    have hx_nonneg : 0 ≤ x := le_trans h1 hx.1
    constructor
    · rw [Real.cosh_le_cosh, abs_of_nonneg h1, abs_of_nonneg hx_nonneg]
      exact hx.1
    · rw [Real.cosh_le_cosh, abs_of_nonneg hx_nonneg, abs_of_nonneg (le_trans h1 I.le)]
      exact hx.2
  · -- Case: I.hi ≤ 0 (cosh decreasing on (-∞, 0])
    simp only [mem_def]
    have hx_nonpos : x ≤ 0 := le_trans hx.2 h2
    have hlo_neg : I.lo < 0 := not_le.mp h1
    constructor
    · rw [Real.cosh_le_cosh, abs_of_nonpos h2, abs_of_nonpos hx_nonpos]
      linarith
    · rw [Real.cosh_le_cosh, abs_of_nonpos hx_nonpos, abs_of_nonpos (le_of_lt hlo_neg)]
      linarith
  · -- Case: interval contains 0
    simp only [mem_def]
    push Not at h1 h2
    constructor
    · exact Real.one_le_cosh x
    · -- cosh(x) ≤ max(cosh(lo), cosh(hi))
      by_cases! hx0 : 0 ≤ x
      · -- x ≥ 0: cosh(x) ≤ cosh(hi) since |x| ≤ |hi|
        have hle : Real.cosh x ≤ Real.cosh I.hi := by
          rw [Real.cosh_le_cosh, abs_of_nonneg hx0, abs_of_pos h2]
          exact hx.2
        exact le_trans hle (le_max_right _ _)
      · -- x < 0: cosh(x) ≤ cosh(lo) since |x| ≤ |lo|
        have hx_nonpos : x ≤ 0 := le_of_lt hx0
        have hle : Real.cosh x ≤ Real.cosh I.lo := by
          rw [Real.cosh_le_cosh, abs_of_nonpos hx_nonpos, abs_of_neg h1]
          linarith
        exact le_trans hle (le_max_left _ _)

/-! ### Square root interval -/

/-- Interval bound for sqrt.
    For any interval I, sqrt(x) ∈ [0, max(hi, 1)] for x ∈ I.
    This is always sound because:
    - sqrt(x) ≥ 0 for all x (Mathlib convention: sqrt(negative) = 0)
    - sqrt(x) ≤ max(x, 1) for x ≥ 0, so sqrt(x) ≤ max(hi, 1) -/
noncomputable def sqrtInterval (I : IntervalReal) : IntervalReal where
  lo := 0
  hi := max I.hi 1
  le := le_max_of_le_right zero_le_one

/-- Helper: sqrt(x) ≤ max(x, 1) for x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  rcases le_or_gt x 1 with hle | hgt
  · -- x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
      _ ≤ max x 1 := le_max_right x 1
  · -- x > 1: sqrt(x) < x ≤ max(x, 1)
    have hx_pos : 0 < x := lt_trans zero_lt_one hgt
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_gt_one : 1 < Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    have hsqrt_lt : Real.sqrt x < x := by
      have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
      have h2 : Real.sqrt x * 1 < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_left hsqrt_gt_one hsqrt_pos
      simp only [mul_one] at h2
      linarith
    calc Real.sqrt x ≤ x := le_of_lt hsqrt_lt
      _ ≤ max x 1 := le_max_left x 1

/-- FTIA for sqrt: if x ∈ I, then sqrt(x) ∈ sqrtInterval(I).
    Works for all x including negative (where sqrt returns 0 by Mathlib convention). -/
theorem mem_sqrtInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtInterval I := by
  simp only [mem_def, sqrtInterval]
  constructor
  · exact Real.sqrt_nonneg x
  · rcases le_or_gt 0 x with hnn | hneg
    · -- x ≥ 0: sqrt(x) ≤ max(x, 1) ≤ max(hi, 1)
      calc Real.sqrt x ≤ max x 1 := sqrt_le_max_one hnn
        _ ≤ max I.hi 1 := max_le_max_right 1 hx.2
    · -- x < 0: sqrt(x) = 0 ≤ max(hi, 1)
      have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
      rw [hsqrt_zero]
      exact le_max_of_le_right zero_le_one

end IntervalReal

end LeanCert.Core

end

end

section

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Shared Trigonometric Range Reduction

Common rational `π` bounds and interval-shifting proofs used by IntervalRat and
Taylor-model trigonometric evaluators.
-/

/-! ### Rational approximations of π and 2π -/

public section

namespace LeanCert.Core.TrigReduction

open LeanCert.Core

/-- Lower bound for π: 314159265/100000000 < π -/
def piRatLo : ℚ := 314159265/100000000

/-- Upper bound for π: π < 355/113 -/
def piRatHi : ℚ := 355/113

/-- Lower bound for 2π -/
def twoPiRatLo : ℚ := 2 * piRatLo

/-- Upper bound for 2π -/
def twoPiRatHi : ℚ := 2 * piRatHi

/-- `piRatLo < π`, proved from Mathlib's decimal π bounds. -/
theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi := by
  have h₁ : (piRatLo : ℝ) < (3.14159265358979323846 : ℝ) := by
    norm_num [piRatLo]
  exact lt_trans h₁ Real.pi_gt_d20

/-- `π < piRatHi`, proved from Mathlib's decimal π bounds. -/
theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) := by
  have h₁ : (3.14159265358979323847 : ℝ) < (piRatHi : ℝ) := by
    norm_num [piRatHi]
  exact lt_trans Real.pi_lt_d20 h₁

/-- twoPiRatLo < 2π -/
theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi := by
  unfold twoPiRatLo
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := piRatLo_lt_pi
  linarith

/-- 2π < twoPiRatHi -/
theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) := by
  unfold twoPiRatHi
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := pi_lt_piRatHi
  linarith

/-- twoPiRatLo ≤ twoPiRatHi -/
theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi := by
  unfold twoPiRatLo twoPiRatHi piRatLo piRatHi
  norm_num

/-! ### Range reduction -/

/-- Compute the shift amount k such that I.midpoint - k * 2π is approximately in [-π, π]. -/
def computeShiftK (I : IntervalRat) : ℤ :=
  let mid := I.midpoint
  (mid / twoPiRatHi).floor

/-- Shift an interval by subtracting k * 2π using rational bounds. -/
def shiftInterval (I : IntervalRat) (k : ℤ) : IntervalRat :=
  if hk : k ≥ 0 then
    ⟨I.lo - k * twoPiRatHi, I.hi - k * twoPiRatLo,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hk_cast : (0 : ℚ) ≤ k := Int.cast_nonneg hk
         have h2 : (k : ℚ) * twoPiRatLo ≤ k * twoPiRatHi :=
           mul_le_mul_of_nonneg_left h1 hk_cast
         linarith [I.le]⟩
  else
    ⟨I.lo - k * twoPiRatLo, I.hi - k * twoPiRatHi,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hkneg : k < 0 := Int.not_le.mp hk
         have hk_cast : (k : ℚ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
         have h2 : (k : ℚ) * twoPiRatHi ≤ k * twoPiRatLo :=
           mul_le_mul_of_nonpos_left h1 hk_cast
         linarith [I.le]⟩

/-- Reduce interval to be approximately in [-π, π] by subtracting multiples of 2π. -/
def reduceToMainPeriod (I : IntervalRat) : IntervalRat × ℤ :=
  let k := computeShiftK I
  (shiftInterval I k, k)

/-! ### Correctness of range reduction -/

/-- If x ∈ I, then x - 2πk ∈ shiftInterval I k. -/
theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  simp only [IntervalRat.mem_def] at hx ⊢
  unfold shiftInterval
  split_ifs with hk
  · constructor
    · have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : 2 * Real.pi * k ≤ (twoPiRatHi : ℝ) * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : (twoPiRatLo : ℝ) * k ≤ 2 * Real.pi * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
  · have hkneg : k < 0 := Int.not_le.mp hk
    have hk_cast : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
    constructor
    · have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      have h3 : (k : ℝ) * (2 * Real.pi) ≤ k * twoPiRatLo :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      have h3 : (k : ℝ) * twoPiRatHi ≤ k * (2 * Real.pi) :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith

/-- Convenience form: if x ∈ I, then x - 2πk ∈ (reduceToMainPeriod I).1. -/
theorem mem_reduceToMainPeriod_of_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x - 2 * Real.pi * (reduceToMainPeriod I).2 ∈ (reduceToMainPeriod I).1 := by
  unfold reduceToMainPeriod
  exact mem_shiftInterval_of_mem hx

end LeanCert.Core.TrigReduction

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Computable Range Reduction for Trigonometric Functions

This file implements range reduction for sin and cos to improve Taylor series
convergence for intervals far from 0.

## Problem

Standard Taylor series for sin/cos centered at 0 have remainder bounds of
`|x|^{n+1} / (n+1)!`. For intervals far from 0 (e.g., [10, 11]), this remainder
is huge even for moderate n.

## Solution: Range Reduction

Use the periodicity of sin/cos:
- `sin(x) = sin(x - 2πk)` for any integer k
- `cos(x) = cos(x - 2πk)` for any integer k

By choosing k to bring x - 2πk into [-π, π], the Taylor series converges much
faster since |x - 2πk| ≤ π ≈ 3.14.

## Main definitions

* `twoPiRatLo`, `twoPiRatHi` - Rational bounds for 2π
* `reduceToMainPeriod` - Shift interval to be near 0
* `sinComputableReduced`, `cosComputableReduced` - Computable evaluation with range reduction
-/

/-! ### Shared range-reduction API -/

public section

namespace LeanCert.Core.IntervalRat

/-- The rational lower π bound from the trigonometric reduction implementation. -/
def piRatLo : ℚ := LeanCert.Core.TrigReduction.piRatLo
/-- The rational upper π bound from the trigonometric reduction implementation. -/
def piRatHi : ℚ := LeanCert.Core.TrigReduction.piRatHi
/-- The rational lower bound for twice π used in argument reduction. -/
def twoPiRatLo : ℚ := LeanCert.Core.TrigReduction.twoPiRatLo
/-- The rational upper bound for twice π used in argument reduction. -/
def twoPiRatHi : ℚ := LeanCert.Core.TrigReduction.twoPiRatHi
/-- Choose the integer number of periods used to reduce an input interval. -/
def computeShiftK : IntervalRat → ℤ := LeanCert.Core.TrigReduction.computeShiftK
/-- Shift an interval by the selected integer multiple of the period enclosure. -/
def shiftInterval : IntervalRat → ℤ → IntervalRat := LeanCert.Core.TrigReduction.shiftInterval
/-- Return the reduced interval and its integer period shift. -/
def reduceToMainPeriod : IntervalRat → IntervalRat × ℤ :=
  LeanCert.Core.TrigReduction.reduceToMainPeriod

theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi :=
  LeanCert.Core.TrigReduction.piRatLo_lt_pi

theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.pi_lt_piRatHi

theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_lt_two_pi

theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.two_pi_lt_twoPiRatHi

theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_le_twoPiRatHi

theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  change x - 2 * Real.pi * k ∈ LeanCert.Core.TrigReduction.shiftInterval I k
  exact LeanCert.Core.TrigReduction.mem_shiftInterval_of_mem hx

/-! ### Computable reduced evaluation -/

/-- Computable sin evaluation with range reduction. -/
def sinComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    sinComputable Ired n

/-- Computable cos evaluation with range reduction. -/
def cosComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    cosComputable Ired n

/-- sin x ∈ sinComputableReduced I for all x ∈ I -/
theorem mem_sinComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.sin x ∈ sinComputableReduced I n := by
  unfold sinComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hsin_eq : Real.sin x = Real.sin (x - 2 * Real.pi * k) := by
    have h := Real.sin_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · push Not at hwide
    rw [hsin_eq]
    exact mem_sinComputable hxred n

/-- cos x ∈ cosComputableReduced I for all x ∈ I -/
theorem mem_cosComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.cos x ∈ cosComputableReduced I n := by
  unfold cosComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hcos_eq : Real.cos x = Real.cos (x - 2 * Real.pi * k) := by
    have h := Real.cos_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · rw [hcos_eq]
    exact mem_cosComputable hxred n

end LeanCert.Core.IntervalRat

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Computable Interval Evaluation

This file implements the computable interval evaluator for `LeanCert.Core.Expr`.
Given an expression and intervals for its variables, we compute an interval
guaranteed to contain all possible values.

## Main definitions

* `IntervalEnv` - Variable assignment as intervals
* `EvalConfig` - Configuration for evaluation parameters (Taylor depth)
* `LeanCert.Internal.Rational.evalTotalCore` - Computable interval evaluator for core expressions
* `evalIntervalCore_correct` - Correctness theorem for core evaluation

## Design notes

This evaluator is COMPUTABLE, allowing use of `native_decide` for bound checking
in tactics. The transcendental functions (exp, sin, cos) use Taylor series with
configurable depth for precision control.

For inv: computes bounds using `invInterval`, but correctness is not covered by
`evalIntervalCore_correct`. Use `evalIntervalOption` for inv.
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

open LeanCert.Core

-- Re-export support predicates from Core for backward compatibility
export LeanCert.Core (ExprSupportedCore ADSupported)

/-! ### Interval bounds for transcendental functions -/

/-- Simple interval bound for sin.
    Since |sin x| ≤ 1 for all x, we use the global bound [-1, 1].
    This is sound but not tight. -/
@[expose]
def sinInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of sin interval: sin x ∈ [-1, 1] for all x -/
theorem mem_sinInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.sin x ∈ sinInterval I := by
  simp only [IntervalRat.mem_def, sinInterval]
  have h := Real.sin_mem_Icc x
  simp only [Set.mem_Icc] at h
  simp only [Rat.cast_neg, Rat.cast_one]
  exact h

/-- Simple interval bound for cos.
    Since |cos x| ≤ 1 for all x, we use the global bound [-1, 1].
    This is sound but not tight. -/
@[expose]
def cosInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of cos interval: cos x ∈ [-1, 1] for all x -/
theorem mem_cosInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.cos x ∈ cosInterval I := by
  simp only [IntervalRat.mem_def, cosInterval]
  have h := Real.cos_mem_Icc x
  simp only [Set.mem_Icc] at h
  simp only [Rat.cast_neg, Rat.cast_one]
  exact h

/-- Simple interval bound for atan.
    Since atan x ∈ (-π/2, π/2) for all x, we use the global bound [-2, 2].
    This is sound but not tight (π/2 ≈ 1.57). -/
@[expose]
def atanInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-2, 2, by norm_num⟩

/-- Correctness of atan interval: arctan x ∈ [-2, 2] for all x -/
theorem mem_atanInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.arctan x ∈ atanInterval I := by
  simp only [IntervalRat.mem_def, atanInterval, Rat.cast_neg, Rat.cast_ofNat]
  -- arctan x ∈ (-π/2, π/2), and π/2 < 2 since π < 4
  have h_lo : Real.arctan x > -Real.pi / 2 := by
    have := Real.neg_pi_div_two_lt_arctan x; linarith
  have h_hi : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have hpi_lt_four : Real.pi < 4 := Real.pi_lt_four
  have hpi_lo : -Real.pi / 2 > (-2 : ℝ) := by linarith
  have hpi_hi : Real.pi / 2 < (2 : ℝ) := by linarith
  constructor <;> linarith

/-- Interval bound for erf using computable Taylor series.
    erf(x) = (2/√π) * ∫₀ˣ exp(-t²) dt, strictly monotone increasing.
    This computes tight bounds using verified Taylor series. -/
def erfInterval (I : IntervalRat) (taylorDepth : ℕ := 15) : IntervalRat :=
  IntervalRat.erfComputable I taylorDepth

/-- Helper: The integral of exp(-t²) over (a, b] is positive when a < b.
    This follows from exp(-t²) > 0 and the interval having positive measure. -/
private theorem integral_exp_neg_sq_pos (a b : ℝ) (hab : a < b) :
    0 < ∫ t in a..b, Real.exp (-(t^2)) := by
  have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
    Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
  apply intervalIntegral.integral_pos hab hcont.continuousOn
  · intro x _; exact le_of_lt (Real.exp_pos _)
  · exact ⟨a, Set.left_mem_Icc.mpr (le_of_lt hab), Real.exp_pos _⟩

/-- erf is strictly monotone increasing.
    Proof: erf'(x) = (2/√π) * exp(-x²) > 0 for all x.

    We use that for a < b, the integral ∫_{a}^{b} exp(-t²) dt > 0 since the
    integrand is strictly positive. -/
theorem Real.strictMono_erf : StrictMono Real.erf := by
  intro a b hab
  unfold Real.erf
  have hfactor : (0 : ℝ) < 2 / Real.sqrt Real.pi := by
    apply div_pos (by norm_num : (0 : ℝ) < 2)
    exact Real.sqrt_pos.mpr Real.pi_pos
  have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
    Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
  have hint : ∀ c d : ℝ, IntervalIntegrable (fun t => Real.exp (-(t^2))) MeasureTheory.volume c d :=
    fun c d => hcont.intervalIntegrable c d
  -- The integral ∫ t in a..b, exp(-t²) > 0 when a < b since exp(-t²) > 0
  have hpos : 0 < ∫ x in a..b, Real.exp (-(x^2)) := integral_exp_neg_sq_pos a b hab
  -- Split integral: ∫ 0..b = ∫ 0..a + ∫ a..b
  have heq := (intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)).symm
  -- Since ∫ a..b > 0, we have ∫ 0..a < ∫ 0..a + ∫ a..b = ∫ 0..b
  have hineq : ∫ x in (0 : ℝ)..a, Real.exp (-(x^2)) < ∫ x in (0 : ℝ)..b, Real.exp (-(x^2)) := by
    rw [heq]
    linarith
  -- Multiply both sides by positive factor
  exact mul_lt_mul_of_pos_left hineq hfactor

/-- Quantitative global bound: `|erf x| ≤ (2257/2000) * |x|`.
    This is conservative but fully proved from the integral definition. -/
private theorem Real.abs_erf_le_2257_div_2000_mul_abs (x : ℝ) :
    |Real.erf x| ≤ ((2257 : ℝ) / 2000) * |x| := by
  unfold Real.erf
  have h_int :
      ‖∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))‖ ≤ |x| := by
    have hnorm :
        ∀ t ∈ Set.uIoc (0 : ℝ) x, ‖Real.exp (-(t ^ 2))‖ ≤ (1 : ℝ) := by
      intro t _ht
      have hsq : 0 ≤ t ^ 2 := sq_nonneg t
      have hle : Real.exp (-(t ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hnonneg : 0 ≤ Real.exp (-(t ^ 2)) := le_of_lt (Real.exp_pos _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := x) (C := (1 : ℝ)) (f := fun t => Real.exp (-(t ^ 2))) hnorm
    simpa [one_mul, sub_zero] using h
  have hfactor_nonneg : 0 ≤ 2 / Real.sqrt Real.pi := by
    exact div_nonneg (by norm_num) (le_of_lt (Real.sqrt_pos.mpr Real.pi_pos))
  have hsqrt_ge_17724 : (17724 / 10000 : ℝ) ≤ Real.sqrt Real.pi := by
    have hpi_ge : (3.1415 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d4
    have hsq : (17724 / 10000 : ℝ) ^ 2 ≤ Real.pi := by
      have hcalc : (17724 / 10000 : ℝ) ^ 2 = 3.14140176 := by norm_num
      linarith
    have hnonneg : (0 : ℝ) ≤ (17724 / 10000 : ℝ) := by norm_num
    have hsqrt_sq : (17724 / 10000 : ℝ) = Real.sqrt ((17724 / 10000 : ℝ) ^ 2) := by
      symm; exact Real.sqrt_sq hnonneg
    calc
      (17724 / 10000 : ℝ) = Real.sqrt ((17724 / 10000 : ℝ) ^ 2) := hsqrt_sq
      _ ≤ Real.sqrt Real.pi := by exact Real.sqrt_le_sqrt hsq
  have hfactor_le_2257_div_2000 : 2 / Real.sqrt Real.pi ≤ ((2257 : ℝ) / 2000) := by
    have hmul : (2 : ℝ) ≤ ((2257 : ℝ) / 2000) * Real.sqrt Real.pi := by
      calc
        (2 : ℝ) ≤ ((2257 : ℝ) / 2000) * (17724 / 10000 : ℝ) := by norm_num
        _ ≤ ((2257 : ℝ) / 2000) * Real.sqrt Real.pi := by
              gcongr
    exact (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).2 hmul
  calc
    |(2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))|
        = (2 / Real.sqrt Real.pi) * ‖∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))‖ := by
            rw [abs_mul, abs_of_nonneg hfactor_nonneg, Real.norm_eq_abs]
    _ ≤ (2 / Real.sqrt Real.pi) * |x| := by
          gcongr
    _ ≤ ((2257 : ℝ) / 2000) * |x| := by
          nlinarith [hfactor_nonneg, hfactor_le_2257_div_2000, abs_nonneg x]

/-- Correctness of `erfPointComputable`.
    The enclosure is sign-aware and uses monotonicity of erf with `erf(0)=0`. -/
theorem mem_erfPointComputable (q : ℚ) (n : ℕ) :
    Real.erf q ∈ IntervalRat.erfPointComputable q n := by
  unfold IntervalRat.erfPointComputable
  have h_abs1 : |Real.erf q| ≤ (1 : ℝ) := by
    refine (abs_le.2 ?_)
    exact_mod_cast (Real.erf_mem_Icc q)
  have h_abs2 : |Real.erf q| ≤ ((2257 : ℝ) / 2000) * |(q : ℝ)| :=
    Real.abs_erf_le_2257_div_2000_mul_abs q
  by_cases hq : q < 0
  · simp only [hq, ↓reduceDIte, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_min, Rat.cast_one,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_abs, Rat.cast_zero]
    have hq_real : (q : ℝ) < 0 := by exact_mod_cast hq
    have herf_lt_erf0 : Real.erf q < Real.erf 0 := Real.strictMono_erf hq_real
    have herf_nonpos : Real.erf q ≤ 0 := by
      simpa [Real.erf] using le_of_lt herf_lt_erf0
    have hneg_min : -(min (1 : ℝ) (((2257 : ℝ) / 2000) * |(q : ℝ)|)) ≤ Real.erf q := by
      exact (abs_le.mp (le_min h_abs1 h_abs2)).1
    exact ⟨hneg_min, herf_nonpos⟩
  · by_cases h0 : q = 0
    · subst h0
      simp [IntervalRat.mem_def, Real.erf]
    · simp only [hq, ↓reduceDIte, h0, IntervalRat.mem_def, Rat.cast_zero,
        Rat.cast_min, Rat.cast_one,
      Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_abs, le_inf_iff]
      have hq_pos : 0 < q := lt_of_le_of_ne (le_of_not_gt hq) (by
        intro hz
        exact h0 hz.symm)
      have hq_pos_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
      have herf0_lt : Real.erf 0 < Real.erf q := Real.strictMono_erf hq_pos_real
      have herf_nonneg : 0 ≤ Real.erf q := by
        simpa [Real.erf] using le_of_lt herf0_lt
      exact ⟨herf_nonneg, (abs_le.mp h_abs1).2, (abs_le.mp h_abs2).2⟩

/-- Correctness of erf interval using monotonicity and endpoint evaluation.

    Since erf is strictly monotone increasing:
    - For x ∈ [I.lo, I.hi], we have erf(I.lo) ≤ erf(x) ≤ erf(I.hi)
    - erfPointComputable(I.lo) contains erf(I.lo)
    - erfPointComputable(I.hi) contains erf(I.hi)
    - hull of these intervals contains [erf(I.lo), erf(I.hi)]
    - Therefore erf(x) ∈ hull(...) ∩ [-1, 1] -/
theorem mem_erfInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 15) :
    Real.erf x ∈ erfInterval I n := by
  unfold erfInterval IntervalRat.erfComputable
  simp only []
  -- Get membership in endpoint intervals
  have hlo_mem := mem_erfPointComputable I.lo n
  have hhi_mem := mem_erfPointComputable I.hi n
  -- Use monotonicity
  have hx_bounds := hx
  rw [IntervalRat.mem_def] at hx_bounds
  have herf_lo : Real.erf I.lo ≤ Real.erf x :=
    Real.strictMono_erf.monotone hx_bounds.1
  have herf_hi : Real.erf x ≤ Real.erf I.hi :=
    Real.strictMono_erf.monotone hx_bounds.2
  -- erf x is in hull of endpoint intervals
  have h_in_hull : Real.erf x ∈ IntervalRat.hull
      (IntervalRat.erfPointComputable I.lo n) (IntervalRat.erfPointComputable I.hi n) := by
    rw [IntervalRat.mem_def] at hlo_mem hhi_mem ⊢
    unfold IntervalRat.hull
    simp only []
    constructor
    · calc (↑(min (IntervalRat.erfPointComputable I.lo n).lo
              (IntervalRat.erfPointComputable I.hi n).lo) : ℝ)
          ≤ (IntervalRat.erfPointComputable I.lo n).lo := by
            simp only [Rat.cast_min]; exact min_le_left _ _
        _ ≤ Real.erf I.lo := hlo_mem.1
        _ ≤ Real.erf x := herf_lo
    · calc Real.erf x
          ≤ Real.erf I.hi := herf_hi
        _ ≤ (IntervalRat.erfPointComputable I.hi n).hi := hhi_mem.2
        _ ≤ (↑(max (IntervalRat.erfPointComputable I.lo n).hi
              (IntervalRat.erfPointComputable I.hi n).hi) : ℝ) := by
            simp only [Rat.cast_max]; exact le_max_right _ _
  -- erf x is in [-1, 1]
  have h_global : Real.erf x ∈ ({lo := -1, hi := 1, le := by norm_num} : IntervalRat) := by
    simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc x
  -- Combine via case analysis on intersection result
  set erfLo := IntervalRat.erfPointComputable I.lo n
  set erfHi := IntervalRat.erfPointComputable I.hi n
  set raw := erfLo.hull erfHi
  set globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  -- Use mem_intersect which says: if x ∈ I and x ∈ J, then ∃ K, intersect I J = some K ∧ x ∈ K
  have ⟨K, hK_eq, hK_mem⟩ := IntervalRat.mem_intersect h_in_hull h_global
  simp only [hK_eq]
  exact hK_mem

/-- Simple interval bound for arsinh.
    arsinh is unbounded, so we use a very rough linear bound.
    We use max(|lo|, |hi|) + 1 as a safe bound that always works. -/
@[expose]
def arsinhInterval (I : IntervalRat) : IntervalRat :=
  let bound := max (abs I.lo) (abs I.hi) + 1
  ⟨-bound, bound, by
    have h1 : (0 : ℚ) ≤ |I.lo| := abs_nonneg I.lo
    have h2 : |I.lo| ≤ |I.lo| ⊔ |I.hi| := le_max_left _ _
    have h3 : (0 : ℚ) ≤ |I.lo| ⊔ |I.hi| := le_trans h1 h2
    have h4 : (0 : ℚ) ≤ |I.lo| ⊔ |I.hi| + 1 := by linarith
    have h5 : -(|I.lo| ⊔ |I.hi| + 1) ≤ |I.lo| ⊔ |I.hi| + 1 := by linarith
    exact h5⟩

/-- Correctness of arsinh interval.
    Uses the bound |arsinh x| ≤ |x| for all x (from IntervalRealEndpoints). -/
theorem mem_arsinhInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.arsinh x ∈ arsinhInterval I := by
  simp only [IntervalRat.mem_def, arsinhInterval]
  -- Key bound: |arsinh x| ≤ |x| + 1
  -- This is a well-known bound that follows from sinh y ≥ y for y ≥ 0
  have hbound : |Real.arsinh x| ≤ |x| + 1 := by
    -- Use the sharper bound |arsinh x| ≤ |x| from IntervalRealEndpoints
    have h := IntervalReal.abs_arsinh_le_abs x
    linarith
  simp only [IntervalRat.mem_def] at hx
  have hx_bound : |x| ≤ max (|I.lo|) (|I.hi|) := by
    simp only [Rat.cast_abs, Rat.cast_max]
    rcases le_or_gt x 0 with hxneg | hxpos
    · simp only [abs_of_nonpos hxneg]
      calc -x ≤ -(I.lo : ℝ) := by linarith [hx.1]
        _ ≤ |↑I.lo| := neg_le_abs _
        _ ≤ max |↑I.lo| |↑I.hi| := le_max_left _ _
    · simp only [abs_of_pos hxpos]
      calc x ≤ I.hi := hx.2
        _ ≤ |↑I.hi| := le_abs_self _
        _ ≤ max |↑I.lo| |↑I.hi| := le_max_right _ _
  have habs_lo : -(|x| + 1) ≤ Real.arsinh x := (abs_le.mp hbound).1
  have habs_hi : Real.arsinh x ≤ |x| + 1 := (abs_le.mp hbound).2
  have hmax_cast : (max (|I.lo|) (|I.hi|) : ℝ) = max |↑I.lo| |↑I.hi| := by
    rfl
  constructor
  · simp only [Rat.cast_neg, Rat.cast_add, Rat.cast_one, Rat.cast_max, Rat.cast_abs]
    have h1 : -(|↑I.lo| ⊔ |↑I.hi| + 1) = -(max |↑I.lo| |↑I.hi|) - (1 : ℝ) := by ring
    have h2 : -(max |↑I.lo| |↑I.hi|) - (1 : ℝ) ≤ -|x| - 1 := by
      have hxb : |x| ≤ max |↑I.lo| |↑I.hi| := by
        convert hx_bound using 1
        simp [Rat.cast_max, Rat.cast_abs]
      linarith
    have h3 : -|x| - (1 : ℝ) ≤ Real.arsinh x := by
      have : -(|x| + 1) = -|x| - 1 := by ring
      rw [← this]; exact habs_lo
    linarith
  · simp only [Rat.cast_add, Rat.cast_one, Rat.cast_max, Rat.cast_abs]
    have h1 : Real.arsinh x ≤ |x| + 1 := habs_hi
    have h2 : |x| + (1 : ℝ) ≤ max |↑I.lo| |↑I.hi| + 1 := by
      have hxb : |x| ≤ max |↑I.lo| |↑I.hi| := by
        convert hx_bound using 1
        simp [Rat.cast_max, Rat.cast_abs]
      linarith
    linarith

/-- Interval bound for atanh.
    atanh is defined for (-1, 1). If interval is within this range,
    we compute tight bounds using monotonicity. Otherwise returns default. -/
noncomputable def atanhInterval (I : IntervalRat) : IntervalRat :=
  if h : -1 < I.lo ∧ I.hi < 1 then
    let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, h.1, h.2⟩
    IntervalRat.atanhIntervalComputed Iball
  else
    default

/-- Correctness of atanh interval: when x ∈ I and I ⊂ (-1, 1), atanh(x) ∈ atanhInterval I. -/
theorem mem_atanhInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (hlo : -1 < I.lo) (hhi : I.hi < 1) :
    Real.atanh x ∈ atanhInterval I := by
  unfold atanhInterval
  simp only [hlo, hhi, and_self, ↓reduceDIte]
  let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, hlo, hhi⟩
  have hx_ball : x ∈ Iball := by
    simp only [Membership.mem]
    exact hx
  exact IntervalRat.mem_atanhIntervalComputed hx_ball

/-- Tight interval bound for tanh.
    Since tanh(x) ∈ (-1, 1) for all x ∈ ℝ, we use the global bound [-1, 1].
    This avoids the interval explosion that occurs when desugaring to exp. -/
def tanhInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of tanh interval: tanh x ∈ [-1, 1] for all x -/
theorem mem_tanhInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.tanh x ∈ tanhInterval I := by
  simp only [IntervalRat.mem_def, tanhInterval, Rat.cast_neg, Rat.cast_one]
  constructor
  -- tanh x ≥ -1 for all x: use that tanh = sinh/cosh and cosh > 0
  · rw [Real.tanh_eq_sinh_div_cosh]
    have hcosh : Real.cosh x > 0 := Real.cosh_pos x
    -- -1 ≤ sinh/cosh iff -cosh ≤ sinh (since cosh > 0)
    rw [le_div_iff₀ hcosh, neg_one_mul]
    -- Need: -cosh x ≤ sinh x
    -- sinh x = (exp x - exp(-x))/2, cosh x = (exp x + exp(-x))/2
    -- sinh x + cosh x = exp x ≥ 0 ✓
    rw [Real.sinh_eq, Real.cosh_eq]
    have h1 : Real.exp x > 0 := Real.exp_pos x
    linarith
  -- tanh x ≤ 1 for all x: use that sinh ≤ cosh (since exp(-x) > 0)
  · rw [Real.tanh_eq_sinh_div_cosh]
    have hcosh : Real.cosh x > 0 := Real.cosh_pos x
    rw [div_le_one₀ hcosh]
    -- Need: sinh x ≤ cosh x
    rw [Real.sinh_eq, Real.cosh_eq]
    have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith

/-- Interval enclosure for π.
    Uses tight bounds from Mathlib's pi_gt_d20 and pi_lt_d20 which give 20 decimal digits.
    3.14159265358979323846 < π < 3.14159265358979323847 -/
@[expose]
def piInterval : IntervalRat :=
  -- Use rational approximation: 31415926535897932/10000000000000000 ≤ pi ≤
  -- 31415926535897933/10000000000000000
  ⟨31415926535897932/10000000000000000, 31415926535897933/10000000000000000, by norm_num⟩

/-- Correctness of pi interval: Real.pi ∈ piInterval -/
theorem mem_piInterval : Real.pi ∈ piInterval := by
  simp only [IntervalRat.mem_def, piInterval]
  constructor
  · -- Lower bound from pi_gt_d20
    have h : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    have eq : (31415926535897932 : ℚ) / 10000000000000000 = (3.1415926535897932 : ℚ) := by norm_num
    simp only [Rat.cast_div, Rat.cast_ofNat] at *
    linarith
  · -- Upper bound from pi_lt_d20
    have h : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    have eq : (31415926535897933 : ℚ) / 10000000000000000 = (3.1415926535897933 : ℚ) := by norm_num
    simp only [Rat.cast_div, Rat.cast_ofNat] at *
    linarith

/-- Interval enclosure for the Euler–Mascheroni constant γ.
    Tight bounds derived from `eulerMascheroniSeq 100 < γ < eulerMascheroniSeq' 100`
    combined with explicit Taylor partial sums for `log`. The proofs below are
    axiom-free (no `native_decide`): all rational arithmetic is certified by
    `norm_num`, and the only analytic inputs are Mathlib's
    `abs_log_sub_add_sum_range_le` and the d9 bounds on `log 2`. -/
def eulerMascheroniInterval : IntervalRat :=
  ⟨5722/10000, 5823/10000, by norm_num⟩

/-- `harmonic 100` as an explicit rational literal. -/
private lemma harmonic_100_eq : harmonic 100 =
    14466636279520351160221518043104131447711/2788815009188499086581352357412492142272 := by
  norm_num [harmonic_succ, harmonic_zero]

/-- Series bound for `log (5/4) = -log (1 - 1/5)`: nine Taylor terms with the
    Mathlib tail estimate `|x|^(n+1)/(1-|x|)`. -/
private lemma log_five_quarter_approx :
    |Real.log (5/4) - 219656921/984375000| ≤ (1/7812500 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5 : ℝ))
    (by rw [abs_of_nonneg] <;> norm_num) 9
  have hsum : (∑ i ∈ Finset.range 9, (1/5 : ℝ) ^ (i + 1) / (i + 1)) = 219656921/984375000 := by
    simp [Finset.sum_range_succ]
    norm_num
  have hlog : Real.log (1 - 1/5) = -Real.log (5/4) := by
    rw [show (1 - 1/5 : ℝ) = (5/4)⁻¹ by norm_num, Real.log_inv]
  rw [hsum, hlog, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/5)] at h
  calc |Real.log (5/4) - 219656921/984375000|
      = |(219656921/984375000 : ℝ) + -Real.log (5/4)| := by rw [← abs_neg]; ring_nf
    _ ≤ (1/5 : ℝ) ^ 10 / (1 - 1/5) := h
    _ ≤ (1/7812500 : ℝ) := by norm_num

/-- Series bound for `log (101/100) = -log (1 - 1/101)`: three Taylor terms. -/
private lemma log_ratio_101_approx :
    |Real.log (101/100) - 61511/6181806| ≤ (1/103030100 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/101 : ℝ))
    (by rw [abs_of_nonneg] <;> norm_num) 3
  have hsum : (∑ i ∈ Finset.range 3, (1/101 : ℝ) ^ (i + 1) / (i + 1)) = 61511/6181806 := by
    simp [Finset.sum_range_succ]
    norm_num
  have hlog : Real.log (1 - 1/101) = -Real.log (101/100) := by
    rw [show (1 - 1/101 : ℝ) = (101/100)⁻¹ by norm_num, Real.log_inv]
  rw [hsum, hlog, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/101)] at h
  calc |Real.log (101/100) - 61511/6181806|
      = |(61511/6181806 : ℝ) + -Real.log (101/100)| := by rw [← abs_neg]; ring_nf
    _ ≤ (1/101 : ℝ) ^ 4 / (1 - 1/101) := h
    _ ≤ (1/103030100 : ℝ) := by norm_num

/-- Decompose `log 100` over `log 2` and `log (5/4)`: `100 = 2^6 * (5/4)^2`. -/
private lemma log_100_eq : Real.log 100 = 6 * Real.log 2 + 2 * Real.log (5/4) := by
  rw [show (100 : ℝ) = 2^6 * (5/4)^2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast; ring

/-- Decompose `log 101` as `log 100 + log (101/100)`. -/
private lemma log_101_eq :
    Real.log 101 = 6 * Real.log 2 + 2 * Real.log (5/4) + Real.log (101/100) := by
  rw [← log_100_eq, show (101 : ℝ) = 100 * (101/100) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  norm_num

/-- Helper: `5722/10000 ≤ harmonic 100 - log 101` via explicit series bounds. -/
private theorem eulerMascheroniSeq_100_ge :
    (5722/10000 : ℝ) ≤ Real.eulerMascheroniSeq 100 := by
  have h54 := log_five_quarter_approx
  have h101 := log_ratio_101_approx
  have hlog2 := Real.log_two_lt_d9
  have heq : Real.eulerMascheroniSeq 100 = ↑(harmonic 100 : ℚ) - Real.log 101 := by
    simp [Real.eulerMascheroniSeq]; ring_nf
  rw [heq, harmonic_100_eq, log_101_eq]
  rw [abs_le] at h54 h101
  push_cast
  linarith [h54.1, h54.2, h101.1, h101.2]

/-- Helper: `harmonic 100 - log 100 ≤ 5823/10000` via explicit series bounds. -/
private theorem eulerMascheroniSeq'_100_le :
    Real.eulerMascheroniSeq' 100 ≤ (5823/10000 : ℝ) := by
  have h54 := log_five_quarter_approx
  have hlog2 := Real.log_two_gt_d9
  have heq : Real.eulerMascheroniSeq' 100 = ↑(harmonic 100 : ℚ) - Real.log 100 := by
    simp [Real.eulerMascheroniSeq']
  rw [heq, harmonic_100_eq, log_100_eq]
  rw [abs_le] at h54
  push_cast
  linarith [h54.1, h54.2]

/-- Correctness of Euler–Mascheroni interval: γ ∈ eulerMascheroniInterval -/
theorem mem_eulerMascheroniInterval :
    Real.eulerMascheroniConstant ∈ eulerMascheroniInterval := by
  simp only [IntervalRat.mem_def, eulerMascheroniInterval]
  constructor
  · -- Lower: 5722/10000 ≤ eulerMascheroniSeq 100 < γ
    have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 100
    linarith [eulerMascheroniSeq_100_ge]
  · -- Upper: γ < eulerMascheroniSeq' 100 ≤ 5823/10000
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 100
    linarith [eulerMascheroniSeq'_100_le]

end LeanCert.Engine

namespace LeanCert.Core.MathConst
open LeanCert.Engine

/-- Centralized interval lookup for named mathematical constants.
    Extending this table is the ONLY change needed to add a new constant. -/
@[expose]
def interval : MathConst → IntervalRat
  | .pi => piInterval
  | .eulerMascheroni => eulerMascheroniInterval

/-- Correctness: the real value of every named constant is in its interval. -/
theorem mem_interval (c : MathConst) : c.toReal ∈ c.interval := by
  cases c with
  | pi => exact mem_piInterval
  | eulerMascheroni => exact mem_eulerMascheroniInterval

end LeanCert.Core.MathConst

namespace LeanCert.Engine
open LeanCert.Core

/-- Interval bound for sinh using computable Taylor series for exp.
    sinh(x) = (exp(x) - exp(-x)) / 2, and sinh is strictly monotonic.
    This computes tight bounds using the verified exp implementation. -/
@[expose]
def sinhInterval (I : IntervalRat) (taylorDepth : ℕ := 10) : IntervalRat :=
  IntervalRat.sinhComputable I taylorDepth

/-- Interval bound for cosh using computable Taylor series for exp.
    cosh(x) = (exp(x) + exp(-x)) / 2, with minimum 1 at x = 0.
    This computes tight bounds using the verified exp implementation. -/
@[expose]
def coshInterval (I : IntervalRat) (taylorDepth : ℕ := 10) : IntervalRat :=
  IntervalRat.coshComputable I taylorDepth

/-! ### Interval inverse -/

/-- Wide bound constant for when inverse is undefined (denominator contains 0) -/
def invWideBound : ℚ := 10^30

private theorem invWideBound_pos : (0 : ℝ) < invWideBound := by
  simp only [invWideBound]
  norm_num

/-- Computable interval inverse.
    For [a,b] with a > 0: returns [1/b, 1/a] (1/x is decreasing on positive reals)
    For [a,b] with b < 0: returns [1/b, 1/a] (1/x is decreasing on negative reals)
    For intervals containing 0: returns wide bounds [-M, M]. NOTE: this branch is
    NOT a sound enclosure of x⁻¹ in general (1/x is unbounded near 0); the
    correctness theorem `mem_invInterval` therefore requires the extra
    hypothesis `|x⁻¹| ≤ invWideBound` in that case. -/
def invInterval (I : IntervalRat) : IntervalRat :=
  if h : I.lo > 0 then
    -- Positive interval: 1/x is decreasing, so [1/b, 1/a]
    let invHi := 1 / I.lo
    let invLo := 1 / I.hi
    if hle : invLo ≤ invHi then { lo := invLo, hi := invHi, le := hle }
    else { lo := invHi, hi := invLo, le := by linarith }
  else if h' : I.hi < 0 then
    -- Negative interval: 1/x is decreasing, so [1/b, 1/a]
    let invHi := 1 / I.lo
    let invLo := 1 / I.hi
    if hle : invLo ≤ invHi then { lo := invLo, hi := invHi, le := hle }
    else { lo := invHi, hi := invLo, le := by linarith }
  else
    -- Interval contains zero: return wide bounds
    ⟨-invWideBound, invWideBound, by simp only [invWideBound]; norm_num⟩

/-- Correctness of invInterval when denominator interval is positive.
    For x ∈ [a,b] with a > 0, we have 1/x ∈ [1/b, 1/a] -/
theorem mem_invInterval_pos {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hpos : I.lo > 0) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def] at hx ⊢
  simp only [invInterval, hpos, ↓reduceDIte]
  -- x > 0 since x ≥ I.lo > 0
  have hx_pos : (x : ℝ) > 0 := by
    have h1 : (I.lo : ℝ) ≤ x := hx.1
    have h2 : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- For positive x: 1/b ≤ 1/x ≤ 1/a when a ≤ x ≤ b
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hlo_ne : (I.lo : ℝ) ≠ 0 := ne_of_gt hlo_pos
  have hhi_pos : (0 : ℝ) < I.hi := by
    have := I.le
    have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast this
    linarith
  have hhi_ne : (I.hi : ℝ) ≠ 0 := ne_of_gt hhi_pos
  split_ifs with hle
  · -- Case: 1/hi ≤ 1/lo (normal ordering)
    simp only [Rat.cast_inv, one_div]
    constructor
    · -- (I.hi)⁻¹ ≤ x⁻¹ follows from x ≤ I.hi
      exact (inv_le_inv₀ hhi_pos hx_pos).mpr hx.2
    · -- x⁻¹ ≤ (I.lo)⁻¹ follows from I.lo ≤ x
      exact (inv_le_inv₀ hx_pos hlo_pos).mpr hx.1
  · -- Case: 1/lo < 1/hi (impossible for positive lo ≤ hi, but we prove the goal anyway)
    -- 1/hi ≤ 1/lo is always true when lo ≤ hi and both positive
    have hhi_pos_q : (0 : ℚ) < I.hi := by
      have := I.le
      linarith
    have hle' : (1 : ℚ) / I.hi ≤ 1 / I.lo := by
      rw [div_le_div_iff₀ hhi_pos_q hpos]
      simp only [one_mul]
      exact I.le
    exact absurd hle' hle

/-- Correctness of invInterval when denominator interval is negative.
    For x ∈ [a,b] with b < 0, we have 1/x ∈ [1/b, 1/a] -/
theorem mem_invInterval_neg {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hneg : I.hi < 0) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def] at hx ⊢
  -- I.lo ≤ 0 since I.lo ≤ I.hi < 0
  have hlo_le : ¬(I.lo > 0) := by
    have := I.le
    have hhi_neg : I.hi < 0 := hneg
    intro h
    have : (I.lo : ℚ) ≤ I.hi := this
    linarith
  simp only [invInterval, hlo_le, ↓reduceDIte, hneg]
  -- x < 0 since x ≤ I.hi < 0
  have hx_neg : (x : ℝ) < 0 := by
    have h1 : x ≤ I.hi := hx.2
    have h2 : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  have hlo_neg : (I.lo : ℝ) < 0 := by
    have h1 : I.lo ≤ I.hi := I.le
    have h2 : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    have h3 : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast h1
    linarith
  have hhi_neg' : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
  -- For negative x: 1/x is still decreasing, so 1/b ≤ 1/x ≤ 1/a
  split_ifs with hle
  · simp only [Rat.cast_inv, one_div]
    constructor
    · -- (I.hi)⁻¹ ≤ x⁻¹ when x ≤ hi < 0 (since 1/x is decreasing for negatives)
      exact (inv_le_inv_of_neg hhi_neg' hx_neg).mpr hx.2
    · -- x⁻¹ ≤ (I.lo)⁻¹ when lo ≤ x < 0
      exact (inv_le_inv_of_neg hx_neg hlo_neg).mpr hx.1
  · -- Case: 1/lo < 1/hi (impossible for negative lo ≤ hi < 0)
    -- For negative numbers: lo ≤ hi < 0 implies 1/hi ≤ 1/lo
    -- Use: one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a
    have hle' : (1 : ℚ) / I.hi ≤ 1 / I.lo :=
      one_div_le_one_div_of_neg_of_le hneg I.le
    exact absurd hle' hle

/-- Correctness of invInterval when denominator interval contains zero.
    Requires a bound on |x⁻¹| to be provable, since x can be arbitrarily close to 0. -/
theorem mem_invInterval_wide {x : ℝ} {I : IntervalRat}
    (_hx : x ∈ I) (hlo : ¬(I.lo > 0)) (hhi : ¬(I.hi < 0))
    (hbnd : |x⁻¹| ≤ invWideBound) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def, invInterval, hlo, hhi, ↓reduceDIte]
  constructor
  · -- -invWideBound ≤ x⁻¹
    calc ((-invWideBound : ℚ) : ℝ) = -(invWideBound : ℝ) := by simp
      _ ≤ -|x⁻¹| := neg_le_neg hbnd
      _ ≤ x⁻¹ := neg_abs_le x⁻¹
  · -- x⁻¹ ≤ invWideBound
    calc x⁻¹ ≤ |x⁻¹| := le_abs_self x⁻¹
      _ ≤ (invWideBound : ℝ) := hbnd

/-- Main correctness theorem for invInterval.
    Fully proved for intervals bounded away from zero.
    For intervals containing zero, requires a bound on |x⁻¹|. -/
theorem mem_invInterval {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hbnd : |x⁻¹| ≤ invWideBound) :
    x⁻¹ ∈ invInterval I := by
  -- Case split based on the interval position
  by_cases hpos : I.lo > 0
  · exact mem_invInterval_pos hx hpos
  · by_cases hneg : I.hi < 0
    · exact mem_invInterval_neg hx hneg
    · exact mem_invInterval_wide hx hpos hneg hbnd

/-- Correctness of invInterval for intervals bounded away from zero (no extra hypothesis needed) -/
theorem mem_invInterval_nonzero {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hnonzero : I.lo > 0 ∨ I.hi < 0) :
    x⁻¹ ∈ invInterval I := by
  rcases hnonzero with hpos | hneg
  · exact mem_invInterval_pos hx hpos
  · exact mem_invInterval_neg hx hneg

/-! ### Core interval evaluation (computable) -/

/-- Variable assignment as intervals -/
abbrev IntervalEnv := Nat → IntervalRat

/-- Configuration for interval evaluation parameters.
    This allows certificates to specify the required precision. -/
structure EvalConfig where
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : ℕ := 10
  deriving Repr, DecidableEq

/-- Default evaluation configuration with 10 Taylor terms -/
instance : Inhabited EvalConfig := ⟨{ taylorDepth := 10 }⟩

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Internal total evaluator for the theorem-restricted core expression fragment.

    For expressions in `ExprSupportedCore`, this computes correct interval
    bounds with a fully-verified proof (given domain validity conditions).

    For inv: computes bounds using `invInterval`, but correctness is not
    covered by `evalIntervalCore_correct`. Use `evalIntervalOption` for inv.

    For log: uses `logComputable` with Taylor series. Correctness requires
    that the argument interval is positive (see `evalDomainValid`).

    This evaluator is COMPUTABLE, allowing use of `native_decide` for
    bound checking in tactics. The transcendental functions (exp, sin, cos, log)
    use Taylor series with configurable depth for precision control. -/
def evalTotalCore (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig := {}) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (LeanCert.Internal.Rational.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.Rational.evalTotalCore e₂ ρ cfg)
  | Expr.mul e₁ e₂ => IntervalRat.mul (LeanCert.Internal.Rational.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.Rational.evalTotalCore e₂ ρ cfg)
  | Expr.neg e => IntervalRat.neg (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  | Expr.inv e => invInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  | Expr.exp e => IntervalRat.expComputable (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.sin e => IntervalRat.sinComputableReduced (LeanCert.Internal.Rational.evalTotalCore e ρ
    cfg) cfg.taylorDepth
  | Expr.cos e => IntervalRat.cosComputableReduced (LeanCert.Internal.Rational.evalTotalCore e ρ
    cfg) cfg.taylorDepth
  | Expr.log e => IntervalRat.logComputable (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.atan e => atanInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  | Expr.arsinh e => arsinhInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  | Expr.atanh _ => default  -- Not in ExprSupportedCore; use evalIntervalOption for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf e => erfInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.sinh e => sinhInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.cosh e => coshInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.tanh e => tanhInterval (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  | Expr.sqrt e => IntervalRat.sqrtIntervalTightPrec (LeanCert.Internal.Rational.evalTotalCore e ρ
    cfg)
  | Expr.namedConst c => c.interval

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- A real environment is contained in an interval environment -/
@[expose]
def envMem (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_int i

/-- Domain validity predicate for expressions with domain restrictions.

    For log: requires the argument interval to be strictly positive.
    This ensures that logComputable returns correct bounds.

    For other expressions: always true (no domain restrictions). -/
def evalDomainValid (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValid e₁ ρ cfg ∧ evalDomainValid e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValid e₁ ρ cfg ∧ evalDomainValid e₂ ρ cfg
  | Expr.neg e => evalDomainValid e ρ cfg
  | Expr.inv e => evalDomainValid e ρ cfg  -- Note: inv correctness not covered anyway
  | Expr.exp e => evalDomainValid e ρ cfg
  | Expr.sin e => evalDomainValid e ρ cfg
  | Expr.cos e => evalDomainValid e ρ cfg
  | Expr.log e => evalDomainValid e ρ cfg ∧ (LeanCert.Internal.Rational.evalTotalCore e ρ cfg).lo
    > 0
  | Expr.atan e => evalDomainValid e ρ cfg
  | Expr.arsinh e => evalDomainValid e ρ cfg
  | Expr.atanh e => evalDomainValid e ρ cfg
  | Expr.sinc e => evalDomainValid e ρ cfg
  | Expr.erf e => evalDomainValid e ρ cfg
  | Expr.sinh e => evalDomainValid e ρ cfg
  | Expr.cosh e => evalDomainValid e ρ cfg
  | Expr.tanh e => evalDomainValid e ρ cfg
  | Expr.sqrt e => evalDomainValid e ρ cfg
  | Expr.namedConst _ => True

/-- Single-variable domain validity -/
@[expose]
def evalDomainValid1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Prop :=
  evalDomainValid e (fun _ => I) cfg

/-- Computable (decidable) check for domain validity -/
def checkDomainValid (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValid e₁ ρ cfg && checkDomainValid e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValid e₁ ρ cfg && checkDomainValid e₂ ρ cfg
  | Expr.neg e => checkDomainValid e ρ cfg
  | Expr.inv e => checkDomainValid e ρ cfg
  | Expr.exp e => checkDomainValid e ρ cfg
  | Expr.sin e => checkDomainValid e ρ cfg
  | Expr.cos e => checkDomainValid e ρ cfg
  | Expr.log e => checkDomainValid e ρ cfg && decide ((LeanCert.Internal.Rational.evalTotalCore e
    ρ cfg).lo > 0)
  | Expr.atan e => checkDomainValid e ρ cfg
  | Expr.arsinh e => checkDomainValid e ρ cfg
  | Expr.atanh e => checkDomainValid e ρ cfg
  | Expr.sinc e => checkDomainValid e ρ cfg
  | Expr.erf e => checkDomainValid e ρ cfg
  | Expr.sinh e => checkDomainValid e ρ cfg
  | Expr.cosh e => checkDomainValid e ρ cfg
  | Expr.tanh e => checkDomainValid e ρ cfg
  | Expr.sqrt e => checkDomainValid e ρ cfg
  | Expr.namedConst _ => true

/-- Single-variable domain check -/
def checkDomainValid1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  checkDomainValid e (fun _ => I) cfg

/-- checkDomainValid = true implies evalDomainValid -/
theorem checkDomainValid_correct (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig)
    (h : checkDomainValid e ρ cfg = true) : evalDomainValid e ρ cfg := by
  induction e with
  | const q => trivial
  | var idx => trivial
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValid, Bool.and_eq_true] at h
    simp only [evalDomainValid]
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValid, Bool.and_eq_true] at h
    simp only [evalDomainValid]
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | neg e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | inv e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | exp e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | sin e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | cos e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | log e ih =>
    simp only [checkDomainValid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [evalDomainValid]
    exact ⟨ih h.1, h.2⟩
  | atan e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | arsinh e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | atanh e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | sinc e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | erf e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | sinh e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | cosh e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | tanh e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | sqrt e ih =>
    simp only [checkDomainValid] at h
    simp only [evalDomainValid]
    exact ih h
  | namedConst _ => trivial

/-- checkDomainValid1 = true implies evalDomainValid1 -/
theorem checkDomainValid1_correct (e : Expr) (I : IntervalRat) (cfg : EvalConfig)
    (h : checkDomainValid1 e I cfg = true) : evalDomainValid1 e I cfg :=
  checkDomainValid_correct e (fun _ => I) cfg h

/-- evalDomainValid is equivalent to checkDomainValid = true -/
theorem evalDomainValid_iff_checkDomainValid (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig) :
    evalDomainValid e ρ cfg ↔ checkDomainValid e ρ cfg = true := by
  constructor
  · -- evalDomainValid → checkDomainValid
    intro h
    induction e with
    | const _ => rfl
    | var _ => rfl
    | add e₁ e₂ ih₁ ih₂ =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid, Bool.and_eq_true]
      exact ⟨ih₁ h.1, ih₂ h.2⟩
    | mul e₁ e₂ ih₁ ih₂ =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid, Bool.and_eq_true]
      exact ⟨ih₁ h.1, ih₂ h.2⟩
    | neg e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | inv e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | exp e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | sin e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | cos e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | log e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ih h.1, h.2⟩
    | atan e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | arsinh e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | atanh e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | sinc e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | erf e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | sinh e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | cosh e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | tanh e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | sqrt e ih =>
      simp only [evalDomainValid] at h
      simp only [checkDomainValid]
      exact ih h
    | namedConst _ => rfl
  · -- checkDomainValid → evalDomainValid
    exact checkDomainValid_correct e ρ cfg

/-- Decidability instance for domain validity -/
instance decidableEvalDomainValid (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig) :
    Decidable (evalDomainValid e ρ cfg) :=
  decidable_of_iff' _ (evalDomainValid_iff_checkDomainValid e ρ cfg)

/-- Decidability instance for single-variable domain validity -/
instance decidableEvalDomainValid1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig) :
    Decidable (evalDomainValid1 e I cfg) :=
  decidableEvalDomainValid e (fun _ => I) cfg

/-- ADSupported expressions (which don't include log) always have valid domains.
    This is because only log has domain restrictions (positive argument). -/
theorem ADSupported.domainValid {e : Expr} (hsupp : ADSupported e)
    (ρ : IntervalEnv) (cfg : EvalConfig) : evalDomainValid e ρ cfg := by
  induction hsupp generalizing ρ cfg with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih₁ ih₂ => exact ⟨ih₁ ρ cfg, ih₂ ρ cfg⟩
  | mul _ _ ih₁ ih₂ => exact ⟨ih₁ ρ cfg, ih₂ ρ cfg⟩
  | neg _ ih => exact ih ρ cfg
  | sin _ ih => exact ih ρ cfg
  | cos _ ih => exact ih ρ cfg
  | exp _ ih => exact ih ρ cfg

/-- Single-variable version of domainValid for ADSupported -/
theorem exprSupported_domainValid1 {e : Expr} (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig) : evalDomainValid1 e I cfg :=
  ADSupported.domainValid hsupp (fun _ => I) cfg

/-- Fundamental correctness theorem for core evaluation.

    This theorem is FULLY PROVED for core expressions (no sorry, no axioms).
    The `hsupp` hypothesis ensures we only consider expressions in the
    computable verified subset. The `hdom` hypothesis ensures domain validity
    (e.g., log arguments are positive). Works for any Taylor depth. -/
theorem evalIntervalCore_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int)
    (cfg : EvalConfig := {})
    (hdom : evalDomainValid e ρ_int cfg) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Rational.evalTotalCore e ρ_int cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Rational.evalTotalCore]
    exact hρ idx
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
  | neg _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_sinComputableReduced (ih hdom) cfg.taylorDepth
  | cos _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_cosComputableReduced (ih hdom) cfg.taylorDepth
  | exp _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_expComputable (ih hdom) cfg.taylorDepth
  | log _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_logComputable (ih hdom.1) hdom.2 cfg.taylorDepth
  | sqrt _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Rational.evalTotalCore]
    exact IntervalRat.mem_sqrtIntervalTightPrec' (ih hdom)
  | sinh _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Rational.evalTotalCore, sinhInterval]
    exact IntervalRat.mem_sinhComputable (ih hdom) cfg.taylorDepth
  | cosh _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Rational.evalTotalCore, coshInterval]
    exact IntervalRat.mem_coshComputable (ih hdom) cfg.taylorDepth
  | tanh _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Rational.evalTotalCore, tanhInterval]
    exact mem_tanhInterval (ih hdom)
  | erf _ ih =>
    simp only [evalDomainValid] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.Rational.evalTotalCore]
    exact mem_erfInterval (ih hdom) cfg.taylorDepth
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Rational.evalTotalCore]
    exact c.mem_interval

/-! ### Convenience functions -/

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Computable single-variable evaluation for core expressions -/
def evalTotalCore1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  LeanCert.Internal.Rational.evalTotalCore e (fun _ => I) cfg

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- Correctness for single-variable core evaluation -/
theorem evalIntervalCore1_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I)
    (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg) :
    Expr.eval (fun _ => x) e ∈ LeanCert.Internal.Rational.evalTotalCore1 e I cfg :=
  evalIntervalCore_correct e hsupp _ _ (fun _ => hx) cfg hdom

/-! ### Smart constructors for supported expressions -/

/-- Build a constant expression (always supported) -/
def mkConst (q : ℚ) : { e : Expr // ADSupported e } :=
  ⟨Expr.const q, ADSupported.const q⟩

/-- Build a variable expression (always supported) -/
def mkVar (idx : Nat) : { e : Expr // ADSupported e } :=
  ⟨Expr.var idx, ADSupported.var idx⟩

/-- Build an addition (supported if both operands are supported) -/
def mkAdd (e₁ e₂ : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.add e₁.val e₂.val, ADSupported.add e₁.property e₂.property⟩

/-- Build a multiplication (supported if both operands are supported) -/
def mkMul (e₁ e₂ : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.mul e₁.val e₂.val, ADSupported.mul e₁.property e₂.property⟩

/-- Build a negation (supported if operand is supported) -/
def mkNeg (e : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.neg e.val, ADSupported.neg e.property⟩

/-- Build a sin (supported if operand is supported) -/
def mkSin (e : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.sin e.val, ADSupported.sin e.property⟩

/-- Build a cos (supported if operand is supported) -/
def mkCos (e : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.cos e.val, ADSupported.cos e.property⟩

/-- Build an exp (supported if operand is supported) -/
def mkExp (e : { e : Expr // ADSupported e }) : { e : Expr // ADSupported e } :=
  ⟨Expr.exp e.val, ADSupported.exp e.property⟩

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Checked evaluation results

Certified evaluators return a finite enclosure only after all partial-domain
conditions have been checked.  Failures are data: callers must propagate them
instead of substituting a finite sentinel that could be mistaken for an
enclosure.
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Why a checked evaluator could not produce a finite certified enclosure. -/
inductive EvalError where
  | reciprocalContainsZero (interval : IntervalRat)
  | logNonpositive (interval : IntervalRat)
  | atanhOutsideUnitBall (interval : IntervalRat)
  | unsupportedBackend (operation : String)
  | unsupportedFeature (feature : String)
  | invalidConfiguration (message : String)
  | nestedFailure (operation : String) (cause : EvalError)
  deriving Repr, DecidableEq

/-- Result type used by checked evaluators and public computation APIs. -/
abbrev EvalResult (α : Type) := Except EvalError α

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Extended (Noncomputable) Interval Evaluation

This file implements the noncomputable interval evaluator for `LeanCert.Core.Expr`,
supporting exp with floor/ceil bounds and partial evaluation for inv/log.

## Main definitions

* `evalInterval` - Noncomputable interval evaluator supporting exp
* `evalInterval_correct` - Correctness theorem for extended evaluation
* `evalIntervalOption` - Partial (Option-returning) evaluator with inv/log support
* `evalIntervalOption_correct` - Correctness theorem for partial evaluation

## Design notes

The extended evaluator uses `Real.exp` with floor/ceil bounds, which requires
noncomputability. For computability, use `LeanCert.Internal.Rational.evalTotalCore` instead.

The partial evaluator `evalIntervalOption` returns `none` when:
- The denominator interval for `inv` contains zero
- The argument interval for `log` is not strictly positive
- The argument for `atanh` is not in (-1, 1)

When it returns `some I`, correctness is guaranteed.
-/

/-! ### Extended interval evaluation (noncomputable, supports exp) -/

public section

namespace LeanCert.Engine

open LeanCert.Core

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Noncomputable interval evaluator supporting exp.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalIntervalOption for partial functions like inv and log.

    This evaluator is NONCOMPUTABLE due to exp using Real.exp with floor/ceil. -/
noncomputable def evalUnchecked (e : Expr) (ρ : IntervalEnv) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (evalUnchecked e₁ ρ) (evalUnchecked e₂ ρ)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalUnchecked e₁ ρ) (evalUnchecked e₂ ρ)
  | Expr.neg e => IntervalRat.neg (evalUnchecked e ρ)
  | Expr.inv _ => default  -- Not in ADSupported; safe default
  | Expr.exp e => IntervalRat.expInterval (evalUnchecked e ρ)
  | Expr.sin e => sinInterval (evalUnchecked e ρ)
  | Expr.cos e => cosInterval (evalUnchecked e ρ)
  | Expr.log _ => default  -- Not in ADSupported; use evalIntervalOption for log
  | Expr.atan e => atanInterval (evalUnchecked e ρ)
  | Expr.arsinh e => arsinhInterval (evalUnchecked e ρ)
  | Expr.atanh _ => default  -- Not in ADSupported; use evalIntervalOption for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh _ => default  -- sinh unbounded; use LeanCert.Internal.Rational.evalTotalCore for
    -- tight bounds
  | Expr.cosh _ => default  -- cosh unbounded; use LeanCert.Internal.Rational.evalTotalCore for
    -- tight bounds
  | Expr.tanh _ => default  -- tanh bounded but not in ADSupported; use
    -- LeanCert.Internal.Rational.evalTotalCore
  | Expr.sqrt e => IntervalRat.sqrtInterval (evalUnchecked e ρ)
  | Expr.namedConst c => c.interval

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- Fundamental correctness theorem for extended evaluation.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalInterval_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Rational.evalUnchecked e ρ_int := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Rational.evalUnchecked]
    exact hρ idx
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_add, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_mul, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, LeanCert.Internal.Rational.evalUnchecked]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, LeanCert.Internal.Rational.evalUnchecked]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_expInterval ih

/-! ### Convenience functions

Note: LeanCert.Internal.Rational.evalTotalCore now uses Taylor series for exp/sin/cos, which gives
different (often tighter) intervals than evalInterval's floor/ceil bounds.
Both are correct, but they are not necessarily equal.

For purely algebraic expressions (const, var, add, mul, neg),
both evaluators give identical results. -/

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Internal single-variable wrapper around `evalUnchecked`. -/
noncomputable def evalUnchecked1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  evalUnchecked e (fun _ => I)

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- Correctness for single-variable extended evaluation -/
theorem evalInterval1_correct (e : Expr) (hsupp : ADSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ LeanCert.Internal.Rational.evalUnchecked1 e I :=
  evalInterval_correct e hsupp _ _ (fun _ => hx)

/-! ### Partial interval evaluation with inv support -/

/-- Partial (Option-returning) interval evaluator supporting inv.

    For expressions with inv, this evaluator returns `none` if the denominator
    interval contains zero, and `some I` with a correct enclosure otherwise.

    This allows safe interval evaluation of expressions like 1/x when we can
    verify the denominator is bounded away from zero.

    For expressions without inv, this always returns `some` with the same
    result as `evalInterval`. -/
def evalIntervalLogDepth : ℕ := 60

/-- The Taylor truncation depth used by the checked exponential evaluator. -/
def evalIntervalExpDepth : ℕ := 30

/-- Taylor depth used by the strict `atanh` evaluator. -/
def evalIntervalAtanhDepth : ℕ := 30

/-- Evaluate an expression by rational intervals, failing when a domain check fails. -/
def evalIntervalOption (e : Expr) (ρ : IntervalEnv) : Option IntervalRat :=
  match e with
  | Expr.const q => some (IntervalRat.singleton q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalIntervalOption e₁ ρ, evalIntervalOption e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.add I₁ I₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalIntervalOption e₁ ρ, evalIntervalOption e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.mul I₁ I₂)
      | _, _ => none
  | Expr.neg e =>
      match evalIntervalOption e ρ with
      | some I => some (IntervalRat.neg I)
      | none => none
  | Expr.inv e₁ =>
      match evalIntervalOption e₁ ρ with
      | none => none
      | some J =>
          if h : IntervalRat.containsZero J then
            none
          else
            some (IntervalRat.invNonzero ⟨J, h⟩)
  | Expr.exp e =>
      match evalIntervalOption e ρ with
      | some I => some (IntervalRat.expComputable I evalIntervalExpDepth)
      | none => none
  | Expr.sin e =>
      match evalIntervalOption e ρ with
      | some I => some (sinInterval I)
      | none => none
  | Expr.cos e =>
      match evalIntervalOption e ρ with
      | some I => some (cosInterval I)
      | none => none
  | Expr.log e =>
      match evalIntervalOption e ρ with
      | none => none
      | some J =>
          if h : IntervalRat.isPositive J then
            some (IntervalRat.logComputable J evalIntervalLogDepth)
          else
            none
  | Expr.atan e =>
      match evalIntervalOption e ρ with
      | some I => some (atanInterval I)
      | none => none
  | Expr.arsinh e =>
      match evalIntervalOption e ρ with
      | some I => some (arsinhInterval I)
      | none => none
  | Expr.atanh e =>
      match evalIntervalOption e ρ with
      | none => none
      | some J =>
          if -1 < J.lo ∧ J.hi < 1 then
            some (IntervalRat.atanhComputable J evalIntervalAtanhDepth)
          else
            none
  | Expr.sinc e =>
      match evalIntervalOption e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
      | none => none
  | Expr.erf e =>
      match evalIntervalOption e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
      | none => none
  | Expr.sinh e =>
      match evalIntervalOption e ρ with
      | some I => some (sinhInterval I)
      | none => none
  | Expr.cosh e =>
      match evalIntervalOption e ρ with
      | some I => some (coshInterval I)
      | none => none
  | Expr.tanh e =>
      match evalIntervalOption e ρ with
      | some I => some (tanhInterval I)
      | none => none
  | Expr.sqrt e =>
      match evalIntervalOption e ρ with
      | some I => some (IntervalRat.sqrtInterval I)
      | none => none
  | Expr.namedConst c => some c.interval

/-- Main correctness theorem for evalIntervalOption (approach 1 from plan).

    When evalIntervalOption returns `some I`:
    1. The expression evaluates to a value in I for all ρ_real ∈ ρ_int
    2. All inv denominators along the evaluation are guaranteed nonzero
       (because their intervals don't contain zero)

    This follows your suggestion to keep ADSupported syntactic and add
    separate semantic hypotheses. The key insight is that if evalIntervalOption
    succeeds (returns Some), the interval arithmetic has already verified
    that no denominator interval contains zero. -/
theorem evalIntervalOption_correct (e : Expr)
    (ρ_int : IntervalEnv) (I : IntervalRat)
    (hsome : evalIntervalOption e ρ_int = some I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  induction e generalizing I with
  | const q =>
    simp only [evalIntervalOption] at hsome
    cases hsome
    simp only [Expr.eval_const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalIntervalOption] at hsome
    cases hsome
    simp only [Expr.eval_var]
    exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalIntervalOption] at hsome
    cases heq₁ : evalIntervalOption e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalIntervalOption e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_add]
        exact IntervalRat.mem_add (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalIntervalOption] at hsome
    cases heq₁ : evalIntervalOption e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalIntervalOption e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_mul]
        exact IntervalRat.mem_mul (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | neg e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_neg]
      exact IntervalRat.mem_neg (ih I' heq)
  | inv e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · contradiction
      · rename_i hnonzero
        cases hsome
        simp only [Expr.eval_inv]
        have hJ_mem := ih J heq
        -- The denominator is nonzero because J doesn't contain zero and eval ∈ J
        have heval_ne : Expr.eval ρ_real e ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hJ_mem
          simp only [IntervalRat.mem_def] at hJ_mem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnonzero
          rcases le_or_gt J.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ J.hi := by
              have h : (0 : ℝ) ≤ J.hi := hJ_mem.2
              exact_mod_cast h
            exact absurd (hnonzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < J.lo := by exact_mod_cast hlo
            exact absurd hJ_mem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hJ_mem heval_ne
  | log e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · rename_i hpos
        cases hsome
        simp only [Expr.eval_log]
        have hJ_mem := ih J heq
        -- The argument is positive because J.lo > 0 and eval ∈ J
        exact IntervalRat.mem_logComputable hJ_mem hpos evalIntervalLogDepth
      · contradiction
  | atanh e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · rename_i hunit
        cases hsome
        simp only [Expr.eval_atanh]
        exact IntervalRat.mem_atanhComputable (ih J heq) hunit.1 hunit.2
          evalIntervalAtanhDepth
      · contradiction
  | sinc e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_sinc]
      -- sinc(x) ∈ [-1, 1] for all x, using Mathlib's Real.sinc lemmas
      simp only [IntervalRat.mem_def]
      simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using
        (Real.sinc_mem_Icc (Expr.eval ρ_real e))
  | erf e ih =>
    simp only [evalIntervalOption] at hsome
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_erf]
      -- erf(x) ∈ [-1, 1] for all x
      simp only [IntervalRat.mem_def]
      simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using
        (Real.erf_mem_Icc (Expr.eval ρ_real e))
  | namedConst c =>
    simp only [evalIntervalOption] at hsome
    cases hsome
    simp only [Expr.eval_namedConst]
    exact c.mem_interval
  | exp e ih | sin e ih | cos e ih | sinh e ih | cosh e ih | tanh e ih
  | atan e ih | arsinh e ih | sqrt e ih =>
    cases heq : evalIntervalOption e ρ_int with
    | none => simp only [evalIntervalOption, heq] at hsome; contradiction
    | some I' =>
      simp only [evalIntervalOption, heq] at hsome
      cases hsome
      first
      | exact IntervalRat.mem_expComputable (ih I' heq) evalIntervalExpDepth
      | exact mem_sinInterval (ih I' heq)
      | exact mem_cosInterval (ih I' heq)
      | exact IntervalRat.mem_sinhComputable (ih I' heq) 10
      | exact IntervalRat.mem_coshComputable (ih I' heq) 10
      | exact mem_tanhInterval (ih I' heq)
      | exact mem_atanInterval (ih I' heq)
      | exact mem_arsinhInterval (ih I' heq)
      | exact IntervalRat.mem_sqrtInterval' (ih I' heq)

/-! ### Checked API with diagnostics -/

/-- Diagnose the first partial-domain failure after `evalIntervalOption` returned
`none`. This function is deliberately separate from the trusted computation:
soundness depends only on successful `evalIntervalOption`, while diagnostics may be
refined without changing the correctness theorem. -/
def diagnoseEvalIntervalFailure (e : Expr) (ρ : IntervalEnv) : EvalError :=
  match e with
  | .add e₁ e₂ | .mul e₁ e₂ =>
      if evalIntervalOption e₁ ρ = none then
        .nestedFailure "left operand" (diagnoseEvalIntervalFailure e₁ ρ)
      else
        .nestedFailure "right operand" (diagnoseEvalIntervalFailure e₂ ρ)
  | .neg e | .exp e | .sin e | .cos e | .atan e | .arsinh e | .sinc e |
      .erf e | .sinh e | .cosh e | .tanh e | .sqrt e =>
      .nestedFailure "unary operand" (diagnoseEvalIntervalFailure e ρ)
  | .inv e =>
      match evalIntervalOption e ρ with
      | some I => .reciprocalContainsZero I
      | none => .nestedFailure "reciprocal operand" (diagnoseEvalIntervalFailure e ρ)
  | .log e =>
      match evalIntervalOption e ρ with
      | some I => .logNonpositive I
      | none => .nestedFailure "logarithm operand" (diagnoseEvalIntervalFailure e ρ)
  | .atanh e =>
      match evalIntervalOption e ρ with
      | some I => .atanhOutsideUnitBall I
      | none => .nestedFailure "atanh operand" (diagnoseEvalIntervalFailure e ρ)
  | .const _ | .var _ | .namedConst _ =>
      .unsupportedBackend "internal: total expression unexpectedly failed"
termination_by e

/-- Checked rational evaluator. Every successful result is a certified finite
enclosure; domain-invalid expressions return a structured error. -/
def evalIntervalChecked (e : Expr) (ρ : IntervalEnv) : EvalResult IntervalRat :=
  match evalIntervalOption e ρ with
  | some I => .ok I
  | none => .error (diagnoseEvalIntervalFailure e ρ)

/-- Success of `evalIntervalChecked` is sufficient for enclosure correctness
for every expression constructor. -/
theorem evalIntervalChecked_correct (e : Expr) (ρ_int : IntervalEnv) (I : IntervalRat)
    (hsuccess : evalIntervalChecked e ρ_int = .ok I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  cases heval : evalIntervalOption e ρ_int with
  | none =>
    rw [evalIntervalChecked, heval] at hsuccess
    contradiction
  | some J =>
    rw [evalIntervalChecked, heval] at hsuccess
    injection hsuccess with hJI
    subst I
    exact evalIntervalOption_correct e ρ_int J heval ρ_real hρ

/-- Checked Rational evaluation with a tight path for the verified computable
core. Unsupported syntax or a failed core-domain check falls back to the
general checked evaluator, preserving its structured domain errors. -/
def evalIntervalTightChecked (e : Expr) (ρ : IntervalEnv)
    (cfg : EvalConfig := {}) : EvalResult IntervalRat :=
  if e.checkSupportedCore && checkDomainValid e ρ cfg then
    .ok (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  else
    evalIntervalChecked e ρ

/-- Every successful tight checked Rational evaluation encloses the expression
value. The core branch uses the core correctness theorem; the fallback uses
the general checked evaluator theorem. -/
theorem evalIntervalTightChecked_correct (e : Expr) (ρ_int : IntervalEnv)
    (cfg : EvalConfig) (I : IntervalRat)
    (hsuccess : evalIntervalTightChecked e ρ_int cfg = .ok I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  by_cases hsupp : e.checkSupportedCore = true
  · by_cases hdom : checkDomainValid e ρ_int cfg = true
    · have hsupp' := Expr.checkSupportedCore_correct hsupp
      have hdom' := checkDomainValid_correct e ρ_int cfg hdom
      have hmem := evalIntervalCore_correct e hsupp' ρ_real ρ_int hρ cfg hdom'
      simp only [ExceptT.stM_eq, evalIntervalTightChecked, hsupp, hdom, Bool.and_self, ↓reduceIte,
        Except.ok.injEq] at hsuccess
      subst I
      exact hmem
    · have hfallback :
          evalIntervalTightChecked e ρ_int cfg = evalIntervalChecked e ρ_int := by
        simp [evalIntervalTightChecked, hsupp, hdom]
      rw [hfallback] at hsuccess
      exact evalIntervalChecked_correct e ρ_int I hsuccess ρ_real hρ
  · have hfallback :
        evalIntervalTightChecked e ρ_int cfg = evalIntervalChecked e ρ_int := by
      simp [evalIntervalTightChecked, hsupp]
    rw [hfallback] at hsuccess
    exact evalIntervalChecked_correct e ρ_int I hsuccess ρ_real hρ

/-- Single-variable version of evalIntervalOption -/
def evalIntervalOption1 (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  evalIntervalOption e (fun _ => I)

/-- Correctness for single-variable partial evaluation -/
theorem evalIntervalOption1_correct (e : Expr)
    (I : IntervalRat) (J : IntervalRat)
    (hsome : evalIntervalOption1 e I = some J)
    (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ J :=
  evalIntervalOption_correct e _ J hsome _ (fun _ => hx)

/-- When evalIntervalOption succeeds, we get bounds -/
theorem evalIntervalOption_le_of_hi (e : Expr)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalIntervalOption1 e I = some J)
    (hhi : J.hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalIntervalOption1_correct e I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ J.hi := hmem.2
  have hhi_le_c : (J.hi : ℝ) ≤ c := by exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- When evalIntervalOption succeeds, we get lower bounds -/
theorem evalIntervalOption_ge_of_lo (e : Expr)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalIntervalOption1 e I = some J)
    (hlo : c ≤ J.lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalOption1_correct e I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : J.lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ J.lo := by exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Semantic Lemmas for Interval Bounds

This file provides semantic lemmas for deriving real bounds from certified
interval enclosures. Tactics consume these lemmas, but the definitions belong
to the engine layer so checked programmatic APIs do not depend on tactic
modules.

## Main theorems

### Core (computable) lemmas
* `exprCore_le_of_interval_hi` - Upper bound from interval high endpoint
* `exprCore_ge_of_interval_lo` - Lower bound from interval low endpoint
* `exprCore_lt_of_interval_hi_lt` - Strict upper bound
* `exprCore_gt_of_interval_lo_gt` - Strict lower bound

### Extended (noncomputable) lemmas
* `expr_le_of_interval_hi` - Upper bound from interval high endpoint
* `expr_ge_of_interval_lo` - Lower bound from interval low endpoint
* `expr_lt_of_interval_hi_lt` - Strict upper bound
* `expr_gt_of_interval_lo_gt` - Strict lower bound
* `expr_le_of_mem_interval` - Single-point variant
* `expr_ge_of_mem_interval` - Single-point variant

## Usage

These lemmas are intended to be used by tactics like `certify_bound` and
`interval_decide` to close goals of the form `∀ x ∈ I, f(x) ≤ c` or similar.

The core lemmas use the computable evaluator and can work with `native_decide`.
The extended lemmas use the noncomputable evaluator with floor/ceil bounds.
-/

/-! ### Tactic-facing lemmas for interval bounds (core, computable) -/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Upper bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_le_of_interval_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hhi : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I
    cfg).hi := hmem.2
  have hhi_le_c : ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi : ℝ) ≤ c := by
    exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_ge_of_interval_lo (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hlo : c ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo ≤ Expr.eval (fun _ =>
    x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo := by
    exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_lt_of_interval_hi_lt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hhi : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I
    cfg).hi := hmem.2
  have hhi_lt_c : ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi : ℝ) < c := by
    exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_gt_of_interval_lo_gt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hlo : c < (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo ≤ Expr.eval (fun _ =>
    x) e := hmem.1
  have hc_lt_lo : (c : ℝ) < (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo := by
    exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-! ### Tactic-facing lemmas for interval bounds (extended, noncomputable) -/

/-- Upper bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_le_of_interval_hi (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).hi
    := hmem.2
  have hhi_le_c : ((LeanCert.Internal.Rational.evalUnchecked1 e I).hi : ℝ) ≤ c := by
    exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_ge_of_interval_lo (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e
    := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo := by
    exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_lt_of_interval_hi_lt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).hi
    := hmem.2
  have hhi_lt_c : ((LeanCert.Internal.Rational.evalUnchecked1 e I).hi : ℝ) < c := by
    exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_gt_of_interval_lo_gt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c < (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e
    := hmem.1
  have hc_lt_lo : (c : ℝ) < (LeanCert.Internal.Rational.evalUnchecked1 e I).lo := by
    exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-- Variant for single point (extended). -/
theorem expr_le_of_mem_interval (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi ≤ c) :
    Expr.eval (fun _ => x) e ≤ c :=
  expr_le_of_interval_hi e hsupp I c hhi x hx

/-- Variant for single point (extended). -/
theorem expr_ge_of_mem_interval (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hlo : c ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    c ≤ Expr.eval (fun _ => x) e :=
  expr_ge_of_interval_lo e hsupp I c hlo x hx

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Interval Evaluation of Expressions

This file re-exports the interval evaluation infrastructure for `LeanCert.Core.Expr`.

## Module structure

The implementation is split across several files:

* `LeanCert.Core.Support` - Expression support predicates for total core
  evaluation and automatic differentiation

* `LeanCert.Engine.Eval.Core` - Computable interval evaluator
(`LeanCert.Internal.Rational.evalTotalCore`)
  and transcendental interval bounds

* `LeanCert.Engine.Eval.Extended` - Internal noncomputable evaluator and the
  partial evaluator with inv/log support (`evalIntervalOption`)

* `LeanCert.Engine.Bounds.Lemmas` - Semantic lemmas for deriving real bounds

## Main definitions (re-exported)

### Expression support predicates
* `ExprSupportedCore` - Computable subset (const, var, add, mul, neg, sin, cos, exp, sqrt, sinh,
cosh, tanh, pi)
* `ADSupported` - Noncomputable AD subset (const, var, add, mul, neg, sin, cos, exp)

### Evaluators
* `LeanCert.Internal.Rational.evalTotalCore` - Computable interval evaluator (uses Taylor series)
* `LeanCert.Internal.Rational.evalUnchecked` - Internal noncomputable evaluator
* `evalIntervalOption` - Partial evaluator with inv/log support

### Correctness theorems
* `evalIntervalCore_correct` - Core evaluator correctness
* `evalInterval_correct` - Extended evaluator correctness
* `evalIntervalOption_correct` - Partial evaluator correctness

### Tactic lemmas
* `exprCore_le_of_interval_hi` / `exprCore_ge_of_interval_lo` - Core bounds
* `expr_le_of_interval_hi` / `expr_ge_of_interval_lo` - Extended bounds

## Design notes

The evaluators are split by computability:
- `LeanCert.Internal.Rational.evalTotalCore` is COMPUTABLE, enabling `native_decide` in tactics
- `evalInterval` is NONCOMPUTABLE, using Real.exp with floor/ceil bounds
- Both are fully verified (no sorry, no axioms)
-/

public section

namespace LeanCert.Engine

-- Re-export all definitions from component modules
-- All imports are transitive, so users can continue to `import LeanCert.Engine.IntervalEval`
-- and have access to all definitions as before.

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Basic Definitions

This file provides the core types and algebraic operations for forward-mode
automatic differentiation using interval arithmetic.

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `DualInterval.const` - Constant dual (derivative is zero)
* `DualInterval.varActive` - Active variable (derivative is 1)
* `DualInterval.varPassive` - Passive variable (derivative is 0)
* `DualInterval.add` - Addition with sum rule
* `DualInterval.mul` - Multiplication with product rule
* `DualInterval.neg` - Negation
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Dual number with interval components: represents (value, derivative) -/
structure DualInterval where
  /-- The interval enclosing the function value. -/
  val : IntervalRat
  /-- The interval enclosing the derivative. -/
  der : IntervalRat
  deriving Repr

/-- Default DualInterval for unsupported expression branches -/
instance : Inhabited DualInterval where
  default := ⟨default, default⟩

namespace DualInterval

/-- Dual interval for a constant (derivative is zero) -/
@[expose]
def const (q : ℚ) : DualInterval :=
  { val := IntervalRat.singleton q
    der := IntervalRat.singleton 0 }

/-- Dual interval for the constant π (derivative is zero) -/
def piConst : DualInterval :=
  { val := piInterval
    der := IntervalRat.singleton 0 }

/-- Dual interval for the Euler–Mascheroni constant γ (derivative is zero) -/
def eulerMascheroniConst : DualInterval :=
  { val := eulerMascheroniInterval
    der := IntervalRat.singleton 0 }

/-- Dual interval for a named mathematical constant (derivative is zero) -/
@[expose]
def ofMathConst (c : MathConst) : DualInterval :=
  { val := c.interval
    der := IntervalRat.singleton 0 }

/-- Dual interval for the variable we're differentiating with respect to -/
@[expose]
def varActive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 1 }

/-- Dual interval for a passive variable -/
@[expose]
def varPassive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 0 }

/-- Add two dual intervals -/
@[expose]
def add (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.add d₁.val d₂.val
    der := IntervalRat.add d₁.der d₂.der }

/-- Multiply two dual intervals (product rule) -/
@[expose]
def mul (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.mul d₁.val d₂.val
    -- d(f*g) = f'*g + f*g'
    der := IntervalRat.add
             (IntervalRat.mul d₁.der d₂.val)
             (IntervalRat.mul d₁.val d₂.der) }

/-- Negate a dual interval -/
@[expose]
def neg (d : DualInterval) : DualInterval :=
  { val := IntervalRat.neg d.val
    der := IntervalRat.neg d.der }

/-- Inverse of a dual interval (quotient rule: d(1/f) = -f'/f²)
    Uses invInterval for the value component.
    For intervals containing zero, returns wide bounds. -/
def inv (d : DualInterval) : DualInterval :=
  let inv_val := invInterval d.val
  -- d(1/f) = -f'/f² = -f' * (1/f)²
  let inv_sq := IntervalRat.mul inv_val inv_val
  let der' := IntervalRat.neg (IntervalRat.mul d.der inv_sq)
  { val := inv_val, der := der' }

end DualInterval

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Transcendental Functions

This file provides dual interval implementations for transcendental functions,
implementing the chain rule for each.

## Main definitions

### Total functions (always succeed)
* `DualInterval.sin` - Sine with chain rule
* `DualInterval.cos` - Cosine with chain rule
* `DualInterval.exp` - Exponential with chain rule
* `DualInterval.atan` - Arctangent with chain rule
* `DualInterval.arsinh` - Inverse hyperbolic sine
* `DualInterval.sinh`, `cosh`, `tanh` - Hyperbolic functions
* `DualInterval.erf` - Error function
* `DualInterval.sqrt` - Square root (conservative derivative bound)
* `DualInterval.sinc` - sinc function

### Partial functions (return Option)
* `DualInterval.atanhOption` - Inverse hyperbolic tangent (requires |x| < 1)
* `DualInterval.inv?` - Inverse (requires nonzero)
* `DualInterval.logOption` - Logarithm (requires positive)
* `DualInterval.sqrt?` - Square root with tight bounds (requires positive)
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

namespace DualInterval

/-- Dual for sin (chain rule: d(sin f) = cos(f) * f') -/
@[expose]
def sin (d : DualInterval) : DualInterval :=
  { val := sinInterval d.val
    der := IntervalRat.mul (cosInterval d.val) d.der }

/-- Dual for cos (chain rule: d(cos f) = -sin(f) * f') -/
@[expose]
def cos (d : DualInterval) : DualInterval :=
  { val := cosInterval d.val
    der := IntervalRat.mul (IntervalRat.neg (sinInterval d.val)) d.der }

/-- Dual for exp (chain rule: d(exp f) = exp(f) * f') -/
@[expose]
noncomputable def exp (d : DualInterval) : DualInterval :=
  { val := IntervalRat.expInterval d.val
    der := IntervalRat.mul (IntervalRat.expInterval d.val) d.der }

/-- The interval [0, 1] used to bound derivative factors in (0, 1] -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The derivative factor for arctan: 1/(1+x²) is in [0, 1] -/
theorem arctan_deriv_factor_mem_unitInterval (y : ℝ) :
    1 / (1 + y ^ 2) ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have hpos : 0 < 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  constructor
  · exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hpos)
  · rw [div_le_one hpos]
    nlinarith [sq_nonneg y]

/-- The derivative factor for arsinh: 1/√(1+x²) is in [0, 1] -/
theorem arsinh_deriv_factor_mem_unitInterval (y : ℝ) :
    (Real.sqrt (1 + y ^ 2))⁻¹ ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have h1 : 1 + y ^ 2 ≥ 1 := by nlinarith [sq_nonneg y]
  have hsqrt_ge_one : Real.sqrt (1 + y ^ 2) ≥ 1 := by
    calc Real.sqrt (1 + y ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hsqrt_pos : 0 < Real.sqrt (1 + y ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg y]
  constructor
  · exact inv_nonneg.mpr (le_of_lt hsqrt_pos)
  · exact inv_le_one_of_one_le₀ hsqrt_ge_one

/-- Dual for atan (chain rule: d(atan f) = f' / (1 + f²)) -/
@[expose]
def atan (d : DualInterval) : DualInterval :=
  { val := atanInterval d.val
    -- d(atan f) = f' / (1 + f²)
    -- Since 0 < 1/(1+x²) ≤ 1 for all x, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for arsinh (chain rule: d(arsinh f) = f' / √(1 + f²)) -/
@[expose]
def arsinh (d : DualInterval) : DualInterval :=
  { val := arsinhInterval d.val
    -- d(arsinh f) = f' / √(1 + f²)
    -- Since 0 < 1/√(1+f²) ≤ 1, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for sinh (chain rule: d(sinh f) = cosh(f) * f') -/
@[expose]
def sinh (d : DualInterval) : DualInterval :=
  { val := sinhInterval d.val
    -- sinh'(x) = cosh(x), so d(sinh f) = cosh(f) * f'
    der := IntervalRat.mul (coshInterval d.val) d.der }

/-- Dual for cosh (chain rule: d(cosh f) = sinh(f) * f') -/
@[expose]
def cosh (d : DualInterval) : DualInterval :=
  { val := coshInterval d.val
    -- cosh'(x) = sinh(x), so d(cosh f) = sinh(f) * f'
    der := IntervalRat.mul (sinhInterval d.val) d.der }

/-- Dual for tanh (chain rule: d(tanh f) = sech²(f) * f' = (1 - tanh²(f)) * f')
    Since sech²(x) = 1 - tanh²(x) ∈ (0, 1] for all x, we use [0, 1] as bound. -/
def tanh (d : DualInterval) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) = 1 - tanh²(x), which is in (0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Interval containing 2/√π ≈ 1.128379... -/
@[expose]
def twoDivSqrtPi : IntervalRat :=
  ⟨1128/1000, 1129/1000, by norm_num⟩

/-- Dual for erf (chain rule: d(erf f) = (2/√π) * exp(-f²) * f')
    erf'(x) = (2/√π) * exp(-x²), which is always positive and bounded by 2/√π ≈ 1.13 -/
@[expose]
noncomputable def erf (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expInterval negValSq
      let factor := IntervalRat.mul twoDivSqrtPi expPart
      IntervalRat.mul factor d.der }

/-- Computable dual for erf using expComputable -/
def erfCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expComputable negValSq n
      let factor := IntervalRat.mul twoDivSqrtPi expPart
      IntervalRat.mul factor d.der }

/-- Dual for sqrt (chain rule: d(sqrt f) = f' / (2 * sqrt(f)))
    sqrt'(x) = 1/(2*sqrt(x)) for x > 0, undefined at x = 0.
    We use sqrtInterval for the value and a conservative bound for the derivative.
    Note: The derivative blows up as x → 0+, so this uses a wide conservative bound. -/
def sqrt (d : DualInterval) : DualInterval :=
  { val := IntervalRat.sqrtInterval d.val
    -- The derivative 1/(2*sqrt(x)) ∈ [0, ∞) for x > 0
    -- We use a very conservative bound [-100, 100] * der
    der := IntervalRat.mul d.der ⟨-100, 100, by norm_num⟩ }

/-- Conservative derivative bound [-1, 1] for sinc derivative -/
@[expose]
def sincDerivBound : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- Dual for sinc (chain rule: d(sinc f) = sinc'(f) * f')
    sinc'(x) = (x cos x - sin x) / x² for x ≠ 0, limit 0 at x = 0.
    We use conservative bound: |sinc'(x)| ≤ 1 for all x. -/
@[expose]
def sinc (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- sinc is bounded in [-1, 1]
    -- sinc'(x) ∈ [-1, 1] (conservative bound), so d(sinc f) = sinc'(f) * f'
    der := IntervalRat.mul sincDerivBound d.der }

/-! ### Partial functions (domain-restricted) -/

/-- Partial dual for atanh (chain rule: d(atanh f) = f' / (1 - f²))
    Returns None if the value interval is not contained in (-1, 1). -/
noncomputable def atanhOption (d : DualInterval) : Option DualInterval :=
  -- For atanh to be defined, we need |val| < 1
  -- We check if the interval is strictly inside (-1, 1)
  if d.val.hi < 1 ∧ d.val.lo > -1 then
    -- Very rough bound: atanh' = 1/(1-x²), which blows up as |x| → 1
    -- For now we use [-100, 100] * der as a hugely conservative bound
    let bound : ℚ := 100
    some { val := atanhInterval d.val
           der := ⟨-bound * (|d.der.lo| + |d.der.hi| + 1),
                   bound * (|d.der.lo| + |d.der.hi| + 1),
                   by
                     have h1 : (0 : ℚ) ≤ |d.der.lo| := abs_nonneg _
                     have h2 : (0 : ℚ) ≤ |d.der.hi| := abs_nonneg _
                     have h : (0 : ℚ) ≤ bound * (|d.der.lo| + |d.der.hi| + 1) := by
                       exact mul_nonneg (by norm_num) (by linarith)
                     linarith⟩ }
  else
    none

/-- Partial dual for inv (chain rule: d(1/f) = -f'/f²)
    Returns None if the value interval contains zero. -/
@[expose]
def inv? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.containsZero d.val then
    none
  else
    let inv_val := IntervalRat.invNonzero ⟨d.val, h⟩
    -- d(1/f) = -f'/f² = -f' * (1/f)²
    let inv_sq := IntervalRat.mul inv_val inv_val
    let der' := IntervalRat.neg (IntervalRat.mul d.der inv_sq)
    some { val := inv_val, der := der' }

/-- Partial dual for log (chain rule: d(log f) = f'/f)
    Returns None if the value interval is not strictly positive. -/
@[expose]
noncomputable def logOption (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.isPositive d.val then
    let log_val := IntervalRat.logInterval ⟨d.val, h⟩
    -- d(log f) = f'/f
    let inv_val := IntervalRat.invNonzero ⟨d.val, by
      -- isPositive implies not containsZero
      simp only [IntervalRat.isPositive, IntervalRat.containsZero] at h ⊢
      intro ⟨hle, _⟩
      exact absurd h (not_lt.mpr hle)⟩
    let der' := IntervalRat.mul d.der inv_val
    some { val := log_val, der := der' }
  else
    none

/-- Compute a conservative upper bound on 1/(2*sqrt(lo)) for lo > 0.
    Uses the fact that:
    - For 0 < lo ≤ 1: sqrt(lo) ≥ lo, so 1/(2*sqrt(lo)) ≤ 1/(2*lo)
    - For lo > 1: sqrt(lo) > 1, so 1/(2*sqrt(lo)) < 1/2 -/
@[expose]
def sqrtDerivCoefBound (lo : ℚ) (hpos : 0 < lo) : IntervalRat :=
  if lo ≤ 1 then
    ⟨0, 1 / (2 * lo), by
      exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hpos.le)⟩
  else
    ⟨0, 1 / 2, by norm_num⟩

/-- For lo > 0, the derivative coefficient 1/(2*sqrt(x)) is bounded above for x ≥ lo. -/
theorem sqrtDerivCoef_bound {x lo : ℝ} (hlo_pos : 0 < lo) (hx_ge : lo ≤ x) :
    1 / (2 * Real.sqrt x) ≤ max (1 / (2 * lo)) (1 / 2) := by
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx_ge
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hdenom_pos : 0 < 2 * Real.sqrt x := by positivity
  -- sqrt(x) ≥ sqrt(lo) since sqrt is monotone
  have hsqrt_mono : Real.sqrt lo ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_ge
  have hsqrt_lo_pos : 0 < Real.sqrt lo := Real.sqrt_pos.mpr hlo_pos
  -- 1/(2*sqrt(x)) ≤ 1/(2*sqrt(lo))
  have hcoef_le : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    · positivity
    · linarith
  -- Now bound 1/(2*sqrt(lo))
  rcases le_or_gt lo 1 with hle | hgt
  · -- lo ≤ 1: sqrt(lo) ≥ lo (since sqrt(x) ≥ x for 0 < x ≤ 1)
    have hsqrt_ge_lo : lo ≤ Real.sqrt lo := by
      have h1 : lo * lo ≤ lo := by nlinarith
      have h2 : lo = Real.sqrt lo * Real.sqrt lo → lo ≤ Real.sqrt lo := by
        intro heq
        by_contra! hc
        have : lo * lo > lo := by nlinarith
        linarith
      rw [← Real.sq_sqrt (le_of_lt hlo_pos)] at h1
      rcases eq_or_lt_of_le (Real.sqrt_nonneg lo) with hsz | hsgt
      · -- Case sqrt(lo) = 0 contradicts lo > 0
        have hsqrt_zero : Real.sqrt lo = 0 := hsz.symm
        have hlo_le_zero : lo ≤ 0 := Real.sqrt_eq_zero'.mp hsqrt_zero
        linarith
      · nlinarith [Real.sq_sqrt (le_of_lt hlo_pos)]
    -- 1/(2*sqrt(lo)) ≤ 1/(2*lo)
    have hbound : 1 / (2 * Real.sqrt lo) ≤ 1 / (2 * lo) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      · positivity
      · linarith
    calc 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := hcoef_le
      _ ≤ 1 / (2 * lo) := hbound
      _ ≤ max (1 / (2 * lo)) (1 / 2) := le_max_left _ _
  · -- lo > 1: sqrt(lo) > 1
    have hsqrt_gt_one : 1 < Real.sqrt lo := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    -- 1/(2*sqrt(lo)) < 1/2
    have hbound : 1 / (2 * Real.sqrt lo) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt lo) (by norm_num : (0 : ℝ) < 2)]
      ring_nf
      linarith
    calc 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := hcoef_le
      _ ≤ 1 / 2 := le_of_lt hbound
      _ ≤ max (1 / (2 * lo)) (1 / 2) := le_max_right _ _

/-- Partial dual for sqrt (chain rule: d(sqrt f) = f' / (2 * sqrt(f)))
    Returns None if the value interval is not strictly positive. -/
@[expose]
noncomputable def sqrt? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.isPositive d.val then
    let sqrt_val := IntervalRat.sqrtInterval d.val
    -- d(sqrt f) = f' / (2 * sqrt(f)) = f' * (1 / (2 * sqrt(f)))
    let deriv_coef := sqrtDerivCoefBound d.val.lo h
    let der' := IntervalRat.mul d.der deriv_coef
    some { val := sqrt_val, der := der' }
  else
    none

end DualInterval

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Evaluators

This file provides the evaluation functions for automatic differentiation,
mapping expressions to dual intervals.

## Main definitions

* `DualEnv` - Environment mapping variable indices to dual intervals
* `LeanCert.Internal.AD.evalUnchecked` - Main evaluator for supported expressions (total)
* `evalDualOption` - Partial evaluator supporting domain-checked functions (returns Option)
* `evalDualOption1` - Single-variable version of evalDualOption
* `mkDualEnv` - Create a dual environment for differentiation w.r.t. a variable
* `evalWithDeriv` - Evaluate and differentiate w.r.t. a variable index
* `derivInterval` - Get just the derivative interval
* `evalWithDeriv1` - Single-variable evaluation and differentiation
-/

/-! ### Dual evaluation -/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Environment for dual evaluation -/
abbrev DualEnv := Nat → DualInterval

end LeanCert.Engine

namespace LeanCert.Internal.AD

open LeanCert.Core LeanCert.Engine

/-- Evaluate expression in dual interval mode.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct dual interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalDualOption for partial functions like inv and log. -/
noncomputable def evalUnchecked (e : Expr) (ρ : DualEnv) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (LeanCert.Internal.AD.evalUnchecked e₁ ρ)
    (LeanCert.Internal.AD.evalUnchecked e₂ ρ)
  | Expr.mul e₁ e₂ => DualInterval.mul (LeanCert.Internal.AD.evalUnchecked e₁ ρ)
    (LeanCert.Internal.AD.evalUnchecked e₂ ρ)
  | Expr.neg e => DualInterval.neg (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.inv _ => default  -- Not in ADSupported; safe default
  | Expr.exp e => DualInterval.exp (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sin e => DualInterval.sin (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.cos e => DualInterval.cos (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.log _ => default  -- Not in ADSupported; use evalDualOption for log
  | Expr.atan e => DualInterval.atan (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.arsinh e => DualInterval.arsinh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.atanh _ => default  -- Partial function; use evalDualOption for atanh
  | Expr.sinc e => DualInterval.sinc (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.erf e => DualInterval.erf (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sinh e => DualInterval.sinh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.cosh e => DualInterval.cosh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.tanh e => DualInterval.tanh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sqrt e => DualInterval.sqrt (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.namedConst c => DualInterval.ofMathConst c

end LeanCert.Internal.AD

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Partial dual evaluation -/

/-- Partial dual evaluator that supports domain-checked functions.
    Returns `none` if any domain error would occur:
    - inv of an interval containing zero
    - log of an interval not strictly positive
    When it returns `some`, the result is guaranteed to be correct.

    The total and computable dual evaluators support `tanh`, but this
    Option-returning evaluator deliberately keeps `tanh` disabled until the
    `evalDualOption`-specific value/differentiability/derivative correctness path
    is wired for that constructor. -/
@[expose]
noncomputable def evalDualOption (e : Expr) (ρ : DualEnv) : Option DualInterval :=
  match e with
  | Expr.const q => some (DualInterval.const q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalDualOption e₁ ρ, evalDualOption e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.add d₁ d₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalDualOption e₁ ρ, evalDualOption e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.mul d₁ d₂)
      | _, _ => none
  | Expr.neg e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.neg d)
      | none => none
  | Expr.inv e₁ =>
      match evalDualOption e₁ ρ with
      | none => none
      | some d => DualInterval.inv? d
  | Expr.exp e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.exp d)
      | none => none
  | Expr.sin e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.sin d)
      | none => none
  | Expr.cos e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.cos d)
      | none => none
  | Expr.log e =>
      match evalDualOption e ρ with
      | none => none
      | some d => DualInterval.logOption d
  | Expr.atan e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.atan d)
      | none => none
  | Expr.arsinh e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.arsinh d)
      | none => none
  | Expr.atanh _ =>
      -- atanh is partial (defined only for |x| < 1) and requires complex bounds
      -- We return none to avoid the complexity of proving atanh bounds
      none
  | Expr.sinc e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.sinc d)
      | none => none
  | Expr.erf e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.erf d)
      | none => none
  | Expr.sinh e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.sinh d)
      | none => none
  | Expr.cosh e =>
      match evalDualOption e ρ with
      | some d => some (DualInterval.cosh d)
      | none => none
  | Expr.tanh _ =>
      -- See the docstring above:
      -- `LeanCert.Internal.AD.evalUnchecked`/`LeanCert.Internal.AD.evalTotalCore` support tanh, but
      -- the partial `evalDualOption` correctness theorem currently treats tanh as
      -- outside this Option API.
      none
  | Expr.sqrt e =>
      match evalDualOption e ρ with
      | some d => DualInterval.sqrt? d
      | none => none
  | Expr.namedConst c => some (DualInterval.ofMathConst c)

/-- Single-variable version of evalDualOption -/
@[expose]
noncomputable def evalDualOption1 (e : Expr) (I : IntervalRat) : Option DualInterval :=
  evalDualOption e (fun _ => DualInterval.varActive I)

/-! ### Single variable differentiation -/

/-- Create dual environment for differentiating with respect to variable `idx` -/
@[expose]
def mkDualEnv (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate and differentiate with respect to variable `idx` -/
noncomputable def evalWithDeriv (e : Expr) (ρ : IntervalEnv) (idx : Nat) : DualInterval :=
  LeanCert.Internal.AD.evalUnchecked e (mkDualEnv ρ idx)

/-- Get just the derivative interval -/
noncomputable def derivInterval (e : Expr) (ρ : IntervalEnv) (idx : Nat) : IntervalRat :=
  (evalWithDeriv e ρ idx).der

/-- Evaluate and differentiate a single-variable expression -/
@[expose]
noncomputable def evalWithDeriv1 (e : Expr) (I : IntervalRat) : DualInterval :=
  LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Correctness Theorems

This file proves the correctness of forward-mode automatic differentiation
for supported expressions (ADSupported).

## Main theorems

* `LeanCert.Engine.evalDualUnchecked_val_correct` - Value component is correct
* `LeanCert.Engine.evalDualUnchecked_der_correct` - Derivative component is correct
* `evalFunc1_differentiable` - Supported expressions are differentiable
* `deriv_mem_dualDer` - Key theorem: computed derivative contains true derivative
* `LeanCert.Engine.evalDualUnchecked_der_correct_idx` - n-variable derivative correctness
* `evalWithDeriv1_correct` - Single-variable correctness

## Design notes

All theorems in this file are FULLY PROVED with no sorry or axioms.
The correctness relies on the chain rule for each supported operation.
-/

/-! ### Correctness -/

public section

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

/-- The value component is correct for supported expressions.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalDualUnchecked_val_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ (LeanCert.Internal.AD.evalUnchecked e ρ_dual).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.AD.evalUnchecked, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.AD.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, LeanCert.Internal.AD.evalUnchecked, DualInterval.add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, LeanCert.Internal.AD.evalUnchecked, DualInterval.mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, LeanCert.Internal.AD.evalUnchecked, DualInterval.neg]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, LeanCert.Internal.AD.evalUnchecked, DualInterval.sin]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, LeanCert.Internal.AD.evalUnchecked, DualInterval.cos]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, LeanCert.Internal.AD.evalUnchecked, DualInterval.exp]
    exact IntervalRat.mem_expInterval ih

/-! ### Single-variable evaluation for derivative proofs -/

/-- The function t ↦ Expr.eval (fun _ => t) e for single-variable expressions -/
noncomputable abbrev evalFunc1 (e : Expr) : ℝ → ℝ :=
  fun t => Expr.eval (fun _ => t) e

/-! ### Differentiability of supported expressions -/

/-- Supported expressions are differentiable as single-variable functions.
    This theorem shows that for any supported expression,
    the function `evalFunc1 e` is differentiable.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalFunc1_differentiable (e : Expr) (hsupp : ADSupported e) :
    Differentiable ℝ (evalFunc1 e) := by
  induction hsupp with
  | const q =>
    exact differentiable_const _
  | var _ =>
    exact differentiable_id
  | add _ _ ih₁ ih₂ =>
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    exact Differentiable.neg ih
  | sin _ ih =>
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    exact Real.differentiable_exp.comp ih

/-! ### Core derivative correctness micro-lemmas -/

/-- Real.cos y is always in cosInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that cosInterval uses the global bound. -/
theorem cos_mem_cosInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.cos y ∈ cosInterval I := by
  simp only [cosInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.cos_mem_Icc _

/-- Real.sin y is always in sinInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that sinInterval uses the global bound. -/
theorem sin_mem_sinInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.sin y ∈ sinInterval I := by
  simp only [sinInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.sin_mem_Icc _

/-- -Real.sin y is always in IntervalRat.neg (sinInterval I).
    This combines the sin global bound with negation for the cos derivative rule. -/
theorem neg_sin_mem_neg_sinInterval (y : ℝ) (I : IntervalRat) :
    -Real.sin y ∈ IntervalRat.neg (sinInterval I) :=
  IntervalRat.mem_neg (sin_mem_sinInterval_of_any y I)

/-- The key lemma for n-variable AD: updateVar ρ_real idx x respects mkDualEnv ρ_int idx.
    This encapsulates the repeated proof that appears in mul/exp cases. -/
theorem updateVar_mem_mkDualEnv_val (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (x : ℝ) (hx : x ∈ ρ_int idx) (hρ : ∀ i, ρ_real i ∈ ρ_int i) :
    ∀ i, Expr.updateVar ρ_real idx x i ∈ (mkDualEnv ρ_int idx i).val := by
  intro i
  by_cases hi : i = idx
  · subst hi
    simp only [Expr.updateVar_same, mkDualEnv, ↓reduceIte, DualInterval.varActive]
    exact hx
  · simp only [Expr.updateVar_other _ _ _ _ hi, mkDualEnv, ite_eq_right hi, DualInterval.varPassive]
    exact hρ i

/-! ### evalFunc1 unfolding lemmas -/

/-- Helper lemma: evalFunc1 for addition unfolds correctly -/
theorem evalFunc1_add (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = fun t => evalFunc1 e₁ t + evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for addition in Pi form -/
theorem evalFunc1_add_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = evalFunc1 e₁ + evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for multiplication unfolds correctly -/
theorem evalFunc1_mul (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = fun t => evalFunc1 e₁ t * evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for multiplication in Pi form -/
theorem evalFunc1_mul_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = evalFunc1 e₁ * evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for negation unfolds correctly -/
theorem evalFunc1_neg (e : Expr) :
    evalFunc1 (Expr.neg e) = fun t => -(evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for negation in Pi form -/
theorem evalFunc1_neg_pi (e : Expr) :
    evalFunc1 (Expr.neg e) = -evalFunc1 e := rfl

/-- Helper lemma: evalFunc1 for sin unfolds correctly -/
theorem evalFunc1_sin (e : Expr) :
    evalFunc1 (Expr.sin e) = fun t => Real.sin (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for cos unfolds correctly -/
theorem evalFunc1_cos (e : Expr) :
    evalFunc1 (Expr.cos e) = fun t => Real.cos (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for exp unfolds correctly -/
theorem evalFunc1_exp (e : Expr) :
    evalFunc1 (Expr.exp e) = fun t => Real.exp (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for log unfolds correctly -/
theorem evalFunc1_log (e : Expr) :
    evalFunc1 (Expr.log e) = fun t => Real.log (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atan unfolds correctly -/
theorem evalFunc1_atan (e : Expr) :
    evalFunc1 (Expr.atan e) = fun t => Real.arctan (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for arsinh unfolds correctly -/
theorem evalFunc1_arsinh (e : Expr) :
    evalFunc1 (Expr.arsinh e) = fun t => Real.arsinh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atanh unfolds correctly -/
theorem evalFunc1_atanh (e : Expr) :
    evalFunc1 (Expr.atanh e) = fun t => Real.atanh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for sinc unfolds correctly -/
theorem evalFunc1_sinc (e : Expr) :
    evalFunc1 (Expr.sinc e) = fun t => Real.sinc (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for erf unfolds correctly -/
theorem evalFunc1_erf (e : Expr) :
    evalFunc1 (Expr.erf e) = fun t => Real.erf (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for sqrt unfolds correctly -/
theorem evalFunc1_sqrt (e : Expr) :
    evalFunc1 (Expr.sqrt e) = fun t => Real.sqrt (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for const -/
@[simp]
theorem evalFunc1_const (q : ℚ) : evalFunc1 (Expr.const q) = fun _ => (q : ℝ) := rfl

/-- Helper lemma: evalFunc1 for var -/
@[simp]
theorem evalFunc1_var (i : ℕ) : evalFunc1 (Expr.var i) = id := rfl

/-- Helper lemma: evalFunc1 for namedConst (constant function) -/
@[simp]
theorem evalFunc1_namedConst (c : MathConst) : evalFunc1 (Expr.namedConst c) = fun _ => c.toReal
  := rfl

/-- Helper lemma: evalFunc1 for pi (constant function) -/
theorem evalFunc1_pi : evalFunc1 (Expr.namedConst .pi) = fun _ => Real.pi := rfl

/-- Helper lemma: evalFunc1 for eulerMascheroni (constant function) -/
theorem evalFunc1_eulerMascheroni : evalFunc1 (Expr.namedConst .eulerMascheroni) = fun _ =>
  Real.eulerMascheroniConstant := rfl

/-- Helper: the dual environment evaluation gives correct derivative.
    This connects the interval-based AD to actual calculus derivatives.

    FULLY PROVED - no sorry, no axioms. -/
theorem deriv_mem_dualDer (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈
      (LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dx (const) = 0
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    -- d/dx (x) = 1
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f + g) = f' + g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.add, evalFunc1_add_pi, deriv_add
      (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f * g) = f' * g + f * g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.mul, evalFunc1_mul_pi, deriv_mul
      (hd₁ x) (hd₂ x)]
    -- Need: f'(x)*g(x) + f(x)*g'(x) ∈ der₁*val₂ + val₁*der₂
    have hval₁ := LeanCert.Engine.evalDualUnchecked_val_correct _ h₁ (fun _ => x) (fun _ =>
      DualInterval.varActive I)
      (fun _ => hx)
    have hval₂ := LeanCert.Engine.evalDualUnchecked_val_correct _ h₂ (fun _ => x) (fun _ =>
      DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval₁ hval₂
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁
      (ih₂ x hx))
  | neg hs ih =>
    -- d/dx (-f) = -f'
    have hd := evalFunc1_differentiable _ hs
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    -- d/dx (sin f) = cos(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.sin, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    -- d/dx (cos f) = -sin(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.cos, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    -- d/dx (exp f) = exp(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalUnchecked, DualInterval.exp, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    -- exp(f(x)) ∈ expInterval and f'(x) ∈ der
    have hval := LeanCert.Engine.evalDualUnchecked_val_correct e' hs (fun _ => x) (fun _ =>
      DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval
    have hexp := IntervalRat.mem_expInterval hval
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- The derivative component of dual interval evaluation is correct.
    For a supported expression evaluated at a point x in the interval I,
    the derivative of the expression (as a function of x) lies in the
    computed derivative interval.

    This is the fundamental correctness theorem for forward-mode AD:
    the derivative bounds computed by interval arithmetic contain the
    true derivative at every point in the domain.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDualUnchecked_der_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈
      (LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)).der :=
  deriv_mem_dualDer e hsupp I x hx

/-! ### Generalized n-variable derivative correctness -/

/-- Helper: evalAlong is differentiable for supported expressions -/
theorem evalAlong_differentiable (e : Expr) (hsupp : ADSupported e)
    (ρ : Nat → ℝ) (idx : Nat) :
    Differentiable ℝ (Expr.evalAlong e ρ idx) := by
  induction hsupp with
  | const q =>
    simp only [Expr.evalAlong_const']
    exact differentiable_const _
  | var i =>
    by_cases h : i = idx
    · subst h
      simp only [Expr.evalAlong_var_active]
      exact differentiable_id
    · simp only [Expr.evalAlong_var_passive _ _ _ h]
      exact differentiable_const _
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_add]
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_mul]
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.evalAlong_neg]
    exact Differentiable.neg ih
  | sin _ ih =>
    simp only [Expr.evalAlong_sin]
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    simp only [Expr.evalAlong_cos]
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    simp only [Expr.evalAlong_exp]
    exact Real.differentiable_exp.comp ih

/-- The derivative of evalAlong with respect to coordinate `idx` lies in the
    computed derivative interval from mkDualEnv.

    This is the fundamental n-variable derivative correctness theorem.
    It shows that for any expression, if we differentiate along coordinate `idx`
    while holding all other coordinates fixed according to `ρ`, the derivative
    at any point `x` in the interval `ρ_int idx` lies in the computed interval.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDualUnchecked_der_correct_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈
      (LeanCert.Internal.AD.evalUnchecked e (mkDualEnv ρ_int idx)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dt (const) = 0
    simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.evalUnchecked,
      DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var i =>
    by_cases h : i = idx
    · -- Active variable: d/dt (t) = 1
      subst h
      simp only [Expr.evalAlong_var_active, LeanCert.Internal.AD.evalUnchecked, mkDualEnv,
        ↓reduceIte,
        DualInterval.varActive, deriv_id]
      convert IntervalRat.mem_singleton 1 using 1
      norm_cast
    · -- Passive variable: d/dt (const) = 0
      simp only [Expr.evalAlong_var_passive _ _ _ h, deriv_const,
        LeanCert.Internal.AD.evalUnchecked, mkDualEnv,
        ite_eq_right h, DualInterval.varPassive]
      convert IntervalRat.mem_singleton 0 using 1
      norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_add_pi, deriv_add (hd₁ x) (hd₂ x),
      LeanCert.Internal.AD.evalUnchecked, DualInterval.add]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_mul_pi, deriv_mul (hd₁ x) (hd₂ x),
      LeanCert.Internal.AD.evalUnchecked, DualInterval.mul]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval₁ := LeanCert.Engine.evalDualUnchecked_val_correct _ h₁ _ _ hmem
    have hval₂ := LeanCert.Engine.evalDualUnchecked_val_correct _ h₂ _ _ hmem
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁
      (ih₂ x hx))
  | neg hs ih =>
    have hd := evalAlong_differentiable _ hs ρ_real idx
    simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.evalUnchecked,
      DualInterval.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt),
      LeanCert.Internal.AD.evalUnchecked, DualInterval.sin]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt),
      LeanCert.Internal.AD.evalUnchecked, DualInterval.cos]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt),
      LeanCert.Internal.AD.evalUnchecked, DualInterval.exp]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval := LeanCert.Engine.evalDualUnchecked_val_correct e' hs _ _ hmem
    exact IntervalRat.mem_mul (IntervalRat.mem_expInterval hval) (ih x hx)

/-- Convenience theorem: derivInterval correctness for n-variable expressions.
    The derivative of `evalAlong e ρ idx` at any point `x` in the interval
    lies in `derivInterval e ρ_int idx`. -/
theorem derivInterval_correct_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈ derivInterval e ρ_int idx := by
  simp only [derivInterval, evalWithDeriv]
  exact LeanCert.Engine.evalDualUnchecked_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx

/-! ### Single-variable expressions -/

/-- Predicate: expression only uses variable index 0.
    This is useful for proving that different environments give the same result
    when they agree at index 0. -/
inductive UsesOnlyVar0 : Expr → Prop where
  | const (q : ℚ) : UsesOnlyVar0 (Expr.const q)
  | var0 : UsesOnlyVar0 (Expr.var 0)
  | add (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.add e₁ e₂)
  | mul (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.mul e₁ e₂)
  | neg (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.neg e)
  | inv (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.inv e)
  | sin (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sin e)
  | cos (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.cos e)
  | exp (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.exp e)
  | log (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.log e)
  | atan (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.atan e)
  | arsinh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.arsinh e)
  | atanh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.atanh e)
  | sinc (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sinc e)
  | erf (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.erf e)
  | sinh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sinh e)
  | cosh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.cosh e)
  | tanh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.tanh e)
  | sqrt (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sqrt e)
  | namedConst (c : MathConst) : UsesOnlyVar0 (Expr.namedConst c)

/-- Bridge between the canonical boolean predicate and the proof-carrying
`UsesOnlyVar0` predicate used by AD correctness lemmas. -/
theorem Expr.usesOnlyVar0_iff_UsesOnlyVar0 {e : Expr} :
    e.usesOnlyVar0 = true ↔ UsesOnlyVar0 e := by
  constructor
  · intro he
    induction e with
    | const q => exact UsesOnlyVar0.const q
    | var i =>
      simp only [Expr.usesOnlyVar0] at he
      have hi : i = 0 := beq_iff_eq.mp he
      subst hi
      exact UsesOnlyVar0.var0
    | add e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.usesOnlyVar0, Bool.and_eq_true] at he
      exact UsesOnlyVar0.add e₁ e₂ (ih₁ he.1) (ih₂ he.2)
    | mul e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.usesOnlyVar0, Bool.and_eq_true] at he
      exact UsesOnlyVar0.mul e₁ e₂ (ih₁ he.1) (ih₂ he.2)
    | neg e ih =>
      exact UsesOnlyVar0.neg e (ih he)
    | inv e ih =>
      exact UsesOnlyVar0.inv e (ih he)
    | exp e ih =>
      exact UsesOnlyVar0.exp e (ih he)
    | sin e ih =>
      exact UsesOnlyVar0.sin e (ih he)
    | cos e ih =>
      exact UsesOnlyVar0.cos e (ih he)
    | log e ih =>
      exact UsesOnlyVar0.log e (ih he)
    | atan e ih =>
      exact UsesOnlyVar0.atan e (ih he)
    | arsinh e ih =>
      exact UsesOnlyVar0.arsinh e (ih he)
    | atanh e ih =>
      exact UsesOnlyVar0.atanh e (ih he)
    | sinc e ih =>
      exact UsesOnlyVar0.sinc e (ih he)
    | erf e ih =>
      exact UsesOnlyVar0.erf e (ih he)
    | sinh e ih =>
      exact UsesOnlyVar0.sinh e (ih he)
    | cosh e ih =>
      exact UsesOnlyVar0.cosh e (ih he)
    | tanh e ih =>
      exact UsesOnlyVar0.tanh e (ih he)
    | sqrt e ih =>
      exact UsesOnlyVar0.sqrt e (ih he)
    | namedConst c =>
      exact UsesOnlyVar0.namedConst c
  · intro h
    induction h with
    | const q => rfl
    | var0 => rfl
    | add _ _ _ _ ih₁ ih₂ =>
      rw [Expr.usesOnlyVar0, ih₁, ih₂]
      rfl
    | mul _ _ _ _ ih₁ ih₂ =>
      rw [Expr.usesOnlyVar0, ih₁, ih₂]
      rfl
    | neg _ _ ih | inv _ _ ih | sin _ _ ih | cos _ _ ih | exp _ _ ih | log _ _ ih
    | atan _ _ ih | arsinh _ _ ih | atanh _ _ ih | sinc _ _ ih | erf _ _ ih
    | sinh _ _ ih | cosh _ _ ih | tanh _ _ ih | sqrt _ _ ih =>
      simpa only [Expr.usesOnlyVar0] using ih
    | namedConst c => rfl

/-- For expressions using only var 0, LeanCert.Internal.AD.evalUnchecked agrees for environments
that match at 0 -/
theorem evalDualUnchecked_congr_at_0 (e : Expr) (h : UsesOnlyVar0 e)
    (ρ₁ ρ₂ : DualEnv) (heq : ρ₁ 0 = ρ₂ 0) :
    LeanCert.Internal.AD.evalUnchecked e ρ₁ = LeanCert.Internal.AD.evalUnchecked e ρ₂ := by
  induction h generalizing ρ₁ ρ₂ with
  | const q => simp only [LeanCert.Internal.AD.evalUnchecked]
  | var0 => simp only [LeanCert.Internal.AD.evalUnchecked, heq]
  | add _ _ _ _ ih₁ ih₂ =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | mul _ _ _ _ ih₁ ih₂ =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | neg _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | inv _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked]
  | sin _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | cos _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | exp _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | log _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked]
  | atan _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | arsinh _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | atanh _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked]
  | sinc _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | erf _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | sinh _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | cosh _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | tanh _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | sqrt _ _ ih =>
    simp only [LeanCert.Internal.AD.evalUnchecked, ih ρ₁ ρ₂ heq]
  | namedConst _ =>
    simp only [LeanCert.Internal.AD.evalUnchecked]

/-- mkDualEnv at index 0 equals varActive at 0 -/
theorem mkDualEnv_at_0 (I : IntervalRat) :
    mkDualEnv (fun _ => I) 0 0 = DualInterval.varActive I := by
  simp only [mkDualEnv, ↓reduceIte]

/-- For expressions using only var 0, derivInterval equals evalWithDeriv1 -/
theorem derivInterval_eq_evalWithDeriv1_of_UsesOnlyVar0 (e : Expr) (h : UsesOnlyVar0 e)
    (I : IntervalRat) :
    derivInterval e (fun _ => I) 0 = (evalWithDeriv1 e I).der := by
  simp only [derivInterval, evalWithDeriv, evalWithDeriv1]
  -- Need to show: (LeanCert.Internal.AD.evalUnchecked e (mkDualEnv (fun _ => I) 0)).der =
  -- (LeanCert.Internal.AD.evalUnchecked e (fun _ => varActive I)).der
  have henv_eq : mkDualEnv (fun _ => I) 0 0 = (fun _ => DualInterval.varActive I) 0 := by
    simp only [mkDualEnv_at_0]
  have heq := LeanCert.Engine.evalDualUnchecked_congr_at_0 e h (mkDualEnv (fun _ => I) 0) (fun _
    => DualInterval.varActive I) henv_eq
  rw [heq]

/-- Correctness of single-variable derivative bounds -/
theorem evalWithDeriv1_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ (evalWithDeriv1 e I).val ∧
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈ (evalWithDeriv1 e I).der := by
  constructor
  · exact LeanCert.Engine.evalDualUnchecked_val_correct e hsupp (fun _ => x) _ (fun _ => hx)
  · exact LeanCert.Engine.evalDualUnchecked_der_correct e hsupp I x hx

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Automatic Differentiation - Computable Evaluators

This file provides computable dual evaluators using Taylor-based approximations
for transcendental functions. This enables `native_decide` for derivative-based
bound checking.

## Main definitions

* `DualInterval.expCore`, `sinCore`, `cosCore` - Taylor-based dual functions
* `DualInterval.sinhCore`, `coshCore`, `tanhCore` - Hyperbolic Taylor-based duals
* `LeanCert.Internal.AD.evalTotalCore` - Computable dual evaluator for ExprSupportedCore
* `derivIntervalCore` - Computable single-variable derivative interval

## Main theorems

* `LeanCert.Engine.evalDualTotalCore_val_correct` - Value component is correct
* `LeanCert.Engine.evalDualTotalCore_der_correct` - Derivative component is correct
* `derivIntervalCore_correct` - Derivative interval correctness
* `strictMonoOn_of_derivIntervalCore_pos` - Monotonicity from positive derivative
* `strictAntiOn_of_derivIntervalCore_neg` - Antitonicity from negative derivative
-/

/-! ### Computable Dual Evaluation for ExprSupportedCore

This section provides a fully computable dual evaluator that uses Taylor-based
approximations for transcendental functions. This enables `native_decide` for
derivative-based bound checking.
-/

public section

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

namespace DualInterval

/-- Computable dual for exp using Taylor series (chain rule: d(exp f) = exp(f) * f') -/
@[expose]
def expCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  let expVal := IntervalRat.expComputable d.val n
  { val := expVal
    der := IntervalRat.mul expVal d.der }

/-- Computable dual for sin using Taylor series -/
@[expose]
def sinCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinComputable d.val n
    der := IntervalRat.mul (IntervalRat.cosComputable d.val n) d.der }

/-- Computable dual for cos using Taylor series -/
@[expose]
def cosCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.cosComputable d.val n
    der := IntervalRat.mul (IntervalRat.neg (IntervalRat.sinComputable d.val n)) d.der }

/-- Computable dual for log using Taylor series via atanh reduction.
    Chain rule: d(log f) = f' / f -/
def logCore (d : DualInterval) (n : ℕ := 20) : DualInterval :=
  { val := IntervalRat.logComputable d.val n
    -- der = d.der / d.val = d.der * (1/d.val)
    der := IntervalRat.mul (invInterval d.val) d.der }

/-- Computable dual for sinh using Taylor series (chain rule: d(sinh f) = cosh(f) * f') -/
def sinhCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinhComputable d.val n
    der := IntervalRat.mul (IntervalRat.coshComputable d.val n) d.der }

/-- Computable dual for cosh using Taylor series (chain rule: d(cosh f) = sinh(f) * f') -/
def coshCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.coshComputable d.val n
    der := IntervalRat.mul (IntervalRat.sinhComputable d.val n) d.der }

/-- Computable dual for tanh (chain rule: d(tanh f) = sech²(f) * f')
    Since sech²(x) ∈ (0, 1], we use [0, 1] as a conservative bound. -/
def tanhCore (d : DualInterval) (_n : ℕ := 10) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) ∈ (0, 1], use [0, 1] as bound
    der := IntervalRat.mul d.der ⟨0, 1, by norm_num⟩ }

end DualInterval

end LeanCert.Engine

namespace LeanCert.Internal.AD

open LeanCert.Core LeanCert.Engine

/-- Computable dual interval evaluator for ExprSupportedCore expressions.

    This uses Taylor series approximations for transcendental functions,
    making it fully computable and usable with `native_decide`.

    For `inv` and `log`, use `evalDualChecked` or the bounded-denominator
    `evalDualDyadicChecked`; they validate the actual input box before exposing
    this total kernel's result. Correctness is not claimed for unchecked
    partial-operation branches here. -/
@[expose]
def evalTotalCore (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (LeanCert.Internal.AD.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.AD.evalTotalCore e₂ ρ cfg)
  | Expr.mul e₁ e₂ => DualInterval.mul (LeanCert.Internal.AD.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.AD.evalTotalCore e₂ ρ cfg)
  | Expr.neg e => DualInterval.neg (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.inv e => DualInterval.inv (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.exp e => DualInterval.expCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.sin e => DualInterval.sinCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.cos e => DualInterval.cosCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.log e => DualInterval.logCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.atan e => DualInterval.atan (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.arsinh e => DualInterval.arsinh (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.atanh _ => default
  | Expr.sinc e => DualInterval.sinc (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.erf e => DualInterval.erfCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.sinh e => DualInterval.sinhCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.cosh e => DualInterval.coshCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.tanh e => DualInterval.tanhCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.sqrt e => DualInterval.sqrt (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.namedConst c => DualInterval.ofMathConst c

end LeanCert.Internal.AD

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

/-- Computable single-variable derivative interval -/
def derivIntervalCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  (LeanCert.Internal.AD.evalTotalCore e (fun _ => DualInterval.varActive I) cfg).der

/-- Domain validity for dual evaluation.
    This is defined directly in terms of LeanCert.Internal.AD.evalTotalCore to ensure compatibility.
    For log, we require the argument interval to have positive lower bound. -/
@[expose]
def evalDomainValidDual (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidDual e₁ ρ cfg ∧ evalDomainValidDual e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidDual e₁ ρ cfg ∧ evalDomainValidDual e₂ ρ cfg
  | Expr.neg e => evalDomainValidDual e ρ cfg
  | Expr.inv e => evalDomainValidDual e ρ cfg
  | Expr.exp e => evalDomainValidDual e ρ cfg
  | Expr.sin e => evalDomainValidDual e ρ cfg
  | Expr.cos e => evalDomainValidDual e ρ cfg
  | Expr.log e => evalDomainValidDual e ρ cfg ∧ (LeanCert.Internal.AD.evalTotalCore e ρ
    cfg).val.lo > 0
  | Expr.atan e => evalDomainValidDual e ρ cfg
  | Expr.arsinh e => evalDomainValidDual e ρ cfg
  | Expr.atanh e => evalDomainValidDual e ρ cfg
  | Expr.sinc e => evalDomainValidDual e ρ cfg
  | Expr.erf e => evalDomainValidDual e ρ cfg
  | Expr.sinh e => evalDomainValidDual e ρ cfg
  | Expr.cosh e => evalDomainValidDual e ρ cfg
  | Expr.tanh e => evalDomainValidDual e ρ cfg
  | Expr.sqrt e => evalDomainValidDual e ρ cfg
  | Expr.namedConst _ => True

/-- Correctness theorem for computable dual value component.

    Note: Requires domain validity for log (positive argument interval). -/
theorem evalDualTotalCore_val_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (cfg : EvalConfig)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val)
    (hdom : evalDomainValidDual e ρ_dual cfg) :
    Expr.eval ρ_real e ∈ (LeanCert.Internal.AD.evalTotalCore e ρ_dual cfg).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.AD.evalTotalCore, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.AD.evalTotalCore]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
    exact IntervalRat.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
    exact IntervalRat.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
  | neg _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.AD.evalTotalCore, DualInterval.neg]
    exact IntervalRat.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore]
    exact IntervalRat.mem_sinComputable (ih hdom) cfg.taylorDepth
  | cos _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore]
    exact IntervalRat.mem_cosComputable (ih hdom) cfg.taylorDepth
  | exp _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore]
    exact IntervalRat.mem_expComputable (ih hdom) cfg.taylorDepth
  | sqrt _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.AD.evalTotalCore, DualInterval.sqrt]
    exact IntervalRat.mem_sqrtInterval' (ih hdom)
  | sinh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.AD.evalTotalCore, DualInterval.sinhCore]
    exact IntervalRat.mem_sinhComputable (ih hdom) cfg.taylorDepth
  | cosh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.AD.evalTotalCore, DualInterval.coshCore]
    exact IntervalRat.mem_coshComputable (ih hdom) cfg.taylorDepth
  | tanh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.AD.evalTotalCore, DualInterval.tanhCore]
    exact mem_tanhInterval (ih hdom)
  | erf _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.AD.evalTotalCore, DualInterval.erfCore]
    simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | log _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.AD.evalTotalCore, DualInterval.logCore]
    exact IntervalRat.mem_logComputable (ih hdom.1) hdom.2 cfg.taylorDepth
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.AD.evalTotalCore, DualInterval.ofMathConst]
    exact c.mem_interval

/-- For ADSupported expressions (which exclude log), domain validity is trivially true.
    This is because ADSupported has no log constructor. -/
theorem evalDomainValidDual_of_ExprSupported (e : Expr) (hsupp : ADSupported e)
    (ρ : DualEnv) (cfg : EvalConfig) : evalDomainValidDual e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | mul _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Correctness theorem for computable dual derivative component.
    Uses ADSupported since derivative correctness requires differentiability. -/
theorem evalDualTotalCore_der_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ (LeanCert.Internal.AD.evalTotalCore e (fun _ => DualInterval.varActive
      I) cfg).der := by
  induction hsupp generalizing x with
  | const q =>
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.add, evalFunc1_add_pi, deriv_add
      (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.mul, evalFunc1_mul_pi, deriv_mul
      (hd₁ x) (hd₂ x)]
    have hdom₁ := evalDomainValidDual_of_ExprSupported _ h₁ (fun _ => DualInterval.varActive I) cfg
    have hdom₂ := evalDomainValidDual_of_ExprSupported _ h₂ (fun _ => DualInterval.varActive I) cfg
    have hval₁ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₁.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom₁
    have hval₂ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₂.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom₂
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁
      (ih₂ x hx))
  | neg hs ih =>
    have hd := evalFunc1_differentiable _ hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hcos := IntervalRat.mem_cosComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hcos (ih x hx)
  | @cos e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hsin := IntervalRat.mem_sinComputable hval cfg.taylorDepth
    have hnegsin := IntervalRat.mem_neg hsin
    exact IntervalRat.mem_mul hnegsin (ih x hx)
  | @exp e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hexp := IntervalRat.mem_expComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- Convenience theorem: derivIntervalCore correctness -/
theorem derivIntervalCore_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ derivIntervalCore e I cfg :=
  LeanCert.Engine.evalDualTotalCore_der_correct e hsupp I x hx cfg

/-- If derivIntervalCore doesn't contain zero, the derivative is nonzero everywhere on I.
    This is a key theorem for Newton contraction analysis. -/
theorem derivIntervalCore_nonzero_implies_deriv_nonzero (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : ¬(derivIntervalCore e I cfg).containsZero) :
    ∀ x ∈ I, deriv (evalFunc1 e) x ≠ 0 := by
  intro x hx hcontra
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  simp only [IntervalRat.containsZero, not_and_or, not_le] at h
  rw [hcontra] at hmem
  rcases h with hlo | hhi
  · exact absurd hmem.1 (not_le.mpr (by exact_mod_cast hlo))
  · exact absurd hmem.2 (not_le.mpr (by exact_mod_cast hhi))

/-- If derivIntervalCore.lo > 0, then the derivative is positive everywhere on I. -/
theorem derivIntervalCore_pos_implies_deriv_pos (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, 0 < deriv (evalFunc1 e) x := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc (0 : ℝ) < (derivIntervalCore e I cfg).lo := by exact_mod_cast h
    _ ≤ deriv (evalFunc1 e) x := hmem.1

/-- If derivIntervalCore.hi < 0, then the derivative is negative everywhere on I. -/
theorem derivIntervalCore_neg_implies_deriv_neg (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, deriv (evalFunc1 e) x < 0 := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc deriv (evalFunc1 e) x ≤ (derivIntervalCore e I cfg).hi := hmem.2
    _ < 0 := by exact_mod_cast h

/-- Strictly positive derivative (via Core bounds) implies strict monotonicity -/
theorem strictMonoOn_of_derivIntervalCore_pos (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    StrictMonoOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_pos := derivIntervalCore_pos_implies_deriv_pos e hsupp I cfg hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative (via Core bounds) implies strict antitonicity -/
theorem strictAntiOn_of_derivIntervalCore_neg (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hneg : (derivIntervalCore e I cfg).hi < 0) :
    StrictAntiOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_neg := derivIntervalCore_neg_implies_deriv_neg e hsupp I cfg hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

end LeanCert.Engine

end

end

section

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
/-!
# Computable domain-aware automatic differentiation

This module extends LeanCert's computable forward-mode AD path with checked
reciprocal and logarithm nodes.  The existing `ADSupported` fragment remains
the domain-free fast path.  Here, successful evaluation itself certifies both
syntactic support and every partial-domain side condition.
-/

public section

namespace LeanCert.Engine

open LeanCert.Core

/-- The computable domain-aware AD fragment.  Unlike `ADSupported`, this is a
box-dependent check because reciprocal and logarithm have partial domains. -/
def checkADDomain (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : Bool :=
  match e with
  | .const _ | .var _ => true
  | .add a b | .mul a b => checkADDomain a ρ cfg && checkADDomain b ρ cfg
  | .neg a | .exp a | .sin a | .cos a => checkADDomain a ρ cfg
  | .inv a =>
      checkADDomain a ρ cfg &&
        decide (¬IntervalRat.containsZero
          (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val)
  | .log a =>
      checkADDomain a ρ cfg &&
        decide (IntervalRat.isPositive
          (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val)
  | _ => false

/-- Best-effort structured explanation for a failed domain-aware AD check. -/
def diagnoseADDomainFailure (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : EvalError :=
  match e with
  | .add a b | .mul a b =>
      if checkADDomain a ρ cfg then
        .nestedFailure "right operand" (diagnoseADDomainFailure b ρ cfg)
      else
        .nestedFailure "left operand" (diagnoseADDomainFailure a ρ cfg)
  | .neg a | .exp a | .sin a | .cos a =>
      .nestedFailure "unary operand" (diagnoseADDomainFailure a ρ cfg)
  | .inv a =>
      if checkADDomain a ρ cfg then
        .reciprocalContainsZero (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val
      else
        .nestedFailure "reciprocal operand" (diagnoseADDomainFailure a ρ cfg)
  | .log a =>
      if checkADDomain a ρ cfg then
        .logNonpositive (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val
      else
        .nestedFailure "logarithm operand" (diagnoseADDomainFailure a ρ cfg)
  | .const _ | .var _ => .invalidConfiguration "successful AD expression diagnosed as failure"
  | _ => .unsupportedFeature "domain-aware automatic differentiation"

/-- Computable checked dual evaluation.  No finite derivative enclosure is
returned unless every reciprocal denominator excludes zero and every logarithm
argument is strictly positive on the input box. -/
def evalDualChecked (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) :
    EvalResult DualInterval :=
  if checkADDomain e ρ cfg then
    .ok (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  else
    .error (diagnoseADDomainFailure e ρ cfg)

/-- Checked value-and-derivative evaluation along coordinate `idx`. -/
def evalWithDerivChecked (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (cfg : EvalConfig := {}) : EvalResult DualInterval :=
  evalDualChecked e (mkDualEnv ρ idx) cfg

/-- Checked derivative enclosure along coordinate `idx`. -/
def derivIntervalChecked (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (cfg : EvalConfig := {}) : EvalResult IntervalRat :=
  return (← evalWithDerivChecked e ρ idx cfg).der

/-- Checked derivative enclosure for a single-variable expression. -/
def derivIntervalChecked1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) :
    EvalResult IntervalRat :=
  derivIntervalChecked e (fun _ => I) 0 cfg

private theorem checkADDomain_of_evalDualChecked_ok {e : Expr} {ρ : DualEnv}
    {cfg : EvalConfig} {D : DualInterval} (h : evalDualChecked e ρ cfg = .ok D) :
    checkADDomain e ρ cfg = true := by
  simp only [evalDualChecked] at h
  split at h
  · assumption
  · contradiction

private theorem evalDualChecked_ok_eq {e : Expr} {ρ : DualEnv}
    {cfg : EvalConfig} {D : DualInterval} (h : evalDualChecked e ρ cfg = .ok D) :
    D = LeanCert.Internal.AD.evalTotalCore e ρ cfg := by
  simp only [evalDualChecked] at h
  split at h
  · exact (Except.ok.inj h).symm
  · contradiction

private theorem not_containsZero_cases {I : IntervalRat}
    (h : ¬IntervalRat.containsZero I) : I.lo > 0 ∨ I.hi < 0 := by
  simp only [IntervalRat.containsZero, not_and_or, not_le] at h
  exact h

private theorem evalTotalCore_val_correct_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρDual : DualEnv) (cfg : EvalConfig)
    (hρ : ∀ i, ρReal i ∈ (ρDual i).val)
    (hcheck : checkADDomain e ρDual cfg = true) :
    Expr.eval ρReal e ∈ (LeanCert.Internal.AD.evalTotalCore e ρDual cfg).val := by
  induction e with
  | const q =>
      exact IntervalRat.mem_singleton q
  | var i =>
      exact hρ i
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simp only [Expr.eval_add, LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
      exact IntervalRat.mem_add (iha hcheck.1) (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simp only [Expr.eval_mul, LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
      exact IntervalRat.mem_mul (iha hcheck.1) (ihb hcheck.2)
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_neg (ih hcheck)
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      simp only [Expr.eval_inv, LeanCert.Internal.AD.evalTotalCore, DualInterval.inv]
      exact mem_invInterval_nonzero (ih hcheck.1) (not_containsZero_cases hcheck.2)
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_expComputable (ih hcheck) cfg.taylorDepth
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_sinComputable (ih hcheck) cfg.taylorDepth
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_cosComputable (ih hcheck) cfg.taylorDepth
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact IntervalRat.mem_logComputable (ih hcheck.1) hcheck.2 cfg.taylorDepth
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- Successful checked dual evaluation encloses the expression value for every
real environment represented by the dual environment. -/
theorem evalDualChecked_val_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρDual : DualEnv) (cfg : EvalConfig) (D : DualInterval)
    (hρ : ∀ i, ρReal i ∈ (ρDual i).val)
    (hok : evalDualChecked e ρDual cfg = .ok D) :
    Expr.eval ρReal e ∈ D.val := by
  rw [evalDualChecked_ok_eq hok]
  exact evalTotalCore_val_correct_of_check e ρReal ρDual cfg hρ
    (checkADDomain_of_evalDualChecked_ok hok)

private theorem evalAlong_differentiableAt_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (x : ℝ) (hx : x ∈ ρInt idx) (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hcheck : checkADDomain e (mkDualEnv ρInt idx) cfg = true) :
    DifferentiableAt ℝ (Expr.evalAlong e ρReal idx) x := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈ (mkDualEnv ρInt idx i).val :=
    updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ
  induction e with
  | const => exact differentiableAt_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simpa only [Expr.evalAlong_var_active] using differentiableAt_id
      · simpa only [Expr.evalAlong_var_passive _ _ _ hi] using differentiableAt_const (c := ρReal i)
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simpa only [Expr.evalAlong_add_pi] using (iha hcheck.1).add (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simpa only [Expr.evalAlong_mul_pi] using (iha hcheck.1).mul (ihb hcheck.2)
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      simpa only [Expr.evalAlong_neg_pi] using (ih hcheck).neg
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hne : Expr.evalAlong a ρReal idx x ≠ 0 := by
        rw [Expr.evalAlong_eq]
        intro hz
        rw [hz] at hval
        exact hcheck.2 ⟨by exact_mod_cast hval.1, by exact_mod_cast hval.2⟩
      exact DifferentiableAt.inv (ih hcheck.1) hne
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_exp.comp x (ih hcheck)
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_sin.comp x (ih hcheck)
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_cos.comp x (ih hcheck)
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hpos : 0 < Expr.evalAlong a ρReal idx x := by
        rw [Expr.evalAlong_eq]
        exact lt_of_lt_of_le (by exact_mod_cast hcheck.2) hval.1
      exact (Real.differentiableAt_log (ne_of_gt hpos)).comp x (ih hcheck.1)
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- A successful checked evaluation proves differentiability at every point in
the input box along the selected coordinate. -/
theorem evalWithDerivChecked_differentiableAt (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (D : DualInterval) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : evalWithDerivChecked e ρInt idx cfg = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong e ρReal idx) x := by
  exact evalAlong_differentiableAt_of_check e ρReal ρInt idx cfg x hx hρ
    (checkADDomain_of_evalDualChecked_ok hok)

private theorem evalTotalCore_der_correct_idx_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (x : ℝ) (hx : x ∈ ρInt idx) (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hcheck : checkADDomain e (mkDualEnv ρInt idx) cfg = true) :
    deriv (Expr.evalAlong e ρReal idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e (mkDualEnv ρInt idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈ (mkDualEnv ρInt idx i).val :=
    updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ
  induction e with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, deriv_id, LeanCert.Internal.AD.evalTotalCore,
          mkDualEnv, ↓reduceIte, DualInterval.varActive]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.evalTotalCore, mkDualEnv, ite_eq_right hi, DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      have hda := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      have hdb := evalAlong_differentiableAt_of_check b ρReal ρInt idx cfg x hx hρ hcheck.2
      simp only [Expr.evalAlong_add_pi, deriv_add hda hdb, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.add]
      exact IntervalRat.mem_add (iha hcheck.1) (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      have hda := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      have hdb := evalAlong_differentiableAt_of_check b ρReal ρInt idx cfg x hx hρ hcheck.2
      simp only [Expr.evalAlong_mul_pi, deriv_mul hda hdb, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.mul]
      have hva := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hvb := evalTotalCore_val_correct_of_check b (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.2
      exact IntervalRat.mem_add (IntervalRat.mem_mul (iha hcheck.1) hvb)
        (IntervalRat.mem_mul hva (ihb hcheck.2))
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.neg]
      exact IntervalRat.mem_neg (ih hcheck)
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hval' : Expr.evalAlong a ρReal idx x ∈
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        simpa only [Expr.evalAlong_eq] using hval
      have hne : Expr.evalAlong a ρReal idx x ≠ 0 := by
        intro hz
        rw [hz] at hval'
        exact hcheck.2 ⟨by exact_mod_cast hval'.1, by exact_mod_cast hval'.2⟩
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      rw [Expr.evalAlong_inv]
      have hcomp : (fun t => (Expr.evalAlong a ρReal idx t)⁻¹) =
          (fun y : ℝ => y⁻¹) ∘ Expr.evalAlong a ρReal idx := rfl
      rw [hcomp, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [(hasDerivAt_inv hne).deriv, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.inv]
      have hder := ih hcheck.1
      have hinv := mem_invInterval_nonzero hval' (not_containsZero_cases hcheck.2)
      have hneg := IntervalRat.mem_neg
        (IntervalRat.mem_mul hder (IntervalRat.mem_mul hinv hinv))
      convert hneg using 1
      field_simp
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_exp, deriv_exp hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.expCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih hcheck)
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_sin, deriv_sin hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.sinCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih hcheck)
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_cos, deriv_cos hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.cosCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg (IntervalRat.mem_sinComputable hval cfg.taylorDepth)) (ih hcheck)
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hval' : Expr.evalAlong a ρReal idx x ∈
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        simpa only [Expr.evalAlong_eq] using hval
      have hpos : 0 < Expr.evalAlong a ρReal idx x :=
        lt_of_lt_of_le (by exact_mod_cast hcheck.2) hval'.1
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      rw [Expr.evalAlong_log]
      have hcomp : (fun t => Real.log (Expr.evalAlong a ρReal idx t)) =
          Real.log ∘ Expr.evalAlong a ρReal idx := rfl
      rw [hcomp, deriv_comp x (Real.differentiableAt_log (ne_of_gt hpos)) hd]
      simp only [Real.deriv_log, LeanCert.Internal.AD.evalTotalCore, DualInterval.logCore]
      have hder := ih hcheck.1
      have hnz : ¬IntervalRat.containsZero
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        intro hz
        exact (not_lt_of_ge hz.1) hcheck.2
      have hinv := mem_invInterval_nonzero hval' (not_containsZero_cases hnz)
      exact IntervalRat.mem_mul hinv hder
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- Successful checked indexed AD encloses the true partial derivative. -/
theorem evalWithDerivChecked_der_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (D : DualInterval) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : evalWithDerivChecked e ρInt idx cfg = .ok D) :
    deriv (Expr.evalAlong e ρReal idx) x ∈ D.der := by
  rw [evalDualChecked_ok_eq hok]
  exact evalTotalCore_der_correct_idx_of_check e ρReal ρInt idx cfg x hx hρ
    (checkADDomain_of_evalDualChecked_ok hok)

/-- Golden soundness theorem for the checked derivative-only API. -/
theorem derivIntervalChecked_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (dI : IntervalRat) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : derivIntervalChecked e ρInt idx cfg = .ok dI) :
    deriv (Expr.evalAlong e ρReal idx) x ∈ dI := by
  simp only [derivIntervalChecked, bind, Except.bind] at hok
  cases hdual : evalWithDerivChecked e ρInt idx cfg with
  | error err => simp [hdual] at hok
  | ok D =>
      rw [hdual] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst dI
      exact evalWithDerivChecked_der_correct e ρReal ρInt idx cfg D x hx hρ hdual

end LeanCert.Engine

end

end
