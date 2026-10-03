/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Abstract integration by parts in time (`s.indy#Q-primitive`, `s.indy#ibp-in-time`)

Source: `enhance.tex` 8700–8830.  A mean-zero `P`-periodic continuous function `G` with
`N P = 1` has the primitive `Q(t) = ∫_0^t G`, which is bounded by `P ‖G‖_∞` and vanishes at
`t = 0` and `t = 1`; integrating by parts against an absolutely-differentiable `A` gives
`|∫_0^1 G A| ≤ P ‖G‖_∞ ∫_0^1 |A'|`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace AVenhance.Infra.Section5.LeftToShow

/-- A `P`-periodic function with `N P = 1` that has mean zero on `[0,1]` has mean zero on a
single period. -/
theorem integral_period_eq_zero_of_unit {G : ℝ → ℝ} {P : ℝ} {N : ℕ}
    (hNP : (N : ℝ) * P = 1) (hG : Continuous G) (hGper : Function.Periodic G P)
    (hGmean : ∫ t in (0 : ℝ)..1, G t = 0) : ∫ t in (0 : ℝ)..P, G t = 0 := by
  have hN : (N : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hNP
    exact zero_ne_one hNP
  have hz := hGper.intervalIntegral_add_zsmul_eq (N : ℤ) 0 (fun a b => hG.intervalIntegrable a b)
  have hcast : ((N : ℤ) • P : ℝ) = 1 := by simpa using hNP
  rw [zero_add, zero_add, hcast, hGmean] at hz
  have : (N : ℝ) * ∫ t in (0 : ℝ)..P, G t = 0 := by simpa using hz.symm
  exact (mul_eq_zero.mp this).resolve_left hN

/-- Abstract `s.indy#Q-primitive` + `s.indy#ibp-in-time`. -/
theorem abs_intervalIntegral_mul_le_of_periodic_mean_zero {G A A' : ℝ → ℝ} {P B : ℝ} {N : ℕ}
    (hP : 0 < P) (hNP : (N : ℝ) * P = 1) (hG : Continuous G) (hGper : Function.Periodic G P)
    (hGmean : ∫ t in (0 : ℝ)..1, G t = 0) (hB : ∀ t, |G t| ≤ B)
    (hA : ContinuousOn A (Set.Icc 0 1)) (hA' : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt A (A' t) t)
    (hA'int : IntervalIntegrable A' MeasureSpace.volume 0 1) :
    |∫ t in (0 : ℝ)..1, G t * A t| ≤ P * B * ∫ t in (0 : ℝ)..1, |A' t| := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmean := integral_period_eq_zero_of_unit hNP hG hGper hGmean
  have hQbound : ∀ t, |periodicPrimitive G t| ≤ P * B :=
    periodicPrimitive_abs_le hP hG hGper hmean hB0 fun t _ => hB t
  have hQ0 : periodicPrimitive G 0 = 0 := by simp [periodicPrimitive]
  have hQ1 : periodicPrimitive G 1 = 0 := hGmean
  have hQcont : Continuous (periodicPrimitive G) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (periodicPrimitive_hasDerivAt hG t).continuousAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := 1) (u := A) (v := periodicPrimitive G) (u' := A') (v' := G)
    (by simpa [Set.uIcc_of_le zero_le_one] using hA) hQcont.continuousOn
    (by simpa using hA') (fun x _ => periodicPrimitive_hasDerivAt hG x) hA'int
    (hG.intervalIntegrable 0 1)
  have hcomm : ∫ t in (0 : ℝ)..1, G t * A t = ∫ t in (0 : ℝ)..1, A t * G t :=
    intervalIntegral.integral_congr fun t _ => mul_comm _ _
  rw [hcomm, hibp, hQ0, hQ1]
  simp only [mul_zero, sub_zero, zero_sub, abs_neg]
  have hle : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖A' t * periodicPrimitive G t‖ ≤ (P * B) * ‖A' t‖ := by
    intro t _
    rw [norm_mul, Real.norm_eq_abs, mul_comm (P * B)]
    exact mul_le_mul_of_nonneg_left (hQbound t) (abs_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall hle)
    (g := fun t => (P * B) * ‖A' t‖) ((hA'int.norm).const_mul (P * B))
  simpa [intervalIntegral.integral_const_mul, Real.norm_eq_abs] using this

end AVenhance.Infra.Section5.LeftToShow

end
