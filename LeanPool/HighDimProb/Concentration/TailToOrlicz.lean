/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.OrliczToTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Tail-to-Orlicz proof boundary

Verified Wikipedia references:
* Layer-cake representation: https://en.wikipedia.org/wiki/Layer_cake_representation
* Orlicz space: https://en.wikipedia.org/wiki/Orlicz_space
* Markov's inequality: https://en.wikipedia.org/wiki/Markov%27s_inequality

This module develops the first reverse implication from scalar tail bounds to
Orlicz bounds, together with reusable layer-cake bridges for future proofs.

The `ψ₂` reverse implication is proved with the scale loss `K -> 2 * K`.
The analogous `ψ₁` reverse implication is proved with the scale loss `K -> 3 * K`.
-/

namespace HighDimProb

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A HighDimProb-facing layer-cake bridge for nonnegative real random variables. -/
theorem lintegral_ofReal_eq_lintegral_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Y : RealRandomVariable Ω}
    (hY_nonneg : ∀ ω, 0 ≤ Y ω) (hY : IsRealRandomVariable P Y) :
    (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) =
      ∫⁻ t in Set.Ioi (0 : ℝ), P {ω : Ω | t ≤ Y ω} := by
  simpa using
    MeasureTheory.lintegral_eq_lintegral_meas_le P
      (ae_of_all P hY_nonneg) hY.aemeasurable

/--
Concrete ENNReal form of the elementary integral
`∫_0^∞ (1/2) exp (-(3/4)t) dt = 2/3 <= 1`.

This is the decay integral that appears after applying layer cake to
`exp (Z / 4) - 1` and using a tail bound of the form
`P(Z >= t) <= 2 exp(-t)`.
-/
theorem lintegral_half_exp_neg_three_quarters_le_one :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * t)) ∂volume) ≤
      (1 : ENNReal) := by
  have h_int :
      IntegrableOn
        (fun t : ℝ => (1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * t))
        (Set.Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(3 / 4 : ℝ)) (by norm_num) 0).const_mul _
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => (1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * t) := by
    exact ae_of_all _ fun t => mul_nonneg (by norm_num) (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  have h_eval :
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * t)) = (2 / 3 : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * t))
          = (1 / 2 : ℝ) *
              (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(3 / 4 : ℝ) * t)) := by
            rw [integral_const_mul]
      _ = (2 / 3 : ℝ) := by
            rw [integral_exp_mul_Ioi (a := -(3 / 4 : ℝ)) (by norm_num) 0]
            norm_num
  rw [h_eval]
  norm_num

/--
Concrete ENNReal form of the elementary integral
`∫_0^∞ (2/3) exp (-(2/3)t) dt = 1`.

This is the decay integral that appears after applying layer cake to
`exp (Z / 3) - 1` and using a tail bound of the form
`P(Z >= t) <= 2 exp(-t)`.
-/
theorem lintegral_two_thirds_exp_neg_two_thirds_le_one :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * t)) ∂volume) ≤
      (1 : ENNReal) := by
  have h_int :
      IntegrableOn
        (fun t : ℝ => (2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * t))
        (Set.Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(2 / 3 : ℝ)) (by norm_num) 0).const_mul _
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => (2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * t) := by
    exact ae_of_all _ fun t => mul_nonneg (by norm_num) (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  have h_eval :
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * t)) = (1 : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * t))
          = (2 / 3 : ℝ) *
              (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(2 / 3 : ℝ) * t)) := by
            rw [integral_const_mul]
      _ = (1 : ℝ) := by
            rw [integral_exp_mul_Ioi (a := -(2 / 3 : ℝ)) (by norm_num) 0]
            norm_num
  rw [h_eval]
  norm_num

/-- Finite-interval primitive used in the exponential layer-cake estimate. -/
theorem integral_quarter_exp_quarter
    (z : ℝ) :
    (∫ t in 0..z, (1 / 4 : ℝ) * Real.exp (t / 4)) =
      Real.exp (z / 4) - 1 := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) z,
        HasDerivAt (fun u : ℝ => Real.exp (u / 4))
          ((1 / 4 : ℝ) * Real.exp (t / 4)) t := by
    intro t _ht
    simpa [mul_comm] using (((hasDerivAt_id t).div_const (4 : ℝ)).exp)
  have hint :
      IntervalIntegrable
        (fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4)) volume 0 z := by
    have hcont : Continuous fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  calc
    (∫ t in 0..z, (1 / 4 : ℝ) * Real.exp (t / 4))
        = Real.exp (z / 4) - Real.exp ((0 : ℝ) / 4) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Real.exp (z / 4) - 1 := by simp

/-- Finite-interval primitive used in the linear-exponential layer-cake estimate. -/
theorem integral_third_exp_third
    (z : ℝ) :
    (∫ t in 0..z, (1 / 3 : ℝ) * Real.exp (t / 3)) =
      Real.exp (z / 3) - 1 := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) z,
        HasDerivAt (fun u : ℝ => Real.exp (u / 3))
          ((1 / 3 : ℝ) * Real.exp (t / 3)) t := by
    intro t _ht
    simpa [mul_comm] using (((hasDerivAt_id t).div_const (3 : ℝ)).exp)
  have hint :
      IntervalIntegrable
        (fun t : ℝ => (1 / 3 : ℝ) * Real.exp (t / 3)) volume 0 z := by
    have hcont : Continuous fun t : ℝ => (1 / 3 : ℝ) * Real.exp (t / 3) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  calc
    (∫ t in 0..z, (1 / 3 : ℝ) * Real.exp (t / 3))
        = Real.exp (z / 3) - Real.exp ((0 : ℝ) / 3) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Real.exp (z / 3) - 1 := by simp

/--
Abstract exponential-tail to exponential-moment bridge.

If a nonnegative real random variable `Z` has tail bounded by `2 * exp(-s)`,
then `exp (Z / 4) - 1` has shifted exponential moment at most `1`.
-/
theorem lintegral_exp_quarter_sub_one_le_of_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : RealRandomVariable Ω}
    (hZ_nonneg : ∀ ω, 0 ≤ Z ω) (hZ : IsRealRandomVariable P Z)
    (hTail :
      ∀ s : ℝ, 0 ≤ s →
        P {ω : Ω | s ≤ Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-s))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 4) - 1) ∂P) ≤
      (1 : ENNReal) := by
  let g : ℝ → ℝ := fun s => (1 / 4 : ℝ) * Real.exp (s / 4)
  have h_left :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 4) - 1) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (∫ s in 0..Z ω, g s) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all P fun ω => by
      change ENNReal.ofReal (Real.exp (Z ω / 4) - 1) =
        ENNReal.ofReal (∫ s in 0..Z ω, (1 / 4 : ℝ) * Real.exp (s / 4))
      rw [integral_quarter_exp_quarter (Z ω)]
  have h_g_int :
      ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t _ht
    exact (by fun_prop : Continuous g).intervalIntegrable _ _
  have h_g_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g t := by
    exact ae_of_all _ fun t => mul_nonneg (by norm_num) (Real.exp_pos _).le
  have h_layer :
      (∫⁻ ω, ENNReal.ofReal (∫ s in 0..Z ω, g s) ∂P) =
        ∫⁻ s in Set.Ioi (0 : ℝ), P {ω : Ω | s ≤ Z ω} * ENNReal.ofReal (g s) := by
    simpa [g] using
      MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul P
        (ae_of_all P hZ_nonneg) hZ.aemeasurable h_g_int h_g_nonneg
  rw [h_left, h_layer]
  refine
    (lintegral_mono_ae ?_).trans
      lintegral_half_exp_neg_three_quarters_le_one
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hg_nonneg : 0 ≤ g s := mul_nonneg (by norm_num) (Real.exp_pos _).le
  calc
    P {ω : Ω | s ≤ Z ω} * ENNReal.ofReal (g s)
        = ENNReal.ofReal (g s) * P {ω : Ω | s ≤ Z ω} := by rw [mul_comm]
    _ ≤ ENNReal.ofReal (g s) * ENNReal.ofReal (2 * Real.exp (-s)) := by
          gcongr
          exact hTail s hs_nonneg
    _ = ENNReal.ofReal (2 * Real.exp (-s)) * ENNReal.ofReal (g s) := by rw [mul_comm]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * s)) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp (-s))]
          congr 1
          simp only [g]
          calc
            2 * Real.exp (-s) * (1 / 4 * Real.exp (s / 4))
                = (1 / 2 : ℝ) * (Real.exp (-s) * Real.exp (s / 4)) := by ring
            _ = (1 / 2 : ℝ) * Real.exp (-s + s / 4) := by rw [Real.exp_add]
            _ = (1 / 2 : ℝ) * Real.exp (-(3 / 4 : ℝ) * s) := by
              congr 1
              ring_nf

/--
Linear-exponential tail to exponential-moment bridge.

If a nonnegative real random variable `Z` has tail bounded by `2 * exp(-s)`,
then `exp (Z / 3) - 1` has shifted exponential moment at most `1`.
-/
theorem lintegral_exp_third_sub_one_le_of_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : RealRandomVariable Ω}
    (hZ_nonneg : ∀ ω, 0 ≤ Z ω) (hZ : IsRealRandomVariable P Z)
    (hTail :
      ∀ s : ℝ, 0 ≤ s →
        P {ω : Ω | s ≤ Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-s))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 3) - 1) ∂P) ≤
      (1 : ENNReal) := by
  let g : ℝ → ℝ := fun s => (1 / 3 : ℝ) * Real.exp (s / 3)
  have h_left :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 3) - 1) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (∫ s in 0..Z ω, g s) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all P fun ω => by
      change ENNReal.ofReal (Real.exp (Z ω / 3) - 1) =
        ENNReal.ofReal (∫ s in 0..Z ω, (1 / 3 : ℝ) * Real.exp (s / 3))
      rw [integral_third_exp_third (Z ω)]
  have h_g_int :
      ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t _ht
    exact (by fun_prop : Continuous g).intervalIntegrable _ _
  have h_g_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g t := by
    exact ae_of_all _ fun t => mul_nonneg (by norm_num) (Real.exp_pos _).le
  have h_layer :
      (∫⁻ ω, ENNReal.ofReal (∫ s in 0..Z ω, g s) ∂P) =
        ∫⁻ s in Set.Ioi (0 : ℝ), P {ω : Ω | s ≤ Z ω} * ENNReal.ofReal (g s) := by
    simpa [g] using
      MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul P
        (ae_of_all P hZ_nonneg) hZ.aemeasurable h_g_int h_g_nonneg
  rw [h_left, h_layer]
  refine
    (lintegral_mono_ae ?_).trans
      lintegral_two_thirds_exp_neg_two_thirds_le_one
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hg_nonneg : 0 ≤ g s := mul_nonneg (by norm_num) (Real.exp_pos _).le
  calc
    P {ω : Ω | s ≤ Z ω} * ENNReal.ofReal (g s)
        = ENNReal.ofReal (g s) * P {ω : Ω | s ≤ Z ω} := by rw [mul_comm]
    _ ≤ ENNReal.ofReal (g s) * ENNReal.ofReal (2 * Real.exp (-s)) := by
          gcongr
          exact hTail s hs_nonneg
    _ = ENNReal.ofReal (2 * Real.exp (-s)) * ENNReal.ofReal (g s) := by rw [mul_comm]
    _ = ENNReal.ofReal ((2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * s)) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp (-s))]
          congr 1
          simp only [g]
          calc
            2 * Real.exp (-s) * (1 / 3 * Real.exp (s / 3))
                = (2 / 3 : ℝ) * (Real.exp (-s) * Real.exp (s / 3)) := by ring
            _ = (2 / 3 : ℝ) * Real.exp (-s + s / 3) := by rw [Real.exp_add]
            _ = (2 / 3 : ℝ) * Real.exp (-(2 / 3 : ℝ) * s) := by
              congr 1
              ring_nf

/--
Specialized exponential-square estimate from a subGaussian tail bound.

This is the analytic core for the reverse implication
`SubGaussianTail P X K -> Psi2Bound P X (2 * K)`.
-/
theorem lintegral_exp_sq_div_four_sub_one_le_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    (∫⁻ ω,
        ENNReal.ofReal (Real.exp ((|X ω| / (2 * K)) ^ 2) - 1) ∂P) ≤
      (1 : ENNReal) := by
  rcases hTail with ⟨hK, hTail_bound⟩
  let Z : RealRandomVariable Ω := fun ω => (|X ω| / K) ^ 2
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := fun ω => sq_nonneg _
  have hZ_meas : IsRealRandomVariable P Z := by
    have h_abs : Measurable fun ω => |X ω| := by
      simpa [Real.norm_eq_abs] using hX.norm
    exact (h_abs.div_const K).pow_const 2
  have hZ_tail :
      ∀ s : ℝ, 0 ≤ s →
        P {ω : Ω | s ≤ Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-s)) := by
    intro s hs
    have h_event : {ω : Ω | s ≤ Z ω} ⊆ absTailEvent X (K * Real.sqrt s) := by
      intro ω hω
      have hquot_nonneg : 0 ≤ |X ω| / K := div_nonneg (abs_nonneg _) hK.le
      have hsqrt_le : Real.sqrt s ≤ |X ω| / K := by
        have hsq : (Real.sqrt s) ^ 2 ≤ (|X ω| / K) ^ 2 := by
          simpa [Z, Real.sq_sqrt hs] using hω
        exact (sq_le_sq₀ (Real.sqrt_nonneg _) hquot_nonneg).mp hsq
      have hmul : K * Real.sqrt s ≤ |X ω| := by
        calc
          K * Real.sqrt s ≤ K * (|X ω| / K) := by
            exact mul_le_mul_of_nonneg_left hsqrt_le hK.le
          _ = |X ω| := by
            field_simp [hK.ne']
      exact hmul
    have ht_nonneg : 0 ≤ K * Real.sqrt s :=
      mul_nonneg hK.le (Real.sqrt_nonneg _)
    have h_tail := hTail_bound (K * Real.sqrt s) ht_nonneg
    calc
      P {ω : Ω | s ≤ Z ω}
          ≤ absTailProb P X (K * Real.sqrt s) := measure_mono h_event
      _ ≤ ENNReal.ofReal
            (2 * Real.exp (-((K * Real.sqrt s) ^ 2 / K ^ 2))) := h_tail
      _ = ENNReal.ofReal (2 * Real.exp (-s)) := by
            congr 1
            congr 1
            have hsq : (K * Real.sqrt s) ^ 2 / K ^ 2 = s := by
              rw [mul_pow, Real.sq_sqrt hs]
              field_simp [hK.ne']
            rw [hsq]
  have h_core :=
    lintegral_exp_quarter_sub_one_le_of_exp_tail
      (P := P) (Z := Z) hZ_nonneg hZ_meas hZ_tail
  have h_eq :
      (∫⁻ ω,
          ENNReal.ofReal (Real.exp ((|X ω| / (2 * K)) ^ 2) - 1) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 4) - 1) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all P fun ω => by
      apply congrArg ENNReal.ofReal
      congr 1
      simp only [Z]
      field_simp [hK.ne']
      ring_nf
  rw [h_eq]
  exact h_core

/--
SubGaussian tail control implies the shifted `ψ₂` Orlicz bound after the
standard scale loss `K -> 2 * K`.
-/
theorem psi2Bound_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    Psi2Bound P X (2 * K) := by
  refine ⟨?_, ?_⟩
  · nlinarith [hTail.1]
  · exact lintegral_exp_sq_div_four_sub_one_le_of_subGaussianTail
      (P := P) (X := X) (K := K) hX hTail

/--
Specialized exponential-linear estimate from a subExponential tail bound.

This is the analytic core for the reverse implication
`SubExponentialTail P X K -> Psi1Bound P X (3 * K)`.
-/
theorem lintegral_exp_abs_div_three_sub_one_le_of_subExponentialTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K) :
    (∫⁻ ω,
        ENNReal.ofReal (Real.exp (|X ω| / (3 * K)) - 1) ∂P) ≤
      (1 : ENNReal) := by
  rcases hTail with ⟨hK, hTail_bound⟩
  let Z : RealRandomVariable Ω := fun ω => |X ω| / K
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := fun ω => div_nonneg (abs_nonneg _) hK.le
  have hZ_meas : IsRealRandomVariable P Z := by
    have h_abs : Measurable fun ω => |X ω| := by
      simpa [Real.norm_eq_abs] using hX.norm
    exact h_abs.div_const K
  have hZ_tail :
      ∀ s : ℝ, 0 ≤ s →
        P {ω : Ω | s ≤ Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-s)) := by
    intro s hs
    have h_event : {ω : Ω | s ≤ Z ω} ⊆ absTailEvent X (K * s) := by
      intro ω hω
      have hmul : K * s ≤ |X ω| := by
        calc
          K * s ≤ K * (|X ω| / K) := by
            exact mul_le_mul_of_nonneg_left hω hK.le
          _ = |X ω| := by
            field_simp [hK.ne']
      exact hmul
    have ht_nonneg : 0 ≤ K * s := mul_nonneg hK.le hs
    have h_tail := hTail_bound (K * s) ht_nonneg
    calc
      P {ω : Ω | s ≤ Z ω}
          ≤ absTailProb P X (K * s) := measure_mono h_event
      _ ≤ ENNReal.ofReal
            (2 * Real.exp (-((K * s) / K))) := h_tail
      _ = ENNReal.ofReal (2 * Real.exp (-s)) := by
            congr 1
            congr 1
            field_simp [hK.ne']
  have h_core :=
    lintegral_exp_third_sub_one_le_of_exp_tail
      (P := P) (Z := Z) hZ_nonneg hZ_meas hZ_tail
  have h_eq :
      (∫⁻ ω,
          ENNReal.ofReal (Real.exp (|X ω| / (3 * K)) - 1) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω / 3) - 1) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all P fun ω => by
      apply congrArg ENNReal.ofReal
      congr 1
      simp only [Z]
      field_simp [hK.ne']
  rw [h_eq]
  exact h_core

/--
SubExponential tail control implies the shifted `ψ₁` Orlicz bound after the
standard scale loss `K -> 3 * K`.
-/
theorem psi1Bound_of_subExponentialTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K) :
    Psi1Bound P X (3 * K) := by
  unfold Psi1Bound
  constructor
  · have hthree : 0 < (3 : ℝ) := by norm_num
    exact mul_pos hthree hTail.1
  · exact lintegral_exp_abs_div_three_sub_one_le_of_subExponentialTail
      (P := P) (X := X) (K := K) hX hTail

/--
Typed proof target: a subGaussian tail bound should imply a `ψ₂` bound after
the standard constant loss.

This is kept as a specification alias for the proved theorem
`psi2Bound_of_subGaussianTail`.
-/
abbrev psi2BoundOfSubGaussianTailStatement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  IsRealRandomVariable P X →
    SubGaussianTail P X K →
      Psi2Bound P X (2 * K)

/--
Typed proof target: a subExponential tail bound should imply a `ψ₁`
bound after the standard constant loss.

This is kept as a specification alias for the proved theorem
`psi1Bound_of_subExponentialTail`.
-/
abbrev psi1BoundOfSubExponentialTailStatement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  IsRealRandomVariable P X →
    SubExponentialTail P X K →
      Psi1Bound P X (3 * K)

end

end HighDimProb
