/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
An explicit smooth terminal-layer trial profile.  Its endpoint values are
zero and one, and its squared value/derivative integrals are at most `2/L`
and `2*L` when `L*T ≥ 1`.  These are the same energy bounds needed for the
piecewise linear terminal ramp in the activation argument.
-/

noncomputable section

namespace EulerTerminalLayerRamp

open Set MeasureTheory

def ramp (T L t : ℝ) : ℝ :=
  (Real.exp (L * (t - T)) - Real.exp (-L * T)) / (1 - Real.exp (-L * T))

def rampDerivative (T L t : ℝ) : ℝ :=
  L * Real.exp (L * (t - T)) / (1 - Real.exp (-L * T))

theorem denominator_lower {T L : ℝ} (hLT : 1 ≤ L * T) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-L * T) := by
  have he : 2 ≤ Real.exp (L * T) := by
    linarith only [Real.add_one_le_exp (L * T), hLT]
  have hp : Real.exp (L * T) * Real.exp (-L * T) = 1 := by
    rw [← Real.exp_add]
    rw [show L * T + -L * T = 0 by ring, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-L * T))
  nlinarith only [hp, hm]

theorem denominator_pos {T L : ℝ} (hLT : 1 ≤ L * T) :
    0 < 1 - Real.exp (-L * T) := lt_of_lt_of_le (by norm_num) (denominator_lower hLT)

@[simp] theorem ramp_initial (T L : ℝ) : ramp T L 0 = 0 := by
  simp [ramp, mul_neg]

theorem ramp_terminal {T L : ℝ} (hLT : 1 ≤ L * T) : ramp T L T = 1 := by
  simp only [ramp, sub_self, mul_zero, Real.exp_zero]
  exact div_self (denominator_pos hLT).ne'

theorem ramp_hasDerivAt (T L t : ℝ) : HasDerivAt (ramp T L) (rampDerivative T L t) t := by
  change HasDerivAt
    (fun s => (Real.exp (L * (s - T)) - Real.exp (-L * T)) / (1 - Real.exp (-L * T)))
    (L * Real.exp (L * (t - T)) / (1 - Real.exp (-L * T))) t
  simpa only [id_eq, mul_one, mul_comm] using
    (((((hasDerivAt_id t).sub_const T).const_mul L).exp).sub_const
      (Real.exp (-L * T))).div_const (1 - Real.exp (-L * T))

theorem ramp_continuous (T L : ℝ) : Continuous (ramp T L) :=
  continuous_iff_continuousAt.2 fun t => (ramp_hasDerivAt T L t).continuousAt

theorem rampDerivative_continuous (T L : ℝ) : Continuous (rampDerivative T L) := by
  unfold rampDerivative
  fun_prop

theorem ramp_nonneg {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T)
    (ht : 0 ≤ t) : 0 ≤ ramp T L t := by
  apply div_nonneg _ (denominator_pos hLT).le
  apply sub_nonneg.mpr (Real.exp_le_exp.mpr _)
  nlinarith only [mul_nonneg hL ht]

theorem ramp_le_exp {T L t : ℝ} (hLT : 1 ≤ L * T) :
    ramp T L t ≤ 2 * Real.exp (L * (t - T)) := by
  apply (div_le_iff₀ (denominator_pos hLT)).2
  have hm := mul_le_mul_of_nonneg_right (denominator_lower hLT)
    (Real.exp_nonneg (L * (t - T)))
  nlinarith only [hm, Real.exp_nonneg (-L * T)]

theorem rampDerivative_nonneg {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    0 ≤ rampDerivative T L t :=
  div_nonneg (mul_nonneg hL (Real.exp_nonneg _)) (denominator_pos hLT).le

theorem rampDerivative_le_exp {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    rampDerivative T L t ≤ 2 * L * Real.exp (L * (t - T)) := by
  apply (div_le_iff₀ (denominator_pos hLT)).2
  have hm := mul_le_mul_of_nonneg_right (denominator_lower hLT)
    (mul_nonneg hL (Real.exp_nonneg (L * (t - T))))
  nlinarith only [hm]

theorem ramp_sq_le {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) (ht : 0 ≤ t) :
    ramp T L t ^ 2 ≤ 4 * Real.exp (2 * L * (t - T)) := by
  have hp := pow_le_pow_left₀ (ramp_nonneg hL hLT ht) (ramp_le_exp (t := t) hLT) 2
  have he : Real.exp (L * (t - T)) ^ 2 = Real.exp (2 * L * (t - T)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp

theorem rampDerivative_sq_le {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    rampDerivative T L t ^ 2 ≤ (4 * L ^ 2) * Real.exp (2 * L * (t - T)) := by
  have hp := pow_le_pow_left₀ (rampDerivative_nonneg (t := t) hL hLT)
    (rampDerivative_le_exp (t := t) hL hLT) 2
  have he : Real.exp (L * (t - T)) ^ 2 = Real.exp (2 * L * (t - T)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp

theorem exp_kernel_integral_le {T L : ℝ} (hL : 0 < L) :
    (∫ t in 0..T, Real.exp (2 * L * (t - T))) ≤ 1 / (2 * L) := by
  have hd (t : ℝ) : HasDerivAt
      (fun s => Real.exp (2 * L * (s - T)) / (2 * L))
      (Real.exp (2 * L * (t - T))) t := by
    simpa only [id_eq, mul_one,
      mul_div_cancel_right₀ _ (show 2 * L ≠ 0 by positivity)] using
      (((((hasDerivAt_id t).sub_const T).const_mul (2 * L)).exp).div_const (2 * L))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub
      continuous_const))).intervalIntegrable 0 T)
  calc
    (∫ t in 0..T, Real.exp (2 * L * (t - T))) =
        (1 - Real.exp (2 * L * (0 - T))) / (2 * L) := by
      rw [hi, sub_self, mul_zero, Real.exp_zero, sub_div]
    _ ≤ 1 / (2 * L) := div_le_div_of_nonneg_right
      (sub_le_self _ (Real.exp_nonneg _)) (by positivity)

theorem ramp_energy {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hLT : 1 ≤ L * T) :
    (∫ t in 0..T, ramp T L t ^ 2) ≤ 2 / L := by
  have hc : Continuous (fun t : ℝ => Real.exp (2 * L * (t - T))) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((ramp_continuous T L).pow 2).intervalIntegrable 0 T)
    ((continuous_const.mul hc).intervalIntegrable (a := 0) (b := T))
    (fun t ht => ramp_sq_le hL.le hLT ht.1)
  change (∫ t in 0..T, ramp T L t ^ 2) ≤
    ∫ t in 0..T, 4 * Real.exp (2 * L * (t - T)) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ t in 0..T, ramp T L t ^ 2) ≤ 4 * (∫ t in 0..T, Real.exp (2 * L * (t - T))) := hi
    _ ≤ 4 * (1 / (2 * L)) := mul_le_mul_of_nonneg_left (exp_kernel_integral_le hL) (by norm_num)
    _ = 2 / L := by ring

theorem rampDerivative_energy {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hLT : 1 ≤ L * T) :
    (∫ t in 0..T, rampDerivative T L t ^ 2) ≤ 2 * L := by
  have hc : Continuous (fun t : ℝ => Real.exp (2 * L * (t - T))) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((rampDerivative_continuous T L).pow 2).intervalIntegrable 0 T)
    ((continuous_const.mul hc).intervalIntegrable (a := 0) (b := T))
    (fun t _ => rampDerivative_sq_le (t := t) hL.le hLT)
  change (∫ t in 0..T, rampDerivative T L t ^ 2) ≤
    ∫ t in 0..T, (4 * L ^ 2) * Real.exp (2 * L * (t - T)) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ t in 0..T, rampDerivative T L t ^ 2) ≤
        (4 * L ^ 2) * (∫ t in 0..T, Real.exp (2 * L * (t - T))) := hi
    _ ≤ (4 * L ^ 2) * (1 / (2 * L)) :=
      mul_le_mul_of_nonneg_left (exp_kernel_integral_le hL) (by positivity)
    _ = 2 * L := by field_simp; ring

end EulerTerminalLayerRamp
