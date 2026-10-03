/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Circle integrals of `log ‖· - a‖`

Consequences of Mathlib's circle-average identities, in the normalisation used here
(integrals over `θ ∈ [0, 2π]` without the factor `(2π)⁻¹`), and countability of point
preimages under `circleMap` and `cos`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

lemma circle_log_integrable (c a : ℂ) (R : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - a‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const R

/-- `∫₀^{2π} log ‖circleMap c R θ - a‖ = 2π (log R + log⁺ (R⁻¹ ‖c - a‖))`. -/
lemma circle_log_integral (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap c R θ - a‖ =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hR
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

lemma circle_log_integral_zero_one (a : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - a‖ = 2 * π * log⁺ ‖a‖ := by
  rw [circle_log_integral 0 a one_ne_zero]
  simp

lemma abs_log_eq (x : ℝ) : |Real.log x| = 2 * log⁺ x - Real.log x := by
  rw [posLog_apply]
  rcases le_total 0 (Real.log x) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma posLog_norm_sub_le (w q : ℂ) (hw : ‖w‖ ≤ 1) : log⁺ ‖w - q‖ ≤ Real.log (1 + ‖q‖) := by
  calc
    log⁺ ‖w - q‖ ≤ log⁺ (1 + ‖q‖) := by
      apply posLog_le_posLog (by linarith [norm_nonneg (w - q)])
      calc
        ‖w - q‖ ≤ ‖w‖ + ‖q‖ := norm_sub_le _ _
        _ ≤ 1 + ‖q‖ := by linarith
    _ = Real.log (1 + ‖q‖) :=
      posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith [norm_nonneg q])

/-- Uniform bound `∫₀^{2π} |log ‖e^{iθ} - q‖| ≤ 4π log (1 + ‖q‖)`. -/
lemma abs_log_circle_integral_le (q : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, |Real.log ‖circleMap 0 1 θ - q‖| ≤ 4 * π * Real.log (1 + ‖q‖) := by
  simp_rw [abs_log_eq]
  have hc : Continuous fun θ => log⁺ ‖circleMap 0 1 θ - q‖ := by
    have := continuous_circleMap 0 1
    fun_prop
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _ |>.const_mul 2)
      (circle_log_integrable 0 q 1),
    intervalIntegral.integral_const_mul, circle_log_integral_zero_one]
  have h1 :
    (∫ θ in (0 : ℝ)..2 * π, log⁺ ‖circleMap 0 1 θ - q‖) ≤
      ∫ θ in (0 : ℝ)..2 * π, Real.log (1 + ‖q‖) := by
    apply integral_mono_on (by positivity) (hc.intervalIntegrable _ _) intervalIntegrable_const
    intro θ _
    apply posLog_norm_sub_le
    simp [circleMap]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  have h2 := posLog_nonneg (x := ‖q‖)
  nlinarith [Real.pi_pos]

/-- Point preimages under `circleMap` are countable. -/
lemma circleMap_preimage_countable (c : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    (circleMap c R ⁻¹' { z }).Countable := by
  rcases (circleMap c R ⁻¹' { z }).eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * π)).mono ?_
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, circleMap] at hθ hθ₀
  have he : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    have := hθ.trans hθ₀.symm
    have h2 : (R : ℂ) * Complex.exp (θ * Complex.I) = R * Complex.exp (θ₀ * Complex.I) := by
      linear_combination this
    exact mul_left_cancel₀ hR' h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨n, ?_⟩
  have : (θ : ℂ) = θ₀ + n * (2 * π) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h3 : (θ : ℂ) * Complex.I = (θ₀ + n * (2 * π)) * Complex.I := by rw [hn]; ring
    exact mul_right_cancel₀ hI h3
  exact_mod_cast this.symm

/-- Point preimages under `cos` are countable. -/
lemma cos_preimage_countable (c : ℝ) : (Real.cos ⁻¹' { c }).Countable := by
  rcases (Real.cos ⁻¹' { c }).eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  refine
    ((Set.countable_range fun k : ℤ => 2 * k * π + θ₀).union
          (Set.countable_range fun k : ℤ => 2 * k * π - θ₀)).mono
      ?_
  intro θ hθ
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hθ hθ₀
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (hθ₀.trans hθ.symm)
  · exact Or.inl ⟨k, hk.symm⟩
  · exact Or.inr ⟨k, hk.symm⟩

lemma circleMap_zero_one_re (θ : ℝ) : (circleMap 0 1 θ).re = Real.cos θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_re]

/-- `cos θ = (w + w⁻¹)/2` for `w = e^{iθ}`. -/
lemma cos_eq_half_add_inv (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) = (circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  rw [← Complex.exp_neg]
  ring_nf

lemma norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by simp [circleMap]

end Zeta5Irrational
