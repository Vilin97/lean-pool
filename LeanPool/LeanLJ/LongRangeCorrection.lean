/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LeanPool.LeanLJ.Instance
import LeanPool.LeanLJ.Function

/-!
# The Lennard-Jones long-range correction integral

This file evaluates the Lennard-Jones long-range correction integral over `(rc, ∞)` in
closed form, matching the standard analytic tail expression `uLRCReal`.
-/

open LeanLJ

open Real MeasureTheory
namespace LeanLJ


theorem long_range_correction_equality (rc ρ ε σ : ℝ) (hr : 0 < rc) :
    (2 * π * ρ) * ∫ (r : ℝ) in Set.Ioi rc, 4 * ε * (r ^ 2 * (((σ / r) ^ 12) -
    ((σ / r) ^ 6))) = (8 * π * ρ * ε) * ((1/9) * (σ ^ 12 / rc ^ 9) -
    (1/3) * (σ ^ 6 / rc ^ 3)) := by
  by_cases hρ : ρ = 0
  · simp only [hρ, mul_zero, zero_mul]
  · by_cases hε : ε = 0
    · simp only [hε, mul_zero, zero_mul, integral_zero, mul_zero]
    · calc
        2 * π * ρ * ∫ (r : ℝ) in Set.Ioi rc, 4 * ε * (r ^ 2 * ((σ / r) ^ 12 -
          (σ / r) ^ 6)) =
        (2 * π * ρ) * (∫ (r : ℝ) in Set.Ioi rc, ((r ^ 2 *
          ((σ / r) ^ 12 - (σ / r) ^ 6)) • (4 * ε))) := by
            field_simp
            congr with x
            ring
        _ = (8 * π * ρ * ε)  * ∫ (r : ℝ) in Set.Ioi rc, (r ^ 2 *
          ((σ / r) ^ 12 - (σ / r) ^ 6)) := by
            rw [integral_smul_const, smul_eq_mul]
            ring
      rw [mul_eq_mul_left_iff]
      left
      calc
        ∫ (r : ℝ) in Set.Ioi rc, r ^ 2 * ((σ / r) ^ 12 - (σ / r) ^ 6) =
          ∫ (r : ℝ) in Set.Ioi rc, (σ ^ 12 / r ^ 10 + - σ ^ 6 / r ^ 4) := by
            congr with r
            by_cases hr : r = 0
            · rw [hr]
              simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
                div_zero, sub_self, add_zero]
            · field_simp
              ring
        _ = (∫ (a : ℝ) in Set.Ioi rc, (σ ^ 12 / a ^ 10)) + ∫ (a : ℝ) in Set.Ioi rc,
          (- σ ^ 6 / a ^ 4) := by
            rw [← integral_add]
            · apply Integrable.const_mul
              rw [← IntegrableOn]
              have heq : Set.EqOn (fun x ↦ x ^ (-10 : ℝ)) (fun x ↦ (x ^ 10)⁻¹) (Set.Ioi rc) := by
                intro x hx
                simp_rw [Real.rpow_neg (hr.trans hx).le, ← Real.rpow_natCast, Nat.cast_ofNat]
              refine IntegrableOn.congr_fun ?_ heq (by measurability)
              exact integrableOn_Ioi_rpow_of_lt (by norm_num) hr
            · apply Integrable.const_mul
              rw [← IntegrableOn]
              have heq : Set.EqOn (fun x ↦ x ^ (-4 : ℝ)) (fun x ↦ (x ^ 4)⁻¹) (Set.Ioi rc) := by
                intro x hx
                simp_rw [Real.rpow_neg (hr.trans hx).le, ← Real.rpow_natCast, Nat.cast_ofNat]
              refine IntegrableOn.congr_fun ?_ heq (by measurability)
              exact integrableOn_Ioi_rpow_of_lt (by norm_num) hr
        _ = σ ^ 12 * (∫ (a : ℝ) in Set.Ioi rc, (1 / a ^ 10)) + (- σ ^ 6) * ∫ (a : ℝ) in Set.Ioi rc,
          (1 / a ^ 4) := by
              rw [mul_comm, ← smul_eq_mul, ← integral_smul_const, eq_comm, add_comm, eq_comm,
                mul_comm, ← smul_eq_mul, ← integral_smul_const, show σ ^ 12 = σ ^ 12 * 1 by
                rw [mul_one], show σ ^ 6 = σ ^ 6 * 1 by rw [mul_one], add_comm]
              simp_rw [smul_eq_mul]
              congr with x <;> ring
        _ = σ ^ 12 * (∫ (a : ℝ) in Set.Ioi rc, (a ^ (-10:ℝ))) + (- σ ^ 6) * ∫ (a : ℝ) in Set.Ioi rc,
          (a ^ (-4:ℝ)) := by
              congr with x <;> norm_cast <;> simp only [one_div, Int.reduceNegSucc, zpow_neg,
                inv_inj] <;> norm_cast
        _ = 1 / 9 * (σ ^ 12 * rc ^ (-9:ℝ)) - 1 / 3 * (σ ^ 6 * rc ^ (-3:ℝ)):= by
              repeat rw [integral_Ioi_rpow_of_lt (by nlinarith) hr]
              norm_num
              ring_nf
        _ = ((1/9) * (σ ^ 12 / rc ^ 9) - (1/3) * (σ ^ 6 / rc ^ 3)) := by
              congr <;> norm_cast

theorem long_range_correction_equality' (rc ρ ε σ : ℝ) (hr : 0 < rc) :
    (2 * π * ρ) * ∫ (r : ℝ) in Set.Ioi rc, 4 * ε * (r ^ 2 * (((σ / r) ^ 12) -
    ((σ / r) ^ 6))) = uLRCReal ρ ε σ rc := by
  rw [uLRCReal]
  exact long_range_correction_equality rc ρ ε σ hr

end LeanLJ
