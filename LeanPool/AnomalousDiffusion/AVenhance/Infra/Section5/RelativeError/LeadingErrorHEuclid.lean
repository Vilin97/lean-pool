/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Euclidean bridge for the `HTilde_m` gradient

The `Hmr` gradient estimates are `eLpNorm`s of `Vec 2`-valued maps, measured with the
ambient Pi sup norm.  The `spaceTimeGradNormSq` integrates `vecNormSq` (the Euclidean
norm squared).  In dimension two, `vecNormSq v ≤ 2 ‖v‖²`, which costs the factor `√2`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

/-- In dimension two the Euclidean norm squared is at most twice the sup norm squared. -/
theorem vecNormSq_two_le (v : Vec 2) : vecNormSq v ≤ 2 * ‖v‖ ^ 2 := by
  have h0 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by
    have := norm_le_pi_norm v 0
    rw [Real.norm_eq_abs] at this
    exact (sq_le_sq' (by linarith [abs_nonneg (v 0), neg_abs_le (v 0)]) (le_trans (le_abs_self _)
        this))
  have h1 : v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
    have := norm_le_pi_norm v 1
    rw [Real.norm_eq_abs] at this
    exact (sq_le_sq' (by linarith [abs_nonneg (v 1), neg_abs_le (v 1)]) (le_trans (le_abs_self _)
        this))
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith only [h0, h1]

/-- Pointwise `ENNReal` form of `vecNormSq_two_le`. -/
theorem ofReal_vecNormSq_le (v : Vec 2) :
    ENNReal.ofReal (vecNormSq v) ≤ 2 * ‖v‖ₑ ^ (2 : ℕ) := by
  calc
    ENNReal.ofReal (vecNormSq v) ≤ ENNReal.ofReal (2 * ‖v‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (vecNormSq_two_le v)
    _ = 2 * ‖v‖ₑ ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg v),
        ofReal_norm]
      simp

/-- The Euclidean integral of a vector field with sup-norm `L²` bound `B` is at most `2 B²`. -/
theorem integral_vecNormSq_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (g : α → Vec 2) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm g 2 μ ≤ ENNReal.ofReal B) :
    ∫ z, vecNormSq (g z) ∂μ ≤ 2 * B ^ 2 := by
  by_cases hint : Integrable (fun z => vecNormSq (g z)) μ
  · have hnn : 0 ≤ᵐ[μ] fun z => vecNormSq (g z) :=
      Filter.Eventually.of_forall fun z => by
        simp only [Pi.zero_apply]
        exact vecNormSq_nonneg _
    have hmeas : AEStronglyMeasurable g μ :=
      aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
    have hsq : eLpNorm g 2 μ ^ 2 = ∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hl : ENNReal.ofReal (∫ z, vecNormSq (g z) ∂μ) ≤ ENNReal.ofReal (2 * B ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
      calc
        ∫⁻ z, ENNReal.ofReal (vecNormSq (g z)) ∂μ ≤ ∫⁻ z, 2 * ‖g z‖ₑ ^ (2 : ℕ) ∂μ :=
          lintegral_mono fun z => ofReal_vecNormSq_le (g z)
        _ = 2 * eLpNorm g 2 μ ^ 2 := by
          rw [lintegral_const_mul' _ _ (by norm_num), hsq]
        _ ≤ 2 * ENNReal.ofReal B ^ 2 := by gcongr
        _ = ENNReal.ofReal (2 * B ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hB]
          simp
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hl
  · rw [integral_undef hint]
    positivity

/-- Euclidean `√∫|g|²` is at most `√2` times the sup-norm `L²` bound. -/
theorem sqrt_integral_vecNormSq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (g : α → Vec 2) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm g 2 μ ≤ ENNReal.ofReal B) :
    Real.sqrt (∫ z, vecNormSq (g z) ∂μ) ≤ Real.sqrt 2 * B := by
  calc
    Real.sqrt (∫ z, vecNormSq (g z) ∂μ) ≤ Real.sqrt (2 * B ^ 2) :=
      Real.sqrt_le_sqrt (integral_vecNormSq_le_of_eLpNorm_le g hB h)
    _ = Real.sqrt 2 * B := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hB]

/-- The `spaceTimeGradNormSq` version over the open time cell. -/
theorem sqrt_spaceTimeGradNormSq_le_of_eLpNorm_le (Dθ : ℝ → Vec 2 → Vec 2) {B : ℝ}
    (hB : 0 ≤ B)
    (h : eLpNorm (fun z : ℝ × Vec 2 => Dθ z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal B) :
    Real.sqrt (AVenhance.spaceTimeGradNormSq Dθ) ≤ Real.sqrt 2 * B :=
  sqrt_integral_vecNormSq_le (fun z : ℝ × Vec 2 => Dθ z.1 z.2) hB h

end AVenhance.Infra.Section5.RelativeError
