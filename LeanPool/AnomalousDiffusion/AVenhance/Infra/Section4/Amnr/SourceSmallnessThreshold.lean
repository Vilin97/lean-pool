/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds

/-! One literal source smallness threshold pays for the terminal coefficient bounds. -/

@[expose] public section

namespace AVenhance.Infra.Section4

theorem amnr_source_smallness_threshold {L P e : ℝ}
    (hL : 0 ≤ L) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hsmall : e ^ 2 ≤ ((2 + 320 * (L + 1) * (P + 1)) ^ 2)⁻¹) :
    P * e ^ 2 ≤ 1 / 2 ∧ L * (P * e ^ 2 + e) ≤ 9 / 160 := by
  let R := 2 + 320 * (L + 1) * (P + 1)
  have hR2 : 2 ≤ R := by
    have hh : 0 ≤ 320 * (L + 1) * (P + 1) := by positivity
    dsimp [R]
    linarith only [hh]
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) hR2
  have heInv : e ≤ R⁻¹ := by
    rw [← inv_pow] at hsmall
    exact (sq_le_sq₀ he (inv_nonneg.mpr hR.le)).mp hsmall
  have hRe : R * e ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left heInv hR.le
    simpa only [mul_inv_cancel₀ hR.ne'] using hh
  have he1 : e ≤ 1 := heInv.trans ((inv_le_one₀ hR).mpr (by linarith only [hR2]))
  have heSq : e ^ 2 ≤ e := by
    have hh := mul_nonneg he (sub_nonneg.mpr he1)
    nlinarith only [hh]
  have hRP : 2 * P ≤ R := by
    have hh := mul_nonneg hL (add_nonneg hP zero_le_one)
    dsimp [R]
    nlinarith only [hh, hP]
  have hRL : (160 / 9) * L * (P + 1) ≤ R := by
    have hh := mul_nonneg hL (add_nonneg hP zero_le_one)
    dsimp [R]
    nlinarith only [hh, hP]
  have hPe := mul_le_mul_of_nonneg_right hRP he
  have hLe := mul_le_mul_of_nonneg_right hRL he
  have hPSq := mul_le_mul_of_nonneg_left heSq hP
  have hLSq := mul_le_mul_of_nonneg_left (add_le_add_right hPSq e) hL
  constructor <;> nlinarith only [hPe, hLe, hRe, hPSq, hLSq]

end AVenhance.Infra.Section4
