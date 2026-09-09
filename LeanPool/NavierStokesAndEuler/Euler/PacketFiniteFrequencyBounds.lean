/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail

@[expose] public section

/-! Frequency guards turn the finite geometric remainder into fixed polynomial bounds. -/

namespace EulerPacketFiniteFrequency


theorem fourth_power_le_frequency (k B : ℝ) (hk : 1 ≤ k) (hB0 : 0 ≤ B)
    (hB : B ≤ k^(1/100 : ℝ)) : B^4 ≤ k := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  calc
    _ ≤ (k^(1/100 : ℝ))^4 := pow_le_pow_left₀ hB0 hB 4
    _ = k^((1/100 : ℝ)*4) := (Real.rpow_mul_natCast hk0 _ _).symm
    _ ≤ k^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk (by norm_num)
    _ = k := Real.rpow_one k

theorem normalized_low_high_le (k B C₁ C₂ : ℝ) (hk : 2 ≤ k) (hC₂ : 0 ≤ C₂)
    (hB4 : B^4 ≤ k) :
    k*(k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3) ≤ C₁+C₂+1 := by
  have hk0 : 0 < k := by linarith
  have he : k*(k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3) = C₁+C₂/k+2*B^4/k^2 := by
    field_simp
  have hc : C₂/k ≤ C₂ := (div_le_iff₀ hk0).mpr (by nlinarith)
  have ht : 2*B^4/k^2 ≤ 1 := (div_le_one (sq_pos_of_pos hk0)).mpr (by nlinarith)
  rw [he]
  linarith

theorem remainder_low_high_le (k B C₂ : ℝ) (hk : 0 < k) (hB4 : B^4 ≤ k) :
    (k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3 ≤ (C₂+2)/k^2 := by
  have he : (k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3 = (C₂+2*B^4/k)/k^2 := by
    field_simp
  have ht : 2*B^4/k ≤ 2 := (div_le_iff₀ hk).mpr (by nlinarith)
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg k)

end EulerPacketFiniteFrequency
