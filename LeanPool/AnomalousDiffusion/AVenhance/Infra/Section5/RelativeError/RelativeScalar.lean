/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Pure real arithmetic for the relative dissipation step. All transcendental
quantities are supplied as abstract scalars to the polynomial arguments. -/

@[expose] public section

namespace AVenhance.Infra.Section5.RelativeError

theorem relative_sqrt_square_gap {u v B : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hB : 0 ≤ B) (h : |u ^ 2 - v ^ 2| ≤ B ^ 2) : |u - v| ≤ B := by
  have hsum : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have hfac : |u ^ 2 - v ^ 2| = |u - v| * (u + v) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hu hv), mul_comm]
  have hs : |u - v| ^ 2 ≤ B ^ 2 := by
    calc |u - v| ^ 2 = |u - v| * |u - v| := by ring
      _ ≤ |u - v| * (u + v) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ ≤ B ^ 2 := hfac ▸ h
  exact (sq_le_sq₀ (abs_nonneg _) hB).mp hs

theorem relative_energy_gap_of_norm_gap {u S K e : ℝ}
    (hu : 0 ≤ u) (hS : 0 ≤ S) (hK : 0 ≤ K) (he : 0 ≤ e) (he1 : e ≤ 1)
    (h : |u - S| ≤ K * e * S) :
    |u ^ 2 - S ^ 2| ≤ (K * (2 + K)) * e * S ^ 2 := by
  have huupper : u ≤ (1 + K) * S := by
    have h1 := (abs_le.mp h).2
    have h2 : K * e * S ≤ K * S := by
      calc K * e * S ≤ K * 1 * S := by gcongr
        _ = K * S := by ring
    linarith only [h1, h2]
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hu hS), mul_comm]
  calc |u - S| * (u + S) ≤ (K * e * S) * ((2 + K) * S) :=
        mul_le_mul h (by linarith only [huupper]) (add_nonneg hu hS) (by positivity)
    _ = _ := by ring

end AVenhance.Infra.Section5.RelativeError
