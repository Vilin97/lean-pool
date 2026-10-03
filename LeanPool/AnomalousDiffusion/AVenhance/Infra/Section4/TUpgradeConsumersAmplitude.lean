/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTThetaUpgrade

/-! # TUpgrade Consumers Amplitude

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Enlarging a nonnegative amplitude preserves every coordinate energy. -/
theorem iterate_coordinate_profile_amplitude_mono
    {u : ℝ → Vec 2 → ℝ} {κ N B L : ℝ} {i : ℕ}
    (hN : 0 ≤ N) (hNB : N ≤ B)
    (h : iterateCoordinateEnergyProfile u κ N L i) :
    iterateCoordinateEnergyProfile u κ B L i := by
  have hs : N ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hN (hN.trans hNB)).mpr hNB
  constructor
  · intro w hw s ht ht1
    exact (h.1 w hw s ht ht1).trans
      (mul_le_mul_of_nonneg_right hs (sq_nonneg _))
  · intro w
    have hd : N / Real.sqrt κ ≤ B / Real.sqrt κ :=
      div_le_div_of_nonneg_right hNB (Real.sqrt_nonneg _)
    have hd0 : 0 ≤ N / Real.sqrt κ := div_nonneg hN (Real.sqrt_nonneg _)
    exact (h.2 w).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hd0 (hd0.trans hd)).mpr hd) (sq_nonneg _))

/-- Remove an artificial strict-positivity premise without dividing by the amplitude. -/
theorem iterate_amplitude_bound_of_strict_enlargements {a N K : ℝ}
    (hK : 0 ≤ K) (h : ∀ B, N < B → a ≤ B * K) : a ≤ N * K := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < K + 1 := by linarith only [hK]
  have hb := h (N + ε / (K + 1)) (by
    have := div_pos hε hden
    linarith only [this])
  have hfrac : ε / (K + 1) * K ≤ ε := by
    have heq : ε / (K + 1) * (K + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
    have hpos := (div_pos hε hden).le
    nlinarith only [heq, hpos]
  nlinarith only [hb, hfrac]

end AVenhance.Infra.Section4
