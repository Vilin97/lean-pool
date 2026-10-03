/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude

/-! Corrected scalar closure of l.V, retaining the corrected C/C0 remainder.
These are scalar induction helpers; the actual PDE recurrence is a separate
required input and is not claimed to have been derived in this module. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- All printed amplitude coefficients are positive for positive eta. -/
theorem iterateAmplitude_pos {η : ℝ} (hη : 0 < η) (i : ℕ) :
    0 < iterateAmplitude η i := by
  unfold iterateAmplitude
  split_ifs <;> positivity

/-- The squared previous-amplitude estimate also gives the linear ratio
needed for the half-geometric term, including the first increment. -/
theorem iterateAmplitude_scaled_previous_ratio {C₀ q : ℝ}
    (hC : 0 < C₀) (hq : 0 < q) (hsmall : C₀ * q ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) :
    q * iterateAmplitude (C₀ * q) (i - 1) / iterateAmplitude (C₀ * q) i ≤ C₀⁻¹ := by
  have hη := mul_pos hC hq
  have hprev := iterateAmplitude_pos hη (i - 1)
  have hcur := iterateAmplitude_pos hη i
  have hs := iterateAmplitudeSq_squared_previous hη.le hsmall hi
  rw [← iterateAmplitude_square hη.le (i - 1), ← iterateAmplitude_square hη.le i] at hs
  have hmul : C₀ * (q * iterateAmplitude (C₀ * q) (i - 1)) ≤
      iterateAmplitude (C₀ * q) i := by
    apply (sq_le_sq₀ (by positivity) hcur.le).mp
    calc
      _ = (C₀ * q) ^ 2 * iterateAmplitude (C₀ * q) (i - 1) ^ 2 := by ring
      _ ≤ _ := hs
  apply (div_le_iff₀ hcur).mpr
  have h := (le_div_iff₀ hC).mpr (by simpa only [mul_comm C₀] using hmul)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The three retained material remainders at i >= 2 have the corrected
C/C0 + 2C/C0^2 budget. In particular, the C/C0 term is not discarded. -/
theorem iterate_corrected_material_remainder_bound {C C₀ q : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 < C₀) (hq : 0 < q) (hsmall : C₀ * q ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    C * (q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 1) /
      iterateAmplitudeSq (C₀ * q) i) +
    C * (q * iterateAmplitudeSq (C₀ * q) (i - 1) /
      iterateAmplitudeSq (C₀ * q) i) +
    C * (q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 2) /
      iterateAmplitudeSq (C₀ * q) i) ≤ C / C₀ + 2 * C / C₀ ^ 2 := by
  have h₁ := mul_le_mul_of_nonneg_left
    (iterateAmplitudeSq_scaled_squared_previous_ratio (i := i) hC₀ hq hsmall (by omega)) hC
  have h₂ := mul_le_mul_of_nonneg_left
    (iterateAmplitudeSq_scaled_previous_ratio hC₀ hq hsmall hi) hC
  have h₃ := mul_le_mul_of_nonneg_left
    (iterateAmplitudeSq_scaled_two_previous_ratio hC₀ hq hsmall hi) hC
  calc
    _ ≤ C * (C₀ ^ 2)⁻¹ + C * C₀⁻¹ + C * (C₀ ^ 2)⁻¹ :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- The actual source amplitude ratio controls the linear convolution
coefficient by C0^-3, since F >= C0. -/
theorem iterate_source_linear_ratio_le {C₀ ρ F : ℝ}
    (hC₀ : 0 < C₀) (hρ : 0 < ρ) (hF : C₀ ≤ F)
    (hsmall : C₀ * (ρ * F ^ 2) ≤ 1) {i : ℕ} (hi : 1 ≤ i) :
    ρ * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) /
      iterateAmplitude (C₀ * (ρ * F ^ 2)) i ≤ 1 / C₀ ^ 3 := by
  have hFp : 0 < F := hC₀.trans_le hF
  have hq : 0 < ρ * F ^ 2 := mul_pos hρ (sq_pos_of_pos hFp)
  have hp := iterateAmplitude_scaled_previous_ratio hC₀ hq hsmall hi
  have hAi := iterateAmplitude_pos (mul_pos hC₀ hq) i
  calc
    _ = ((ρ * F ^ 2) * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) /
        iterateAmplitude (C₀ * (ρ * F ^ 2)) i) / F ^ 2 := by field_simp
    _ ≤ C₀⁻¹ / F ^ 2 := div_le_div_of_nonneg_right hp (sq_nonneg F)
    _ ≤ C₀⁻¹ / C₀ ^ 2 := div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos hC₀) ((sq_le_sq₀ hC₀.le hFp.le).mpr hF)
    _ = 1 / C₀ ^ 3 := by field_simp

end AVenhance.Infra.Section4
