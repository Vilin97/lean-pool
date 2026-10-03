/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The actual piecewise amplitude weights in l.V and their squared ratios.
The theta base prefactor is handled by a common prefactor outside
these weights; the weights themselves are the printed A_i. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The source amplitude, with eta its smallness parameter. -/
def iterateAmplitude (η : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i ≤ 2 then η else η ^ ((i : ℝ) / 2)

/-- Squaring removes fractional powers from the induction bookkeeping. -/
def iterateAmplitudeSq (η : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i ≤ 2 then η ^ 2 else η ^ i

theorem iterateAmplitude_square {η : ℝ} (hη : 0 ≤ η) (i : ℕ) :
    iterateAmplitude η i ^ 2 = iterateAmplitudeSq η i := by
  unfold iterateAmplitude iterateAmplitudeSq
  split_ifs
  · norm_num
  · rfl
  · rw [← Real.rpow_mul_natCast hη]
    have he : (i : ℝ) / 2 * (2 : ℕ) = (i : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]

theorem iterateAmplitudeSq_pos {η : ℝ} (hη : 0 < η) (i : ℕ) :
    0 < iterateAmplitudeSq η i := by
  unfold iterateAmplitudeSq
  split_ifs <;> positivity

/-- The preceding-increment material term costs one power of eta for i≥2. -/
theorem iterateAmplitudeSq_previous {η : ℝ} (hη1 : η ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    η * iterateAmplitudeSq η (i - 1) ≤ iterateAmplitudeSq η i := by
  by_cases hi2 : i = 2
  · subst i
    norm_num [iterateAmplitudeSq]
    exact mul_le_of_le_one_left (sq_nonneg η) hη1
  · by_cases hi3 : i = 3
    · subst i
      norm_num [iterateAmplitudeSq, pow_succ]
      ring_nf
      exact le_rfl
    · have hi4 : 4 ≤ i := by omega
      have he : i = (i - 1) + 1 := by omega
      simp only [iterateAmplitudeSq, ite_eq_right (by omega : i - 1 ≠ 0),
        ite_eq_right (by omega : ¬i - 1 ≤ 2), ite_eq_right (by omega : i ≠ 0),
        ite_eq_right (by omega : ¬i ≤ 2)]
      rw [he, pow_succ]
      exact le_of_eq (mul_comm _ _)

/-- Two-increment terms cost two powers of eta; the exceptional early
amplitudes are handled explicitly rather than replaced by a uniform power. -/
theorem iterateAmplitudeSq_two_previous {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    η ^ 2 * iterateAmplitudeSq η (i - 2) ≤ iterateAmplitudeSq η i := by
  by_cases hi2 : i = 2
  · subst i
    norm_num [iterateAmplitudeSq]
  · by_cases hi3 : i = 3
    · subst i
      have hp : η ^ 4 ≤ η ^ 3 := pow_le_pow_of_le_one hη hη1 (by omega)
      simpa [iterateAmplitudeSq, ← pow_add] using hp
    · by_cases hi4 : i = 4
      · subst i
        norm_num [iterateAmplitudeSq]
        exact le_of_eq (by ring)
      · have he : i = (i - 2) + 2 := by omega
        simp only [iterateAmplitudeSq, ite_eq_right (by omega : i - 2 ≠ 0),
          ite_eq_right (by omega : ¬i - 2 ≤ 2), ite_eq_right (by omega : i ≠ 0),
          ite_eq_right (by omega : ¬i ≤ 2)]
        rw [he, pow_add]
        exact le_of_eq (mul_comm _ _)

/-- Normalization of the one-increment material remainder for eta=C0*rho. -/
theorem iterateAmplitudeSq_scaled_previous_ratio
    {C₀ ρ : ℝ} (hC : 0 < C₀) (hρ : 0 < ρ) (hsmall : C₀ * ρ ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    ρ * iterateAmplitudeSq (C₀ * ρ) (i - 1) / iterateAmplitudeSq (C₀ * ρ) i ≤ C₀⁻¹ := by
  have hw := iterateAmplitudeSq_pos (mul_pos hC hρ) i
  have hp := iterateAmplitudeSq_previous hsmall hi
  have ht : C₀ * (ρ * iterateAmplitudeSq (C₀ * ρ) (i - 1)) ≤
      iterateAmplitudeSq (C₀ * ρ) i := by simpa only [mul_assoc] using hp
  apply (div_le_iff₀ hw).2
  rw [mul_comm C₀] at ht
  have h := (le_div_iff₀ hC).2 ht
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Normalization of the two-increment material remainder, including i=2. -/
theorem iterateAmplitudeSq_scaled_two_previous_ratio
    {C₀ ρ : ℝ} (hC : 0 < C₀) (hρ : 0 < ρ) (hsmall : C₀ * ρ ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    ρ ^ 2 * iterateAmplitudeSq (C₀ * ρ) (i - 2) / iterateAmplitudeSq (C₀ * ρ) i ≤ (C₀ ^ 2)⁻¹ := by
  have hw := iterateAmplitudeSq_pos (mul_pos hC hρ) i
  have hp := iterateAmplitudeSq_two_previous (mul_pos hC hρ).le hsmall hi
  have ht : C₀ ^ 2 * (ρ ^ 2 * iterateAmplitudeSq (C₀ * ρ) (i - 2)) ≤
      iterateAmplitudeSq (C₀ * ρ) i := by simpa only [mul_pow, mul_assoc] using hp
  apply (div_le_iff₀ hw).2
  rw [mul_comm (C₀ ^ 2)] at ht
  have h := (le_div_iff₀ (sq_pos_of_pos hC)).2 ht
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- A squared gain controls the preceding amplitude even for the exceptional
first increment. This is the gain furnished by the material estimates. -/
theorem iterateAmplitudeSq_squared_previous {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) :
    η ^ 2 * iterateAmplitudeSq η (i - 1) ≤ iterateAmplitudeSq η i := by
  by_cases hi1 : i = 1
  · subst i
    norm_num [iterateAmplitudeSq]
  · have hw : 0 ≤ iterateAmplitudeSq η (i - 1) := by
      unfold iterateAmplitudeSq
      split_ifs <;> positivity
    have hs : η ^ 2 ≤ η := by
      simpa only [pow_two] using mul_le_of_le_one_right hη hη1
    exact (mul_le_mul_of_nonneg_right hs hw).trans
      (iterateAmplitudeSq_previous hη1 (by omega))

/-- Squared material smallness normalizes with C^-2 at every positive
increment, preserving the exceptional first two source amplitudes. -/
theorem iterateAmplitudeSq_scaled_squared_previous_ratio
    {C₀ ρ : ℝ} (hC : 0 < C₀) (hρ : 0 < ρ) (hsmall : C₀ * ρ ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) :
    ρ ^ 2 * iterateAmplitudeSq (C₀ * ρ) (i - 1) / iterateAmplitudeSq (C₀ * ρ) i ≤ (C₀ ^ 2)⁻¹ := by
  have hw := iterateAmplitudeSq_pos (mul_pos hC hρ) i
  have hp := iterateAmplitudeSq_squared_previous (mul_pos hC hρ).le hsmall hi
  have ht : C₀ ^ 2 * (ρ ^ 2 * iterateAmplitudeSq (C₀ * ρ) (i - 1)) ≤
      iterateAmplitudeSq (C₀ * ρ) i := by simpa only [mul_pow, mul_assoc] using hp
  apply (div_le_iff₀ hw).2
  rw [mul_comm (C₀ ^ 2)] at ht
  have h := (le_div_iff₀ (sq_pos_of_pos hC)).2 ht
  simpa only [div_eq_mul_inv, mul_comm] using h

end AVenhance.Infra.Section4
