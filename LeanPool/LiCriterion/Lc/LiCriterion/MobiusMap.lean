/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
  Möbius map geometry for Li's criterion.

  The basic transform is `ρ ↦ 1 - 1/ρ` (equivalently `(ρ - 1) / ρ`).

  It sends:
  - `Re ρ = 1/2` to the unit circle `‖1 - 1/ρ‖ = 1`,
  - `Re ρ > 1/2` to the open unit disk `‖1 - 1/ρ‖ < 1`,
  - `Re ρ < 1/2` to the exterior `1 < ‖1 - 1/ρ‖`,
  for `ρ ≠ 0`.
-/

import Mathlib.Analysis.Complex.Basic

/-!
# The Möbius map `z ↦ 1 - 1/z`

Elementary norm and real-part identities for the map carrying the critical line to the unit
circle, used to turn RH into a statement about the closed unit disk.
-/

namespace LiCriterion

open Complex Real

/-- Helper: norm squared of complex difference. -/
lemma norm_sq_diff (z w : ℂ) : ‖z - w‖ ^ 2 = (z - w).re ^ 2 + (z - w).im ^ 2 := by
  have h1 : ‖z - w‖ ^ 2 = Complex.normSq (z - w) := by
    exact (Complex.normSq_eq_norm_sq (z - w)).symm
  rw [h1, Complex.normSq_apply, sub_re, sub_im, sq, sq]

/-- Helper: expanding `(a - b)²`. -/
lemma sq_sub_expand (a b : ℝ) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_sq]

/-- Helper: norm-squared inequality implies `Re` inequality. -/
lemma norm_sq_ineq_to_re (ρ : ℂ) : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 ↔ ρ.re > 1 / 2 := by
  rw [norm_sq_diff]
  have h1 : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    have : ‖ρ‖ ^ 2 = Complex.normSq ρ := (Complex.normSq_eq_norm_sq ρ).symm
    simp [this, Complex.normSq_apply, sq]
  rw [h1]
  have h2 : (ρ - 1).re = ρ.re - 1 := by
    rw [sub_re, one_re]
  have h3 : (ρ - 1).im = ρ.im := by
    rw [sub_im, one_im]
    ring
  rw [h2, h3, sq_sub_expand]
  have h_simp : ρ.re ^ 2 - 2 * ρ.re * 1 + 1 ^ 2 = ρ.re ^ 2 - 2 * ρ.re + 1 := by ring
  rw [h_simp]
  constructor
  · intro h
    have h4 :
        (ρ.re ^ 2 - 2 * ρ.re + 1) + ρ.im ^ 2 < ρ.re ^ 2 + ρ.im ^ 2 ↔
          ρ.re ^ 2 - 2 * ρ.re + 1 < ρ.re ^ 2 :=
      add_lt_add_iff_right (ρ.im ^ 2)
    have h5 : ρ.re ^ 2 - 2 * ρ.re + 1 < ρ.re ^ 2 := by
      simpa [h4] using h
    have h7 : 1 < 2 * ρ.re := by linarith
    have h8 : 1 / 2 < ρ.re := by
      rw [div_lt_iff₀ two_pos, mul_comm]
      exact h7
    exact h8
  · intro h
    have h4 :
        (ρ.re ^ 2 - 2 * ρ.re + 1) + ρ.im ^ 2 < ρ.re ^ 2 + ρ.im ^ 2 ↔
          ρ.re ^ 2 - 2 * ρ.re + 1 < ρ.re ^ 2 :=
      add_lt_add_iff_right (ρ.im ^ 2)
    rw [h4]
    have h5 : 1 / 2 < ρ.re := h
    rw [div_lt_iff₀ two_pos, mul_comm] at h5
    have h6 : 1 < 2 * ρ.re := h5
    have h8 : ρ.re ^ 2 - 2 * ρ.re + 1 < ρ.re ^ 2 := by linarith
    exact h8

/-- Helper: squaring preserves `<` for nonnegative reals. -/
lemma norm_sq_lt_norm_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a < b ↔ a ^ 2 < b ^ 2 := by
  constructor
  · intro hlt
    have h_neg : -b < a := by
      rw [neg_lt]
      have hb_pos : 0 < b := lt_of_le_of_lt ha hlt
      linarith
    exact sq_lt_sq' h_neg hlt
  · intro hsq
    have ha_eq : a = √(a ^ 2) := (Real.sqrt_sq ha).symm
    have hb_eq : b = √(b ^ 2) := (Real.sqrt_sq hb).symm
    rw [ha_eq, hb_eq]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) hsq

/-- The key strict geometric equivalence: `‖1 - 1/ρ‖ < 1 ↔ Re(ρ) > 1/2` (for `ρ ≠ 0`). -/
lemma modulus_criterion (ρ : ℂ) (hρ : ρ ≠ 0) : ‖1 - 1 / ρ‖ < 1 ↔ ρ.re > 1 / 2 := by
  have h1 : (1 : ℂ) - (1 : ℂ) / ρ = (ρ - 1) / ρ := by
    field_simp
  rw [h1, norm_div]
  have h2 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  rw [div_lt_one h2]
  have h3 : ‖ρ - 1‖ < ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := by
    have h_nn1 : 0 ≤ ‖ρ - 1‖ := norm_nonneg _
    have h_nn2 : 0 ≤ ‖ρ‖ := norm_nonneg _
    exact norm_sq_lt_norm_sq h_nn1 h_nn2
  rw [h3]
  exact norm_sq_ineq_to_re ρ

/-- The equality case: `‖ρ - 1‖² = ‖ρ‖² ↔ Re(ρ) = 1/2`. -/
lemma norm_sq_eq_to_re_half (ρ : ℂ) : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 ↔ ρ.re = 1 / 2 := by
  have hL : ‖ρ - 1‖ ^ 2 = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
    have h := norm_sq_diff ρ 1
    simpa [sub_re, sub_im, one_re, one_im, sq] using h
  have hR : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    have : ‖ρ‖ ^ 2 = Complex.normSq ρ := (Complex.normSq_eq_norm_sq ρ).symm
    simp [this, Complex.normSq_apply, sq]
  constructor
  · intro h
    have hsum : (ρ.re - 1) ^ 2 + ρ.im ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
      simpa [hL, hR] using h
    have h' : (ρ.re - 1) ^ 2 = ρ.re ^ 2 := add_right_cancel hsum
    have : ρ.re ^ 2 - 2 * ρ.re + 1 = ρ.re ^ 2 := by
      simpa [sub_sq] using h'
    have h2 : 2 * ρ.re = 1 := by linarith
    have : ρ.re = (1 : ℝ) / 2 := by
      have hmul : ρ.re * 2 = 1 := by simpa [mul_comm] using h2
      exact (eq_div_iff_mul_eq (two_ne_zero : (2 : ℝ) ≠ 0)).mpr hmul
    simpa [one_div] using this
  · intro h
    have h' : (ρ.re - 1) ^ 2 = ρ.re ^ 2 := by
      have : (1 / 2 - (1 : ℝ)) ^ 2 = (1 / 2 : ℝ) ^ 2 := by norm_num
      simp only [h]
      ring
    simp only [hL, hR, h']

/-- Exterior case: `1 < ‖1 - 1/ρ‖ ↔ Re(ρ) < 1/2` (for `ρ ≠ 0`). -/
lemma one_lt_modulus_iff_re_lt_half (ρ : ℂ) (hρ : ρ ≠ 0) : 1 < ‖1 - 1 / ρ‖ ↔ ρ.re < 1 / 2 := by
  have h1 : (1 : ℂ) - (1 : ℂ) / ρ = (ρ - 1) / ρ := by
    field_simp
  rw [h1, norm_div]
  have hρnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hρnorm_ne : ‖ρ‖ ≠ 0 := ne_of_gt hρnorm_pos
  have hdiv : (1 : ℝ) < ‖ρ - 1‖ / ‖ρ‖ ↔ ‖ρ‖ < ‖ρ - 1‖ := by
    constructor
    · intro hlt
      have hmul : (1 : ℝ) * ‖ρ‖ < (‖ρ - 1‖ / ‖ρ‖) * ‖ρ‖ :=
        mul_lt_mul_of_pos_right hlt hρnorm_pos
      simpa [div_eq_mul_inv, mul_assoc, hρnorm_ne] using hmul
    · intro hlt
      have hdiv' : ‖ρ‖ / ‖ρ‖ < ‖ρ - 1‖ / ‖ρ‖ :=
        div_lt_div_of_pos_right hlt hρnorm_pos
      simpa [hρnorm_ne] using hdiv'
  have hsq : ‖ρ‖ < ‖ρ - 1‖ ↔ ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 := by
    have hnn1 : 0 ≤ ‖ρ‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖ρ - 1‖ := norm_nonneg _
    exact norm_sq_lt_norm_sq (a := ‖ρ‖) (b := ‖ρ - 1‖) hnn1 hnn2
  have hre : ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 ↔ ρ.re < 1 / 2 := by
    have h := (norm_sq_ineq_to_re (ρ := (1 - ρ)))
    have h' : ‖ρ‖ ^ 2 < ‖1 - ρ‖ ^ 2 ↔ (1 - ρ).re > 1 / 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have h'' : ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 ↔ (1 - ρ).re > 1 / 2 := by
      simpa [norm_sub_rev] using h'
    constructor
    · intro hlt
      have : (1 - ρ).re > 1 / 2 := (h'').1 hlt
      have : (1 : ℝ) - ρ.re > 1 / 2 := by simpa [sub_re, one_re] using this
      linarith
    · intro hlt
      have : (1 : ℝ) - ρ.re > 1 / 2 := by linarith
      have : (1 - ρ).re > 1 / 2 := by simpa [sub_re, one_re] using this
      exact (h'').2 this
  constructor
  · intro hlt
    have hlt' : ‖ρ‖ < ‖ρ - 1‖ := (hdiv).1 hlt
    have hsq' : ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 := (hsq).1 hlt'
    exact (hre).1 hsq'
  · intro hlt
    have hsq' : ‖ρ‖ ^ 2 < ‖ρ - 1‖ ^ 2 := (hre).2 hlt
    have hlt' : ‖ρ‖ < ‖ρ - 1‖ := (hsq).2 hsq'
    exact (hdiv).2 hlt'

end LiCriterion
