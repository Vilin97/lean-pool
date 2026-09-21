/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
  Genus-1 estimates for Li's criterion.

  The genus-0 approach tries to bound individual Li summands by `O(1/‖ρ‖)`, which is too strong
  for ξ: the natural Weierstrass product is genus 1 and only gives square-summability.

  The key trick is to *pair* zeros `ρ` and `1-ρ`. On the level of the Li summand, this produces
  the core expression

    `2 - (w^m + w^{-m})`

  which is `O(‖w-1‖^2)` when `w` is near `1`. Since `w-1 = -(1/ρ)`, this yields an eventual bound
  by `C(m) / ‖ρ‖^2`, matching the genus-1 hypothesis.
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic

/-!
# Genus-1 pairing of the Li summands

The core term `2 - (wᵐ + w⁻ᵐ)` and the identity pairing a zero `ρ` with `1 - ρ`, which is what
makes the sum over zeros converge at genus 1.
-/

open scoped BigOperators

namespace LiCriterion

noncomputable section

/-- The paired genus-1 core term `2 - (w^m + w^{-m})`. -/
def core (m : ℕ) (w : ℂ) : ℂ := (2 : ℂ) - (w ^ m + (w ^ m)⁻¹)

/-- The basic Li summand written as `1 - w^{-m}` (with the exponent as a `ℤ`). -/
def liTerm (m : ℕ) (w : ℂ) : ℂ := (1 : ℂ) - w ^ (-(m : ℤ))

lemma liTerm_add_liTerm_inv (m : ℕ) (w : ℂ) :
    liTerm m w + liTerm m w⁻¹ = core m w := by
  simp [liTerm, core, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  norm_num

lemma two_sub_add_inv_eq_neg_sq_div (t : ℂ) (ht : t ≠ 0) :
    (2 : ℂ) - (t + t⁻¹) = -((t - 1) ^ 2) / t := by
  field_simp [ht]
  ring

lemma core_eq_neg_sq_div (m : ℕ) (w : ℂ) (hw : w ≠ 0) :
    core m w = -((w ^ m - 1) ^ 2) / (w ^ m) := by
  have ht : w ^ m ≠ 0 := pow_ne_zero m hw
  simpa [core] using (two_sub_add_inv_eq_neg_sq_div (t := w ^ m) ht)

/-- If `‖w - 1‖ ≤ 1/2` then `‖w‖ ≤ 3/2`. -/
lemma norm_le_three_halves_of_norm_sub_one_le_half {w : ℂ} (hw : ‖w - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖w‖ ≤ (3 / 2 : ℝ) := by
  have hw' : (w - 1) + 1 = w := sub_add_cancel w (1 : ℂ)
  have h := norm_add_le (w - 1) (1 : ℂ)
  have h' := h
  rw [hw'] at h'
  have h'' := h'
  rw [norm_one] at h''
  -- h'' : ‖w‖ ≤ ‖w - 1‖ + 1, hw : ‖w - 1‖ ≤ 1 / 2
  calc ‖w‖ ≤ ‖w - 1‖ + 1 := h''
    _ ≤ 1 / 2 + 1 := by linarith
    _ = 3 / 2 := by norm_num

/-- If `‖w - 1‖ ≤ 1/2` then `1/2 ≤ ‖w‖`. -/
lemma one_half_le_norm_of_norm_sub_one_le_half {w : ℂ} (hw : ‖w - 1‖ ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖w‖ := by
  have h1 : w - (w - 1) = (1 : ℂ) := by
    simp [sub_sub_cancel]
  have h := norm_sub_le w (w - 1)
  have h' := h
  rw [h1] at h'
  have h'' := h'
  rw [norm_one] at h''
  linarith [h'', hw]

/-- Algebraic identity used in zero pairing: if `z ≠ 0, 1`, then

`1 - 1/(1-z) = (1 - 1/z)⁻¹`. -/
lemma one_sub_one_div_one_sub_eq_inv_one_sub_one_div {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (1 : ℂ) - (1 : ℂ) / (1 - z) = ((1 : ℂ) - (1 : ℂ) / z)⁻¹ := by
  have h1z : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  field_simp [hz, h1z]
  ring

/-- The paired Li summand (at `z` and `1-z`) collapses to the genus‑1 core term. -/
lemma paired_liTerm_eq_core (m : ℕ) {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) :
    liTerm m ((1 : ℂ) - (1 : ℂ) / z) + liTerm m ((1 : ℂ) - (1 : ℂ) / (1 - z)) =
      core m ((1 : ℂ) - (1 : ℂ) / z) := by
  set w : ℂ := (1 : ℂ) - (1 : ℂ) / z
  have hw : (1 : ℂ) - (1 : ℂ) / (1 - z) = w⁻¹ := by
    dsimp [w]
    simpa using (one_sub_one_div_one_sub_eq_inv_one_sub_one_div (z := z) hz hz1)
  calc
    liTerm m w + liTerm m ((1 : ℂ) - (1 : ℂ) / (1 - z))
        = liTerm m w + liTerm m w⁻¹ := by
            rw [hw]
    _ = core m w := liTerm_add_liTerm_inv m w
    _ = core m ((1 : ℂ) - (1 : ℂ) / z) := by rfl

/-- Norm bound for the genus-1 paired core term.

If `w` lies within `1/2` of `1`, then `‖core m w‖` is `O(‖w-1‖^2)` with an explicit constant.
This is the estimate used to make the Li zero-sum summable after pairing zeros. -/
lemma norm_core_le_const_mul_norm_sub_one_sq (m : ℕ) {w : ℂ} (hw : ‖w - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖core m w‖ ≤ ((2 : ℝ) ^ m) * (∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)) ^ 2 * ‖w - 1‖ ^ 2 := by
  have hw_upper : ‖w‖ ≤ (3 / 2 : ℝ) := norm_le_three_halves_of_norm_sub_one_le_half (w := w) hw
  have hw_lower : (1 / 2 : ℝ) ≤ ‖w‖ := one_half_le_norm_of_norm_sub_one_le_half (w := w) hw
  have hw_ne : w ≠ 0 := by
    have : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le (by norm_num) hw_lower
    exact (norm_pos_iff).1 this
  -- geometric sum bound: ‖∑_{i<m} w^i‖ ≤ ∑_{i<m} (3/2)^i
  have hsum_w : ‖∑ i ∈ Finset.range m, w ^ i‖ ≤ ∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i) := by
    refine (norm_sum_le (Finset.range m) (fun i => w ^ i)).trans ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    have : ‖w ^ i‖ = ‖w‖ ^ i := by simp [norm_pow]
    have hpow : ‖w‖ ^ i ≤ (3 / 2 : ℝ) ^ i := pow_le_pow_left₀ (norm_nonneg w) hw_upper i
    simpa [this] using hpow
  -- inverse power bound: ‖(w^m)⁻¹‖ ≤ 2^m
  have hinv_pow : ‖(w ^ m)⁻¹‖ ≤ (2 : ℝ) ^ m := by
    have hpow : (1 / 2 : ℝ) ^ m ≤ ‖w‖ ^ m := pow_le_pow_left₀ (by positivity) hw_lower m
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
    have : (1 : ℝ) / (‖w‖ ^ m) ≤ (1 : ℝ) / ((1 / 2 : ℝ) ^ m) :=
      one_div_le_one_div_of_le hpos hpow
    simpa [norm_inv, norm_pow] using this
  -- bound ‖w^m - 1‖ via geometric sum
  have hgeom : ‖w ^ m - 1‖ ≤ (∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)) * ‖w - 1‖ := by
    have hmul : ‖w ^ m - 1‖ = ‖∑ i ∈ Finset.range m, w ^ i‖ * ‖w - 1‖ := by
      have := geom_sum_mul (R := ℂ) w m
      have : w ^ m - 1 = (∑ i ∈ Finset.range m, w ^ i) * (w - 1) := by
        simpa [eq_comm] using this
      simp [this]
    have := mul_le_mul_of_nonneg_right hsum_w (norm_nonneg (w - 1))
    simpa [hmul, mul_assoc] using this
  have hcore : core m w = -((w ^ m - 1) ^ 2) / (w ^ m) := by
    simpa [pow_two] using core_eq_neg_sq_div m w hw_ne
  -- final estimate
  calc
    ‖core m w‖ = ‖-((w ^ m - 1) ^ 2) / (w ^ m)‖ := by simp [hcore]
    _ = ‖((w ^ m - 1) ^ 2) / (w ^ m)‖ := by simp
    _ = ‖(w ^ m - 1) ^ 2‖ * ‖(w ^ m)⁻¹‖ := by simp [div_eq_mul_inv]
    _ = (‖w ^ m - 1‖ ^ 2) * ‖(w ^ m)⁻¹‖ := by simp [pow_two]
    _ ≤ (((∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)) * ‖w - 1‖) ^ 2) * ‖(w ^ m)⁻¹‖ := by
          gcongr
    _ ≤ (((∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)) * ‖w - 1‖) ^ 2) * ((2 : ℝ) ^ m) := by
          gcongr
    _ = ((2 : ℝ) ^ m) * (∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)) ^ 2 * ‖w - 1‖ ^ 2 := by
          ring

end

end LiCriterion
