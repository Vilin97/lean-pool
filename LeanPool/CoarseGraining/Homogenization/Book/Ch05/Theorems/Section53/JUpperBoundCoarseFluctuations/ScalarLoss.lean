/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic

/-! # Scalar Loss -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

/-!
# Uniform scalar losses for the third Section 5.3 lemma

This file isolates the purely scalar estimates that keep the Section 5.3
coarse-fluctuation constant independent of the scale parameters.  In
particular, it bounds the corrected Section 5.2 two-exponent loss at the
`β`-shifted exponents by the manuscript `ξ β^{-3}` factor.
-/

noncomputable section

private theorem inv_sq_mul_div_le_xi_mul_inv_cube
    {s β D ξ : ℝ} (hβ : 0 < β) (hs : 0 < s) (hD : β ≤ D)
    (hβ_le_s : β ≤ s) (hξ_nonneg : 0 ≤ ξ) :
    s⁻¹ ^ 2 * (ξ / D) ≤ ξ * (β ^ 3)⁻¹ := by
  have hD_pos : 0 < D := lt_of_lt_of_le hβ hD
  have hs_inv_le_beta_inv : s⁻¹ ≤ β⁻¹ :=
    (inv_le_inv₀ hs hβ).mpr hβ_le_s
  have hs_inv_sq_le : s⁻¹ ^ 2 ≤ β⁻¹ ^ 2 := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hs_inv_le_beta_inv 2
  have hdiv_le : ξ / D ≤ ξ / β :=
    div_le_div_of_nonneg_left hξ_nonneg hβ hD
  have hdiv_nonneg : 0 ≤ ξ / D := div_nonneg hξ_nonneg hD_pos.le
  calc
    s⁻¹ ^ 2 * (ξ / D) ≤ β⁻¹ ^ 2 * (ξ / β) :=
      mul_le_mul hs_inv_sq_le hdiv_le hdiv_nonneg (sq_nonneg _)
    _ = ξ * (β ^ 3)⁻¹ := by
      field_simp [hβ.ne']

private theorem inv_sq_mul_inv_sq_le_xi_mul_inv_cube
    {s β ξ : ℝ} (hβ : 0 < β) (hs : 0 < s)
    (hβ_le_s : β ≤ s) (hs_inv_le_xi : s⁻¹ ≤ ξ) :
    s⁻¹ ^ 2 * β⁻¹ ^ 2 ≤ ξ * (β ^ 3)⁻¹ := by
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hξ_nonneg : 0 ≤ ξ := hs_inv_nonneg.trans hs_inv_le_xi
  have hβ_inv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ.le
  have hs_inv_le_beta_inv : s⁻¹ ≤ β⁻¹ :=
    (inv_le_inv₀ hs hβ).mpr hβ_le_s
  calc
    s⁻¹ ^ 2 * β⁻¹ ^ 2 =
        (s⁻¹ * s⁻¹) * (β⁻¹ * β⁻¹) := by ring
    _ ≤ (ξ * β⁻¹) * (β⁻¹ * β⁻¹) := by
      exact mul_le_mul
        (mul_le_mul hs_inv_le_xi hs_inv_le_beta_inv hs_inv_nonneg hξ_nonneg)
        (le_rfl : β⁻¹ * β⁻¹ ≤ β⁻¹ * β⁻¹)
        (mul_nonneg hβ_inv_nonneg hβ_inv_nonneg)
        (mul_nonneg hξ_nonneg hβ_inv_nonneg)
    _ = ξ * (β ^ 3)⁻¹ := by
      field_simp [hβ.ne']

private theorem section52MomentLossCoeff_shift_le_xi_beta_cubed_core
    {s β D ξ : ℝ} (hβ : 0 < β) (hs : 0 < s) (hD : β ≤ D)
    (hβ_le_s : β ≤ s) (hs_inv_le_xi : s⁻¹ ≤ ξ) (hξ_nonneg : 0 ≤ ξ) :
    s⁻¹ ^ 2 * (ξ / D + β⁻¹ ^ 2) ≤
      2 * ξ * (β ^ 3)⁻¹ := by
  have hterm1 :=
    inv_sq_mul_div_le_xi_mul_inv_cube hβ hs hD hβ_le_s hξ_nonneg
  have hterm2 :=
    inv_sq_mul_inv_sq_le_xi_mul_inv_cube hβ hs hβ_le_s hs_inv_le_xi
  calc
    s⁻¹ ^ 2 * (ξ / D + β⁻¹ ^ 2) =
        s⁻¹ ^ 2 * (ξ / D) + s⁻¹ ^ 2 * β⁻¹ ^ 2 := by ring
    _ ≤ ξ * (β ^ 3)⁻¹ + ξ * (β ^ 3)⁻¹ := add_le_add hterm1 hterm2
    _ = 2 * ξ * (β ^ 3)⁻¹ := by ring

theorem section53CoarseFluctuationBeta_inv_le_xi_of_sUpper
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper⁻¹ ≤ (hP4.xi : ℝ) := by
  have hdim : (1 : ℝ) ≤ (d : ℝ) := by
    have hd : 1 ≤ d := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_dim
    exact_mod_cast hd
  have hxi_pos : 0 < (hP4.xi : ℝ) := by exact_mod_cast hP4.xi_pos
  have hs_pos := hP4.sUpper_pos
  have hxi_inv_le_s : (hP4.xi : ℝ)⁻¹ ≤ hP4.sUpper := by
    calc
      (hP4.xi : ℝ)⁻¹ ≤ (d : ℝ) / (hP4.xi : ℝ) := by
        rw [div_eq_mul_inv]
        exact le_mul_of_one_le_left (inv_nonneg.mpr hxi_pos.le) hdim
      _ ≤ hP4.sUpper := hP4.dim_div_xi_lt_sUpper.le
  exact (inv_le_comm₀ hs_pos hxi_pos).mpr hxi_inv_le_s

theorem section53CoarseFluctuationBeta_inv_le_xi_of_sLower
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower⁻¹ ≤ (hP4.xi : ℝ) := by
  have hdim : (1 : ℝ) ≤ (d : ℝ) := by
    have hd : 1 ≤ d := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_dim
    exact_mod_cast hd
  have hxi_pos : 0 < (hP4.xi : ℝ) := by exact_mod_cast hP4.xi_pos
  have hs_pos := hP4.sLower_pos
  have hxi_inv_le_s : (hP4.xi : ℝ)⁻¹ ≤ hP4.sLower := by
    calc
      (hP4.xi : ℝ)⁻¹ ≤ (d : ℝ) / (hP4.xi : ℝ) := by
        rw [div_eq_mul_inv]
        exact le_mul_of_one_le_left (inv_nonneg.mpr hxi_pos.le) hdim
      _ ≤ hP4.sLower := hP4.dim_div_xi_lt_sLower.le
  exact (inv_le_comm₀ hs_pos hxi_pos).mpr hxi_inv_le_s

private theorem shiftedMomentDenom_upper_beta_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sUpper + β) := by
  intro β
  have hdim : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  have hhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using section53CoarseFluctuationBeta_nonneg hP4
  have hlower_nonneg : 0 ≤ hP4.sLower := hP4.sLower_nonneg
  have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.zero_le hP4.xi
  have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le d) hxi_nonneg
  nlinarith

private theorem shiftedMomentDenom_lower_beta_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sLower + β) := by
  intro β
  have hdim : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  have hhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using section53CoarseFluctuationBeta_nonneg hP4
  have hupper_nonneg : 0 ≤ hP4.sUpper := hP4.sUpper_nonneg
  have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.zero_le hP4.xi
  have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le d) hxi_nonneg
  nlinarith

theorem section52MomentLossCoeff_upper_beta_shift_le_xi_beta_cubed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    section52MomentLossCoeff d hP4.xi hP4.sUpper (hP4.sUpper + β) ≤
      2 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ := by
  intro β
  have hβ : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs : 0 < hP4.sUpper := hP4.sUpper_pos
  have hβ_le_s : β ≤ hP4.sUpper := by
    simpa [β] using section53CoarseFluctuationBeta_le_sUpper hP4
  have hD : β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sUpper + β) := by
    simpa [β] using shiftedMomentDenom_upper_beta_le hP4
  have hsinv := section53CoarseFluctuationBeta_inv_le_xi_of_sUpper hP4
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  simpa [section52MomentLossCoeff, sub_self] using
    section52MomentLossCoeff_shift_le_xi_beta_cubed_core
      (s := hP4.sUpper) (β := β)
      (D := ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
        (hP4.sUpper + β))
      (ξ := (hP4.xi : ℝ)) hβ hs hD hβ_le_s hsinv hxi_nonneg

theorem section52MomentLossCoeff_lower_beta_shift_le_xi_beta_cubed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    section52MomentLossCoeff d hP4.xi hP4.sLower (hP4.sLower + β) ≤
      2 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ := by
  intro β
  have hβ : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs : 0 < hP4.sLower := hP4.sLower_pos
  have hβ_le_s : β ≤ hP4.sLower := by
    simpa [β] using section53CoarseFluctuationBeta_le_sLower hP4
  have hD : β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sLower + β) := by
    simpa [β] using shiftedMomentDenom_lower_beta_le hP4
  have hsinv := section53CoarseFluctuationBeta_inv_le_xi_of_sLower hP4
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  simpa [section52MomentLossCoeff, sub_self] using
    section52MomentLossCoeff_shift_le_xi_beta_cubed_core
      (s := hP4.sLower) (β := β)
      (D := ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
        (hP4.sLower + β))
      (ξ := (hP4.xi : ℝ)) hβ hs hD hβ_le_s hsinv hxi_nonneg

theorem section52MomentLossCoeff_upper_two_beta_shift_le_xi_beta_cubed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    section52MomentLossCoeff d hP4.xi (hP4.sUpper + β)
        (hP4.sUpper + 2 * β) ≤
      2 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ := by
  intro β
  have hβ : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs : 0 < hP4.sUpper + β := add_pos hP4.sUpper_pos hβ
  have hβ_le_s : β ≤ hP4.sUpper + β := by linarith [hP4.sUpper_nonneg]
  have hD : β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sUpper + 2 * β) := by
    have hdim : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
    have hhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    have hlower_nonneg : 0 ≤ hP4.sLower := hP4.sLower_nonneg
    have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
      exact_mod_cast Nat.zero_le hP4.xi
    have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
      div_nonneg (by exact_mod_cast Nat.zero_le d) hxi_nonneg
    nlinarith
  have hsinv : (hP4.sUpper + β)⁻¹ ≤ (hP4.xi : ℝ) := by
    have hle : hP4.sUpper ≤ hP4.sUpper + β := by linarith [hβ.le]
    have hinv : (hP4.sUpper + β)⁻¹ ≤ hP4.sUpper⁻¹ :=
      (inv_le_inv₀ hs hP4.sUpper_pos).mpr hle
    exact hinv.trans (section53CoarseFluctuationBeta_inv_le_xi_of_sUpper hP4)
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hsub : hP4.sUpper + 2 * β - (hP4.sUpper + β) = β := by ring
  have htwosub : 2 * β + -β = β := by ring
  simpa [section52MomentLossCoeff, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, hsub, htwosub] using
    section52MomentLossCoeff_shift_le_xi_beta_cubed_core
      (s := hP4.sUpper + β) (β := β)
      (D := ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
        (hP4.sUpper + 2 * β))
      (ξ := (hP4.xi : ℝ)) hβ hs hD hβ_le_s hsinv hxi_nonneg

theorem section52MomentLossCoeff_lower_two_beta_shift_le_xi_beta_cubed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    let β := section53CoarseFluctuationBeta hP4
    section52MomentLossCoeff d hP4.xi (hP4.sLower + β)
        (hP4.sLower + 2 * β) ≤
      2 * (hP4.xi : ℝ) * (β ^ 3)⁻¹ := by
  intro β
  have hβ : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs : 0 < hP4.sLower + β := add_pos hP4.sLower_pos hβ
  have hβ_le_s : β ≤ hP4.sLower + β := by linarith [hP4.sLower_nonneg]
  have hD : β ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
      (hP4.sLower + 2 * β) := by
    have hdim : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
    have hhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    have hupper_nonneg : 0 ≤ hP4.sUpper := hP4.sUpper_nonneg
    have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
      exact_mod_cast Nat.zero_le hP4.xi
    have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
      div_nonneg (by exact_mod_cast Nat.zero_le d) hxi_nonneg
    nlinarith
  have hsinv : (hP4.sLower + β)⁻¹ ≤ (hP4.xi : ℝ) := by
    have hle : hP4.sLower ≤ hP4.sLower + β := by linarith [hβ.le]
    have hinv : (hP4.sLower + β)⁻¹ ≤ hP4.sLower⁻¹ :=
      (inv_le_inv₀ hs hP4.sLower_pos).mpr hle
    exact hinv.trans (section53CoarseFluctuationBeta_inv_le_xi_of_sLower hP4)
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hsub : hP4.sLower + 2 * β - (hP4.sLower + β) = β := by ring
  have htwosub : 2 * β + -β = β := by ring
  simpa [section52MomentLossCoeff, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, hsub, htwosub] using
    section52MomentLossCoeff_shift_le_xi_beta_cubed_core
      (s := hP4.sLower + β) (β := β)
      (D := ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
        (hP4.sLower + 2 * β))
      (ξ := (hP4.xi : ℝ)) hβ hs hD hβ_le_s hsinv hxi_nonneg

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
