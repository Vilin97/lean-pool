/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.Common

/-! # Basic -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open scoped BigOperators

/-!
# Basic scalar parameters for the third Section 5.3 lemma

This file contains only the manuscript scalar parameters for
`l.J.upper.bound.coarse.fluctuations.homogenization.scale` and the elementary
inequalities extracted from `(P4)`.
-/

noncomputable section

/-- The minimum quantity whose fixed small fraction is the exponent `β` in the
third Section 5.3 lemma. -/
noncomputable def section53CoarseFluctuationBetaCore {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  min (1 - hP4.sUpper - hP4.sLower)
    (min hP4.sUpper
      (min hP4.sLower
        (min (hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ))
          (hP4.sLower - (d : ℝ) / (hP4.xi : ℝ)))))

/-- The exponent `β` used in
`l.J.upper.bound.coarse.fluctuations.homogenization.scale`. -/
noncomputable def section53CoarseFluctuationBeta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  section53CoarseFluctuationBetaCore hP4 / 8

/-- The Hölder conjugate `ζ = ξ / (ξ - 1)` used in the third Section 5.3
lemma. -/
noncomputable def section53CoarseFluctuationZeta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  (hP4.xi : ℝ) / ((hP4.xi : ℝ) - 1)

/-- Parameter-only version of the Section 5.3 coarse-fluctuation beta core. -/
noncomputable def section53CoarseFluctuationBetaCoreParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  min (1 - params.sUpper - params.sLower)
    (min params.sUpper
      (min params.sLower
        (min (params.sUpper - (d : ℝ) / (params.xi : ℝ))
          (params.sLower - (d : ℝ) / (params.xi : ℝ)))))

/-- Parameter-only version of the Section 5.3 coarse-fluctuation beta. -/
noncomputable def section53CoarseFluctuationBetaParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  section53CoarseFluctuationBetaCoreParams params / 8

/-- Parameter-only version of the Section 5.3 Hölder conjugate exponent. -/
noncomputable def section53CoarseFluctuationZetaParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (params.xi : ℝ) / ((params.xi : ℝ) - 1)

@[simp]
theorem section53CoarseFluctuationBetaCoreParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCoreParams hP4.params =
      section53CoarseFluctuationBetaCore hP4 := rfl

@[simp]
theorem section53CoarseFluctuationBetaParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaParams hP4.params =
      section53CoarseFluctuationBeta hP4 := rfl

@[simp]
theorem section53CoarseFluctuationZetaParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationZetaParams hP4.params =
      section53CoarseFluctuationZeta hP4 := rfl

private theorem section53CoarseFluctuationBetaCore_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < section53CoarseFluctuationBetaCore hP4 := by
  have hgap : 0 < 1 - hP4.sUpper - hP4.sLower := by
    linarith [hP4.sum_lt_one]
  have hupper : 0 < hP4.sUpper := hP4.sUpper_pos
  have hlower : 0 < hP4.sLower := hP4.sLower_pos
  have hupper_gain : 0 < hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sUpper]
  have hlower_gain : 0 < hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCore
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

theorem section53CoarseFluctuationBeta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < section53CoarseFluctuationBeta hP4 := by
  unfold section53CoarseFluctuationBeta
  nlinarith [section53CoarseFluctuationBetaCore_pos hP4]

theorem section53CoarseFluctuationBeta_nonneg {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ section53CoarseFluctuationBeta hP4 :=
  (section53CoarseFluctuationBeta_pos hP4).le

private theorem section53CoarseFluctuationBetaCore_le_sum_gap {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCore hP4 ≤
      1 - hP4.sUpper - hP4.sLower := by
  unfold section53CoarseFluctuationBetaCore
  exact min_le_left _ _

private theorem section53CoarseFluctuationBetaCore_le_sUpper {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCore hP4 ≤ hP4.sUpper := by
  unfold section53CoarseFluctuationBetaCore
  exact (min_le_right _ _).trans (min_le_left _ _)

private theorem section53CoarseFluctuationBetaCore_le_sLower {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCore hP4 ≤ hP4.sLower := by
  unfold section53CoarseFluctuationBetaCore
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

private theorem section53CoarseFluctuationBetaCore_le_sUpper_gain {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCore hP4 ≤
      hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section53CoarseFluctuationBetaCore
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

private theorem section53CoarseFluctuationBetaCore_le_sLower_gain {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBetaCore hP4 ≤
      hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section53CoarseFluctuationBetaCore
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

theorem section53CoarseFluctuationBeta_le_sUpper {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBeta hP4 ≤ hP4.sUpper := by
  unfold section53CoarseFluctuationBeta
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  have hcore_le := section53CoarseFluctuationBetaCore_le_sUpper hP4
  nlinarith

theorem section53CoarseFluctuationBeta_le_sLower {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBeta hP4 ≤ hP4.sLower := by
  unfold section53CoarseFluctuationBeta
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  have hcore_le := section53CoarseFluctuationBetaCore_le_sLower hP4
  nlinarith

theorem section53CoarseFluctuationBeta_le_sUpper_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBeta hP4 ≤
      hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section53CoarseFluctuationBeta
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  have hcore_le := section53CoarseFluctuationBetaCore_le_sUpper_gain hP4
  nlinarith

theorem section53CoarseFluctuationBeta_le_sLower_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationBeta hP4 ≤
      hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section53CoarseFluctuationBeta
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  have hcore_le := section53CoarseFluctuationBetaCore_le_sLower_gain hP4
  nlinarith

theorem sUpper_add_sLower_add_two_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + hP4.sLower +
        2 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  unfold section53CoarseFluctuationBeta
  have hcore_le := section53CoarseFluctuationBetaCore_le_sum_gap hP4
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  nlinarith

theorem sUpper_add_sLower_add_four_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + hP4.sLower +
        4 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  unfold section53CoarseFluctuationBeta
  have hcore_le := section53CoarseFluctuationBetaCore_le_sum_gap hP4
  have hcore_nonneg : 0 ≤ section53CoarseFluctuationBetaCore hP4 :=
    (section53CoarseFluctuationBetaCore_pos hP4).le
  nlinarith

theorem sLower_add_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hupper_nonneg := hP4.sUpper_nonneg
  have hbeta_nonneg := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

theorem sLower_add_two_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + 2 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hupper_nonneg := hP4.sUpper_nonneg
  have hbeta_nonneg := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

theorem sUpper_add_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hlower_nonneg := hP4.sLower_nonneg
  have hbeta_nonneg := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

theorem sUpper_add_two_beta_le_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hlower_nonneg := hP4.sLower_nonneg
  have hbeta_nonneg := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

theorem half_sLower_add_beta_le_sLower {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP4.sLower + section53CoarseFluctuationBeta hP4) / 2 ≤ hP4.sLower := by
  have hle := section53CoarseFluctuationBeta_le_sLower hP4
  nlinarith

theorem sLower_lt_sLower_add_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower < hP4.sLower + section53CoarseFluctuationBeta hP4 := by
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem half_sLower_add_two_beta_le_sLower_add_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP4.sLower + 2 * section53CoarseFluctuationBeta hP4) / 2 ≤
      hP4.sLower + section53CoarseFluctuationBeta hP4 := by
  have hlower_nonneg := hP4.sLower_nonneg
  nlinarith

theorem sLower_add_beta_lt_sLower_add_two_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + section53CoarseFluctuationBeta hP4 <
      hP4.sLower + 2 * section53CoarseFluctuationBeta hP4 := by
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem half_sUpper_add_beta_le_sUpper {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP4.sUpper + section53CoarseFluctuationBeta hP4) / 2 ≤ hP4.sUpper := by
  have hle := section53CoarseFluctuationBeta_le_sUpper hP4
  nlinarith

theorem sUpper_lt_sUpper_add_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper < hP4.sUpper + section53CoarseFluctuationBeta hP4 := by
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem half_sUpper_add_two_beta_le_sUpper_add_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4) / 2 ≤
      hP4.sUpper + section53CoarseFluctuationBeta hP4 := by
  have hupper_nonneg := hP4.sUpper_nonneg
  nlinarith

theorem sUpper_add_beta_lt_sUpper_add_two_beta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + section53CoarseFluctuationBeta hP4 <
      hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4 := by
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem sLower_add_beta_sub_dim_div_xi_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sLower + section53CoarseFluctuationBeta hP4 -
        (d : ℝ) / (hP4.xi : ℝ) := by
  have hgain : 0 < hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sLower]
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem sUpper_add_beta_sub_dim_div_xi_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 -
        (d : ℝ) / (hP4.xi : ℝ) := by
  have hgain : 0 < hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sUpper]
  have hbeta := section53CoarseFluctuationBeta_pos hP4
  linarith

theorem section53CoarseFluctuationZeta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < section53CoarseFluctuationZeta hP4 := by
  unfold section53CoarseFluctuationZeta
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast hP4.two_le_xi
  exact div_pos (by linarith) (by linarith)

theorem one_lt_section53CoarseFluctuationZeta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    1 < section53CoarseFluctuationZeta hP4 := by
  unfold section53CoarseFluctuationZeta
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast hP4.two_le_xi
  have hden_pos : 0 < (hP4.xi : ℝ) - 1 := by linarith
  rw [one_lt_div hden_pos]
  linarith

theorem section53CoarseFluctuationZeta_le_two {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section53CoarseFluctuationZeta hP4 ≤ 2 := by
  unfold section53CoarseFluctuationZeta
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast hP4.two_le_xi
  have hden_pos : 0 < (hP4.xi : ℝ) - 1 := by linarith
  rw [div_le_iff₀ hden_pos]
  linarith

theorem inv_xi_add_inv_section53CoarseFluctuationZeta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    ((hP4.xi : ℝ)⁻¹ + (section53CoarseFluctuationZeta hP4)⁻¹) = 1 := by
  unfold section53CoarseFluctuationZeta
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast hP4.two_le_xi
  have hxi_ne : (hP4.xi : ℝ) ≠ 0 := by linarith
  have hden_ne : (hP4.xi : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hxi_ne, hden_ne]
  ring

/-- Weighted finite Cauchy-Schwarz in the square-root form used by the
expectation-level Section 5.3 RHS conversion. -/
theorem sq_sum_mul_sqrt_le_sum_mul_sum_mul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i ∈ s, 0 ≤ X i) :
    (∑ i ∈ s, w i * Real.sqrt (X i)) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * X i) := by
  let f : ι → ℝ := fun i => Real.sqrt (w i)
  let g : ι → ℝ := fun i => Real.sqrt (w i) * Real.sqrt (X i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hleft :
      (∑ i ∈ s, f i * g i) = ∑ i ∈ s, w i * Real.sqrt (X i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [f, g]
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hsum_f :
      (∑ i ∈ s, f i ^ 2) = ∑ i ∈ s, w i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [f, Real.sq_sqrt (hw i hi)]
  have hsum_g :
      (∑ i ∈ s, g i ^ 2) = ∑ i ∈ s, w i * X i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [g, mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hX i hi)]
  simpa [hleft, hsum_f, hsum_g] using hcs

/-- Paired weighted finite Cauchy-Schwarz estimate, with separate scalar
weights on the two components. -/
theorem weighted_pair_sq_sum_mul_sqrt_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (wg wf G F : ι → ℝ) {σ τ : ℝ}
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hwg : ∀ i ∈ s, 0 ≤ wg i) (hwf : ∀ i ∈ s, 0 ≤ wf i)
    (hG : ∀ i ∈ s, 0 ≤ G i) (hF : ∀ i ∈ s, 0 ≤ F i) :
    σ * (∑ i ∈ s, wg i * Real.sqrt (G i)) ^ 2 +
        τ * (∑ i ∈ s, wf i * Real.sqrt (F i)) ^ 2 ≤
      (∑ i ∈ s, wg i) * (∑ i ∈ s, wg i * (σ * G i)) +
        (∑ i ∈ s, wf i) * (∑ i ∈ s, wf i * (τ * F i)) := by
  have hg :=
    sq_sum_mul_sqrt_le_sum_mul_sum_mul s wg G hwg hG
  have hf :=
    sq_sum_mul_sqrt_le_sum_mul_sum_mul s wf F hwf hF
  have hg' :
      σ * (∑ i ∈ s, wg i * Real.sqrt (G i)) ^ 2 ≤
        σ * ((∑ i ∈ s, wg i) * (∑ i ∈ s, wg i * G i)) :=
    mul_le_mul_of_nonneg_left hg hσ
  have hf' :
      τ * (∑ i ∈ s, wf i * Real.sqrt (F i)) ^ 2 ≤
        τ * ((∑ i ∈ s, wf i) * (∑ i ∈ s, wf i * F i)) :=
    mul_le_mul_of_nonneg_left hf hτ
  calc
    σ * (∑ i ∈ s, wg i * Real.sqrt (G i)) ^ 2 +
        τ * (∑ i ∈ s, wf i * Real.sqrt (F i)) ^ 2
        ≤
      σ * ((∑ i ∈ s, wg i) * (∑ i ∈ s, wg i * G i)) +
        τ * ((∑ i ∈ s, wf i) * (∑ i ∈ s, wf i * F i)) :=
          add_le_add hg' hf'
    _ =
      (∑ i ∈ s, wg i) * (∑ i ∈ s, wg i * (σ * G i)) +
        (∑ i ∈ s, wf i) * (∑ i ∈ s, wf i * (τ * F i)) := by
          have hGsum :
              (∑ i ∈ s, wg i * (σ * G i)) =
                σ * (∑ i ∈ s, wg i * G i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
          have hFsum :
              (∑ i ∈ s, wf i * (τ * F i)) =
                τ * (∑ i ∈ s, wf i * F i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
          rw [hGsum, hFsum]
          ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
