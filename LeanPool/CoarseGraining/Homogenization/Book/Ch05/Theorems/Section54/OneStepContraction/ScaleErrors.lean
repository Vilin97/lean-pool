/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.BetaBridge

/-! # Scale Errors -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Scale-separation errors for the one-step contraction

The Section 5.3 tail terms contain the square of `widetildeTheta_0`.  This
file records the Section 5.4 logarithmic absorption needed to make those tails
small.  Constants are intentionally harmless: the final theorem will absorb
the numerical factors into its existential constant.
-/

/-- A scale-separation constant sufficient for the current one-step tail
absorption. -/
noncomputable def oneStepScaleSeparationConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  2 * (Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 *
    Real.log 3)⁻¹

/-- The one-step scale-separation constant is positive. -/
theorem oneStepScaleSeparationConst_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < oneStepScaleSeparationConst hP4 := by
  unfold oneStepScaleSeparationConst
  have hβ :
      0 < Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 :=
    section53CoarseFluctuationBeta_pos hP4
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  positivity

private theorem oneStepScaleSeparationConst_ge_section54
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    2 * (VarianceBoundGoodScale.section54VarianceBeta hP4 * Real.log 3)⁻¹ ≤
      oneStepScaleSeparationConst hP4 := by
  have hβ53 :
      0 < Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 :=
    section53CoarseFluctuationBeta_pos hP4
  have hβ54 : 0 < VarianceBoundGoodScale.section54VarianceBeta hP4 :=
    VarianceBoundGoodScale.section54VarianceBeta_pos hP4
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hβ_le :
      Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 ≤
        VarianceBoundGoodScale.section54VarianceBeta hP4 :=
    section53CoarseFluctuationBeta_le_section54VarianceBeta hP4
  have hprod_le :
      Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 *
          Real.log 3 ≤
        VarianceBoundGoodScale.section54VarianceBeta hP4 * Real.log 3 :=
    mul_le_mul_of_nonneg_right hβ_le hlog.le
  have hprod53 :
      0 <
        Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 *
          Real.log 3 :=
    mul_pos hβ53 hlog
  have hinv :
      (VarianceBoundGoodScale.section54VarianceBeta hP4 * Real.log 3)⁻¹ ≤
        (Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 *
          Real.log 3)⁻¹ :=
    inv_anti₀ hprod53 hprod_le
  unfold oneStepScaleSeparationConst
  exact mul_le_mul_of_nonneg_left hinv (by norm_num)

private theorem rpow_decay_le_log_scale_two
    {β C ξ δ T : ℝ} {m : ℕ}
    (hβ : 0 < β) (hξ : 1 ≤ ξ)
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hC : 2 * (β * Real.log 3)⁻¹ ≤ C)
    (hm : C * ξ * Real.log (2 + δ⁻¹ * ξ * T) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ) (-β * (m : ℝ)) ≤
      Real.rpow (2 + δ⁻¹ * ξ * T) (-2 : ℝ) := by
  let A : ℝ := 2 + δ⁻¹ * ξ * T
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hβlog : 0 < β * Real.log (3 : ℝ) := mul_pos hβ hlog3
  have hξ_nonneg : 0 ≤ ξ := by linarith
  have hA_ge_two : 2 ≤ A := by
    have hprod : 0 ≤ δ⁻¹ * ξ * T := by
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) hξ_nonneg) hT
    dsimp [A]
    linarith
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) hA_ge_two
  have hlogA_nonneg : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hsep0 :
      (2 * (β * Real.log 3)⁻¹) * Real.log A ≤ (m : ℝ) := by
    have hC2 : 2 * (β * Real.log 3)⁻¹ ≤ C * ξ := by
      have hC_nonneg : 0 ≤ C := by
        exact le_trans (by positivity) hC
      have hC_le_Cξ : C ≤ C * ξ := by
        simpa using mul_le_mul_of_nonneg_left hξ hC_nonneg
      exact hC.trans hC_le_Cξ
    calc
      (2 * (β * Real.log 3)⁻¹) * Real.log A ≤
          (C * ξ) * Real.log A :=
        mul_le_mul_of_nonneg_right hC2 hlogA_nonneg
      _ = C * ξ * Real.log A := by ring
      _ ≤ (m : ℝ) := by simpa [A] using hm
  have hexp_le :
      Real.log (3 : ℝ) * (-β * (m : ℝ)) ≤ Real.log A * (-2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsep0 hβlog.le
    have htwo : β * Real.log (3 : ℝ) *
          ((2 * (β * Real.log 3)⁻¹) * Real.log A) =
        2 * Real.log A := by
      field_simp [hβlog.ne']
    have hmain : 2 * Real.log A ≤ β * Real.log (3 : ℝ) * (m : ℝ) := by
      calc
        2 * Real.log A =
            β * Real.log (3 : ℝ) *
              ((2 * (β * Real.log 3)⁻¹) * Real.log A) := htwo.symm
        _ ≤ β * Real.log (3 : ℝ) * (m : ℝ) := hmul
    calc
      Real.log (3 : ℝ) * (-β * (m : ℝ)) =
          -(β * Real.log (3 : ℝ) * (m : ℝ)) := by ring
      _ ≤ -(2 * Real.log A) := neg_le_neg hmain
      _ = Real.log A * (-2 : ℝ) := by ring
  calc
    Real.rpow (3 : ℝ) (-β * (m : ℝ)) =
        Real.exp (Real.log (3 : ℝ) * (-β * (m : ℝ))) := by
        simpa using
          (Real.rpow_def_of_pos (x := (3 : ℝ))
            (y := -β * (m : ℝ)) (by norm_num : 0 < (3 : ℝ)))
    _ ≤ Real.exp (Real.log A * (-2 : ℝ)) :=
        Real.exp_le_exp.mpr hexp_le
    _ = Real.rpow A (-2 : ℝ) := by
        simpa using
          (Real.rpow_def_of_pos (x := A) (y := (-2 : ℝ)) hA_pos).symm

private theorem rpow_neg_two_mul_sq_le_sqrt_delta
    {δ A T : ℝ} (hδ_pos : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    (hA_ge_one : 1 ≤ A) (hT_nonneg : 0 ≤ T)
    (hT_le : T ≤ δ * A) :
    Real.rpow A (-2 : ℝ) * T ^ (2 : ℕ) ≤ Real.sqrt δ := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hA_inv_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr hA_pos.le
  have hT_over_A : A⁻¹ * T ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left hT_le hA_inv_nonneg
    have hcancel : A⁻¹ * (δ * A) = δ := by
      field_simp [hA_pos.ne']
    rw [hcancel] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hA_m2 : Real.rpow A (-2 : ℝ) = A⁻¹ ^ (2 : ℕ) := by
    calc
      Real.rpow A (-2 : ℝ) = (Real.rpow A (2 : ℝ))⁻¹ := by
        simp
      _ = (A ^ (2 : ℕ))⁻¹ := by
        exact congrArg Inv.inv (Real.rpow_natCast A 2)
      _ = A⁻¹ ^ (2 : ℕ) := by
        field_simp [hA_pos.ne']
  have hT_over_A_sq : (A⁻¹ * T) ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (mul_nonneg hA_inv_nonneg hT_nonneg) hT_over_A 2
  have hdelta_sq_le_delta : δ ^ (2 : ℕ) ≤ δ := by
    have hdelta_le_one : δ ≤ 1 :=
      hδ_le_half.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
    calc
      δ ^ (2 : ℕ) = δ * δ := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hdelta_le_one hδ_pos.le
      _ = δ := by ring
  have hdelta_le_sqrt :
      δ ≤ Real.sqrt δ :=
    delta_le_sqrt_of_pos_of_le_half hδ_pos hδ_le_half
  calc
    Real.rpow A (-2 : ℝ) * T ^ (2 : ℕ) =
        (A⁻¹ * T) ^ (2 : ℕ) := by
        rw [hA_m2]
        ring
    _ ≤ δ ^ (2 : ℕ) := hT_over_A_sq
    _ ≤ δ := hdelta_sq_le_delta
    _ ≤ Real.sqrt δ := hdelta_le_sqrt

private theorem rpow_neg_two_mul_self_le_sqrt_delta
    {δ A T : ℝ} (hδ_pos : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    (hA_ge_one : 1 ≤ A) (hT_nonneg : 0 ≤ T)
    (hT_le : T ≤ δ * A) :
    Real.rpow A (-2 : ℝ) * T ≤ Real.sqrt δ := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hA_inv_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr hA_pos.le
  have hA_inv_le_one : A⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ hA_ge_one
  have hT_over_A : A⁻¹ * T ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left hT_le hA_inv_nonneg
    have hcancel : A⁻¹ * (δ * A) = δ := by
      field_simp [hA_pos.ne']
    rw [hcancel] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hA_m2 : Real.rpow A (-2 : ℝ) = A⁻¹ ^ (2 : ℕ) := by
    calc
      Real.rpow A (-2 : ℝ) = (Real.rpow A (2 : ℝ))⁻¹ := by
        simp
      _ = (A ^ (2 : ℕ))⁻¹ := by
        exact congrArg Inv.inv (Real.rpow_natCast A 2)
      _ = A⁻¹ ^ (2 : ℕ) := by
        field_simp [hA_pos.ne']
  have hlinear :
      Real.rpow A (-2 : ℝ) * T ≤ A⁻¹ * T := by
    rw [hA_m2, sq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left hA_inv_nonneg hA_inv_le_one) hT_nonneg
  have hdelta_le_sqrt :
      δ ≤ Real.sqrt δ :=
    delta_le_sqrt_of_pos_of_le_half hδ_pos hδ_le_half
  exact hlinear.trans (hT_over_A.trans hdelta_le_sqrt)

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P (0 : ℤ) hP4 := by
  simp [Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

private theorem le_delta_mul_log_scale_argument
    {δ ξ T : ℝ} (hδ_pos : 0 < δ) (hξ_one : 1 ≤ ξ) (hT_nonneg : 0 ≤ T) :
    T ≤ δ * (2 + δ⁻¹ * ξ * T) := by
  have hξT : T ≤ ξ * T := by
    calc
      T = 1 * T := by ring
      _ ≤ ξ * T := mul_le_mul_of_nonneg_right hξ_one hT_nonneg
  have hcore : T ≤ δ * (δ⁻¹ * ξ * T) := by
    calc
      T ≤ ξ * T := hξT
      _ = δ * (δ⁻¹ * ξ * T) := by
        field_simp [hδ_pos.ne']
  have harg_le : δ⁻¹ * ξ * T ≤ 2 + δ⁻¹ * ξ * T := by
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    exact le_add_of_nonneg_left htwo_nonneg
  exact hcore.trans (mul_le_mul_of_nonneg_left harg_le hδ_pos.le)

/-- The logarithmic scale separation absorbs the square of
`widetildeTheta_0`. -/
theorem oneStepScaleSeparation_absorbs_widetildeThetaSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (hm :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ)
        (-(VarianceBoundGoodScale.section54VarianceBeta hP4) * (m : ℝ)) *
        (widetildeThetaAtScale P (0 : ℤ) hP4) ^ (2 : ℕ) ≤
      Real.sqrt delta := by
  let T : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let A : ℝ := 2 + delta⁻¹ * (hP4.xi : ℝ) * T
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using widetildeThetaAtScale_zero_nonneg hP4
  have hxi_one : 1 ≤ (hP4.xi : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hP4.xi_pos)
  have hdecay :
      Real.rpow (3 : ℝ)
          (-(VarianceBoundGoodScale.section54VarianceBeta hP4) * (m : ℝ)) ≤
        Real.rpow A (-2 : ℝ) :=
    rpow_decay_le_log_scale_two
      (β := VarianceBoundGoodScale.section54VarianceBeta hP4) (C := C)
      (ξ := (hP4.xi : ℝ)) (δ := delta) (T := T) (m := m)
      (VarianceBoundGoodScale.section54VarianceBeta_pos hP4) hxi_one
      hdelta_pos hT_nonneg
      ((oneStepScaleSeparationConst_ge_section54 hP4).trans hC)
      (by simpa [T, A, mul_assoc] using hm)
  have hA_ge_one : 1 ≤ A := by
    have hprod : 0 ≤ delta⁻¹ * (hP4.xi : ℝ) * T :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hdelta_pos.le) (by linarith)) hT_nonneg
    dsimp [A]
    linarith
  have hT_le : T ≤ delta * A := by
    simpa [A, mul_assoc] using
      le_delta_mul_log_scale_argument hdelta_pos hxi_one hT_nonneg
  exact
    (mul_le_mul_of_nonneg_right hdecay (sq_nonneg T)).trans
      (by
        simpa [T, A] using
          rpow_neg_two_mul_sq_le_sqrt_delta hdelta_pos hdelta_le_half
            hA_ge_one hT_nonneg hT_le)

/-- The same logarithmic scale separation absorbs the Section 5.3-beta tail
that appears in the final coarse-fluctuation RHS. -/
theorem oneStepScaleSeparation_absorbs_section53Beta_widetildeThetaSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (hm :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ)
        (-(Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4) *
          (m : ℝ)) *
        (widetildeThetaAtScale P (0 : ℤ) hP4) ^ (2 : ℕ) ≤
      Real.sqrt delta := by
  let T : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let A : ℝ := 2 + delta⁻¹ * (hP4.xi : ℝ) * T
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using widetildeThetaAtScale_zero_nonneg hP4
  have hxi_one : 1 ≤ (hP4.xi : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hP4.xi_pos)
  have hdecay :
      Real.rpow (3 : ℝ)
          (-(Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4) *
            (m : ℝ)) ≤
        Real.rpow A (-2 : ℝ) :=
    rpow_decay_le_log_scale_two
      (β := Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4)
      (C := C) (ξ := (hP4.xi : ℝ)) (δ := delta) (T := T) (m := m)
      (section53CoarseFluctuationBeta_pos hP4) hxi_one
      hdelta_pos hT_nonneg (by simpa [oneStepScaleSeparationConst] using hC)
      (by simpa [T, A, mul_assoc] using hm)
  have hA_ge_one : 1 ≤ A := by
    have hprod : 0 ≤ delta⁻¹ * (hP4.xi : ℝ) * T :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hdelta_pos.le) (by linarith)) hT_nonneg
    dsimp [A]
    linarith
  have hT_le : T ≤ delta * A := by
    simpa [A, mul_assoc] using
      le_delta_mul_log_scale_argument hdelta_pos hxi_one hT_nonneg
  exact
    (mul_le_mul_of_nonneg_right hdecay (sq_nonneg T)).trans
      (by
        simpa [T, A] using
          rpow_neg_two_mul_sq_le_sqrt_delta hdelta_pos hdelta_le_half
            hA_ge_one hT_nonneg hT_le)

/-- The same logarithmic scale separation absorbs both
`3^{-βm} widetildeTheta_0` and
`3^{-βm} widetildeTheta_0^2` for the Section 5.3 beta. -/
theorem oneStepScaleSeparation_absorbs_section53Beta_widetildeThetaBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : oneStepScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (hm :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ)
        (-(Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4) *
          (m : ℝ)) *
        (widetildeThetaAtScale P (0 : ℤ) hP4 +
          (widetildeThetaAtScale P (0 : ℤ) hP4) ^ (2 : ℕ)) ≤
      2 * Real.sqrt delta := by
  let T : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let A : ℝ := 2 + delta⁻¹ * (hP4.xi : ℝ) * T
  let D : ℝ :=
    Real.rpow (3 : ℝ)
      (-(Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4) *
        (m : ℝ))
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using widetildeThetaAtScale_zero_nonneg hP4
  have hxi_one : 1 ≤ (hP4.xi : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hP4.xi_pos)
  have hdecay : D ≤ Real.rpow A (-2 : ℝ) :=
    rpow_decay_le_log_scale_two
      (β := Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4)
      (C := C) (ξ := (hP4.xi : ℝ)) (δ := delta) (T := T) (m := m)
      (section53CoarseFluctuationBeta_pos hP4) hxi_one
      hdelta_pos hT_nonneg (by simpa [oneStepScaleSeparationConst] using hC)
      (by simpa [T, A, mul_assoc] using hm)
  have hA_ge_one : 1 ≤ A := by
    have hprod : 0 ≤ delta⁻¹ * (hP4.xi : ℝ) * T :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hdelta_pos.le) (by linarith)) hT_nonneg
    dsimp [A]
    linarith
  have hT_le : T ≤ delta * A := by
    simpa [A, mul_assoc] using
      le_delta_mul_log_scale_argument hdelta_pos hxi_one hT_nonneg
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hlinear :
      D * T ≤ Real.sqrt delta := by
    exact
      (mul_le_mul_of_nonneg_right hdecay hT_nonneg).trans
        (by
          simpa [T, A] using
            rpow_neg_two_mul_self_le_sqrt_delta hdelta_pos hdelta_le_half
              hA_ge_one hT_nonneg hT_le)
  have hsquare :
      D * T ^ (2 : ℕ) ≤ Real.sqrt delta := by
    exact
      (mul_le_mul_of_nonneg_right hdecay (sq_nonneg T)).trans
        (by
          simpa [T, A] using
            rpow_neg_two_mul_sq_le_sqrt_delta hdelta_pos hdelta_le_half
              hA_ge_one hT_nonneg hT_le)
  calc
    D * (T + T ^ (2 : ℕ)) = D * T + D * T ^ (2 : ℕ) := by ring
    _ ≤ Real.sqrt delta + Real.sqrt delta := add_le_add hlinear hsquare
    _ = 2 * Real.sqrt delta := by ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
