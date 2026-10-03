/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.FinalAbsorption

/-! # Scale Absorption -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

noncomputable section

/-!
# Scale-separation absorption

This file contains the pure real estimate converting the manuscript scale
separation into the decay needed after the refined variance-budget summation.
-/

/-- A separation constant large enough to turn the logarithmic scale condition
into fourth-power decay of the scale-zero moment parameter. -/
noncomputable def varianceScaleSeparationConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  8 * (section54VarianceBeta hP4 * Real.log 3)⁻¹

private theorem rpow_decay_le_log_scale
    {β C ξ δ T : ℝ} {m : ℕ}
    (hβ : 0 < β) (hξ : 1 ≤ ξ)
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hC : 8 * (β * Real.log 3)⁻¹ ≤ C)
    (hm : C * ξ * Real.log (2 + δ⁻¹ * ξ * T) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ) (-β * (m : ℝ)) ≤
      Real.rpow (2 + δ⁻¹ * ξ * T) (-4 : ℝ) := by
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
      (4 * (β * Real.log 3)⁻¹) * Real.log A ≤ (m : ℝ) := by
    have hC4 : 4 * (β * Real.log 3)⁻¹ ≤ C * ξ := by
      have hstep1 : 4 * (β * Real.log 3)⁻¹ ≤
          8 * (β * Real.log 3)⁻¹ := by
        have hinv_nonneg : 0 ≤ (β * Real.log 3)⁻¹ := inv_nonneg.mpr hβlog.le
        nlinarith
      have hstep2 : 8 * (β * Real.log 3)⁻¹ ≤ C := hC
      have hC_nonneg : 0 ≤ C := le_trans (by positivity) hC
      have hC_le_Cξ : C ≤ C * ξ := by
        nlinarith
      exact hstep1.trans (hstep2.trans hC_le_Cξ)
    calc
      (4 * (β * Real.log 3)⁻¹) * Real.log A ≤
          (C * ξ) * Real.log A :=
        mul_le_mul_of_nonneg_right hC4 hlogA_nonneg
      _ = C * ξ * Real.log A := by ring
      _ ≤ (m : ℝ) := by simpa [A] using hm
  have hexp_le :
      Real.log (3 : ℝ) * (-β * (m : ℝ)) ≤ Real.log A * (-4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsep0 hβlog.le
    have hfour : β * Real.log (3 : ℝ) *
          ((4 * (β * Real.log 3)⁻¹) * Real.log A) =
        4 * Real.log A := by
      field_simp [hβlog.ne']
    have hmain : 4 * Real.log A ≤ β * Real.log (3 : ℝ) * (m : ℝ) := by
      nlinarith
    nlinarith
  calc
    Real.rpow (3 : ℝ) (-β * (m : ℝ)) =
        Real.exp (Real.log (3 : ℝ) * (-β * (m : ℝ))) := by
        simpa using
          (Real.rpow_def_of_pos (x := (3 : ℝ))
            (y := -β * (m : ℝ)) (by norm_num : 0 < (3 : ℝ)))
    _ ≤ Real.exp (Real.log A * (-4 : ℝ)) :=
        Real.exp_le_exp.mpr hexp_le
    _ = Real.rpow A (-4 : ℝ) := by
        simpa using
          (Real.rpow_def_of_pos (x := A) (y := (-4 : ℝ)) hA_pos).symm

private theorem rpow_neg_four_mul_add_sq_le_two_delta
    {δ A T : ℝ} (hδ_pos : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    (hA_ge_one : 1 ≤ A) (hT_nonneg : 0 ≤ T)
    (hT_le : T ≤ δ * A) :
    Real.rpow A (-4 : ℝ) * (T + T ^ (2 : ℕ)) ≤ 2 * δ := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hA_inv_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr hA_pos.le
  have hA_m4_le_m1 :
      Real.rpow A (-4 : ℝ) ≤ Real.rpow A (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA_ge_one (by norm_num)
  have hA_m4_le_m2 :
      Real.rpow A (-4 : ℝ) ≤ Real.rpow A (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA_ge_one (by norm_num)
  have hT_over_A : A⁻¹ * T ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left hT_le hA_inv_nonneg
    have hcancel : A⁻¹ * (δ * A) = δ := by
      field_simp [hA_pos.ne']
    rw [hcancel] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hA_m1 : Real.rpow A (-1 : ℝ) = A⁻¹ := by
    simpa using (Real.rpow_neg hA_pos.le (1 : ℝ))
  have hA_m2 : Real.rpow A (-2 : ℝ) = A⁻¹ ^ (2 : ℕ) := by
    calc
      Real.rpow A (-2 : ℝ) = (Real.rpow A (2 : ℝ))⁻¹ := by
        simp
      _ = (A ^ (2 : ℕ))⁻¹ := by
        exact congrArg Inv.inv (Real.rpow_natCast A 2)
      _ = A⁻¹ ^ (2 : ℕ) := by
        field_simp [hA_pos.ne']
  have hlinear : Real.rpow A (-4 : ℝ) * T ≤ δ := by
    calc
      Real.rpow A (-4 : ℝ) * T ≤ Real.rpow A (-1 : ℝ) * T :=
        mul_le_mul_of_nonneg_right hA_m4_le_m1 hT_nonneg
      _ = A⁻¹ * T := by
        rw [hA_m1]
      _ ≤ δ := hT_over_A
  have hsquare : Real.rpow A (-4 : ℝ) * T ^ (2 : ℕ) ≤ δ := by
    have hT_over_A_sq : (A⁻¹ * T) ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) :=
      pow_le_pow_left₀ (mul_nonneg hA_inv_nonneg hT_nonneg) hT_over_A 2
    have hδ_sq_le : δ ^ (2 : ℕ) ≤ δ := by nlinarith
    calc
      Real.rpow A (-4 : ℝ) * T ^ (2 : ℕ) ≤
          Real.rpow A (-2 : ℝ) * T ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hA_m4_le_m2 (sq_nonneg T)
      _ = (A⁻¹ * T) ^ (2 : ℕ) := by
        rw [hA_m2]
        ring
      _ ≤ δ ^ (2 : ℕ) := hT_over_A_sq
      _ ≤ δ := hδ_sq_le
  nlinarith

/-- Scale separation absorbs the remaining `\widetilde\Theta_0` budget. -/
theorem scaleSeparation_absorbs_widetildeThetaBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C delta : ℝ} {m : ℕ}
    (hC : varianceScaleSeparationConst hP4 ≤ C)
    (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2)
    (hm :
      C * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ)) :
    Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) *
        (widetildeThetaAtScale P 0 hP4 +
          (widetildeThetaAtScale P 0 hP4) ^ (2 : ℕ)) ≤
      2 * delta := by
  let T : ℝ := widetildeThetaAtScale P 0 hP4
  let A : ℝ := 2 + delta⁻¹ * (hP4.xi : ℝ) * T
  have hT_nonneg : 0 ≤ T := by
    simp [T, Ch04.widetildeThetaAtScale]
    exact mul_nonneg
      (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
      (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)
  have hxi_one : 1 ≤ (hP4.xi : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hP4.xi_pos)
  have hdecay :=
    rpow_decay_le_log_scale
      (β := section54VarianceBeta hP4) (C := C) (ξ := (hP4.xi : ℝ))
      (δ := delta) (T := T) (m := m)
      (section54VarianceBeta_pos hP4) hxi_one hdelta_pos hT_nonneg
      (by simpa [varianceScaleSeparationConst] using hC)
      (by simpa [T, A, mul_assoc] using hm)
  have hA_ge_one : 1 ≤ A := by
    have hprod : 0 ≤ delta⁻¹ * (hP4.xi : ℝ) * T :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hdelta_pos.le) (by linarith)) hT_nonneg
    dsimp [A]
    linarith
  have hT_le : T ≤ delta * A := by
    have hcore : delta⁻¹ * T ≤ A := by
      have hxiT : delta⁻¹ * T ≤ delta⁻¹ * (hP4.xi : ℝ) * T := by
        have hδinv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta_pos.le
        have hxi_mul : T ≤ (hP4.xi : ℝ) * T := by nlinarith
        nlinarith
      dsimp [A]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcore hdelta_pos.le
    have hcancel : delta * (delta⁻¹ * T) = T := by
      field_simp [hdelta_pos.ne']
    rw [hcancel] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact
    (mul_le_mul_of_nonneg_right hdecay
      (add_nonneg hT_nonneg (sq_nonneg T))).trans
      (by
        simpa [T, A] using
          rpow_neg_four_mul_add_sq_le_two_delta hdelta_pos hdelta_le_half
            hA_ge_one hT_nonneg hT_le)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
