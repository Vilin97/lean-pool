/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.DilatedP4
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.MomentBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.WidetildeTheta
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.EllipticityMoments

/-! # Shifted Widetilde Theta -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open MeasureTheory
open Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Section 5.5 shifted `widetildeTheta`

This file begins the Lean proof of the shifted localization estimate in
Section 5.5.  The key point is that the decaying Section 5.2 input is used at
the shifted exponents `s_1 + beta` and `s_2 + beta`; these exponents are not
fed back into `(P4)` at the next iteration step.
-/

/-- The beta-decay factor at a natural scale gap is at most one. -/
theorem rpow_three_neg_beta_nat_le_one {β : ℝ} (hβ : 0 ≤ β)
    (m : ℕ) :
    Real.rpow (3 : ℝ) (-β * (m : ℝ)) ≤ 1 := by
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  nlinarith

/-- The shifted high-moment quantity in Section 5.5. -/
noncomputable def shiftedWidetildeThetaAtScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (η : ℝ) : ℝ :=
  Ch04.widetildeThetaAtScale P n (hP4.sUpper + η) (hP4.sLower + η) hP4.xi

/-- The beta-specialized shifted high-moment quantity used internally in
Section 5.5. -/
noncomputable def betaShiftedWidetildeThetaAtScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  shiftedWidetildeThetaAtScale P n hP4 (section53CoarseFluctuationBeta hP4)

private theorem sUpper_add_beta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 := by
  exact add_pos hP4.sUpper_pos (section53CoarseFluctuationBeta_pos hP4)

private theorem sLower_add_beta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sLower + section53CoarseFluctuationBeta hP4 := by
  exact add_pos hP4.sLower_pos (section53CoarseFluctuationBeta_pos hP4)

private theorem sUpper_add_beta_lt_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sUpper + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hlower_pos := sLower_add_beta_pos hP4
  nlinarith

private theorem sLower_add_beta_lt_one {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.sLower + section53CoarseFluctuationBeta hP4 < 1 := by
  have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
  have hupper_pos := sUpper_add_beta_pos hP4
  nlinarith

theorem section52TwoExponentMomentBoundCoeff_nonneg
    {d ξ m : ℕ} {C s r : ℝ}
    (hC_nonneg : 0 ≤ C) (hs_pos : 0 < s) (hr_lt_one : r < 1)
    (hd : 2 ≤ d) :
    0 ≤ section52TwoExponentMomentBoundCoeff d ξ C s r m := by
  have hden :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r := by
    have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hxi_nonneg : (0 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast Nat.zero_le ξ
    have hdiv_nonneg : 0 ≤ (d : ℝ) / (ξ : ℝ) := div_nonneg hd_nonneg hxi_nonneg
    nlinarith
  have hloss_nonneg : 0 ≤ section52MomentLossCoeff d ξ s r := by
    unfold section52MomentLossCoeff
    have hxi_nonneg : (0 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast Nat.zero_le ξ
    have hquot_nonneg :
        0 ≤ (ξ : ℝ) / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r) :=
      div_nonneg hxi_nonneg hden.le
    positivity
  unfold section52TwoExponentMomentBoundCoeff
  exact mul_nonneg (mul_nonneg hC_nonneg hloss_nonneg)
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)

/-- The shifted high-moment quantity is compatible with Ch4 scale
normalization. -/
theorem betaShiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k m : ℕ) :
    betaShiftedWidetildeThetaAtScale (Ch04.restrictionScaleNormalizedLaw k P) (m : ℤ)
        (hP4.scaleNormalized hP hStruct k) =
      betaShiftedWidetildeThetaAtScale P ((k + m : ℕ) : ℤ) hP4 := by
  have hβ :
      section53CoarseFluctuationBeta (hP4.scaleNormalized hP hStruct k) =
        section53CoarseFluctuationBeta hP4 := rfl
  have h :=
    Ch04.widetildeThetaAtScale_restrictionScaleNormalizedLaw hP k m
      (sUpper_add_beta_pos hP4) (sLower_add_beta_pos hP4) hP4.xi
  simpa [betaShiftedWidetildeThetaAtScale, hβ,
    QuantitativeCoarseGrainedEllipticity.scaleNormalized] using! h

/-- Scale normalization sends scale `0` to the original scale `k` for the
unshifted manuscript `widetildeTheta`. -/
theorem widetildeThetaAtScale_zero_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k : ℕ) :
    widetildeThetaAtScale (Ch04.restrictionScaleNormalizedLaw k P) (0 : ℤ)
        (hP4.scaleNormalized hP hStruct k) =
      widetildeThetaAtScale P (k : ℤ) hP4 := by
  have h :=
    Ch04.widetildeThetaAtScale_restrictionScaleNormalizedLaw hP k 0
      hP4.sUpper_pos hP4.sLower_pos hP4.xi
  simpa [widetildeThetaAtScale,
    QuantitativeCoarseGrainedEllipticity.scaleNormalized] using h

/-- Scale normalization sends scale `0` to the original scale `k` for the
structural scalar contrast. -/
theorem thetaAtScale_zero_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (k : ℕ) :
    (hP.scaleNormalized k).thetaAtScale (hStruct.scaleNormalized k) (0 : ℤ) =
      hP.thetaAtScale hStruct (k : ℤ) := by
  simpa using hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct k 0

/-- Dilation rewrite for the shifted quantity on a window `[k,n]`. -/
theorem betaShiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k n : ℕ} (hkn : k ≤ n) :
    betaShiftedWidetildeThetaAtScale (Ch04.restrictionScaleNormalizedLaw k P)
        ((n - k : ℕ) : ℤ) (hP4.scaleNormalized hP hStruct k) =
      betaShiftedWidetildeThetaAtScale P (n : ℤ) hP4 := by
  simpa [Nat.add_sub_of_le hkn] using
    betaShiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw
      hP hStruct hP4 k (n - k)

private theorem annealedMomentRoot_le_const_add_of_nonneg_le_of_error_pow_integrable
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X E : RegCoeffField d → ℝ} {A : ℝ}
    (hξ : 1 ≤ ξ) (hA_nonneg : 0 ≤ A)
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hE_nonneg : ∀ a, 0 ≤ E a)
    (hX_le : ∀ a, X a ≤ A + E a)
    (hX_meas : AEMeasurable X P)
    (hE_meas : AEMeasurable E P)
    (hE_pow_int : Integrable (fun a => E a ^ ξ) P) :
    Ch04.annealedMomentRoot P ξ X ≤
      A + Ch04.annealedMomentRoot P ξ E := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hE_abs_pow_int : Integrable (fun a => |E a| ^ ξ) P := by
    refine hE_pow_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hE_nonneg a)]
  have hE_mem : MemLp E (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hE_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hE_abs_pow_int
  have hY_mem : MemLp (fun a => A + E a) (ξ : ENNReal) P :=
    (memLp_const A).add hE_mem
  have hY_abs_pow_int : Integrable (fun a => |A + E a| ^ ξ) P := by
    simpa [Real.norm_eq_abs] using hY_mem.integrable_norm_pow hξ_ne
  have hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P := by
    refine Integrable.mono' hY_abs_pow_int
      (hX_meas.norm.pow_const ξ).aestronglyMeasurable ?_
    filter_upwards with a
    have hY_nonneg : 0 ≤ A + E a := add_nonneg hA_nonneg (hE_nonneg a)
    have hpow : |X a| ^ ξ ≤ |A + E a| ^ ξ := by
      have habs : |X a| ≤ |A + E a| := by
        simpa [abs_of_nonneg (hX_nonneg a), abs_of_nonneg hY_nonneg] using hX_le a
      exact pow_le_pow_left₀ (abs_nonneg (X a)) habs ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (X a)) ξ),
      abs_of_nonneg (pow_nonneg (abs_nonneg (A + E a)) ξ)] using hpow
  exact
    Ch04.annealedMomentRoot_le_const_add_of_nonneg_le
      (P := P) (ξ := ξ) (X := X) (E := E) (A := A)
      hξ hA_nonneg hX_nonneg hE_nonneg hX_le
      hX_meas hE_meas hX_abs_pow_int hE_abs_pow_int

private theorem LambdaMomentAtScale_le_barSigma_zero_add_positiveExcessMomentAtScale_of_excess_pow_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m : ℤ} {s : ℝ} {ξ : ℕ}
    (hξ : 1 ≤ ξ) (hs : 0 < s)
    (hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0)
    (hExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ ξ) P) :
    Ch04.LambdaMomentAtScale P m s ξ ≤
      hP.barSigmaAtScale hStruct 0 +
        LambdaPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a
  let E : RegCoeffField d → ℝ :=
    fun a => max (X a - hP.barSigmaAtScale hStruct 0) 0
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d m) hs
  have hE_meas : AEMeasurable E P := by
    exact (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ ξ) P := by
    simpa [E, X] using hExcessPowInt
  simpa [Ch04.LambdaMomentAtScale, LambdaPositiveExcessMomentAtScale, X, E] using
    annealedMomentRoot_le_const_add_of_nonneg_le_of_error_pow_integrable
      (P := P) (ξ := ξ) (X := X) (E := E)
      (A := hP.barSigmaAtScale hStruct 0)
      hξ hBarSigma0_nonneg
      (fun a =>
        Ch04.LambdaSqCoeffField_finite_nonneg (originCube d m) a hs
          (by norm_num : (1 : ℝ) ≤ 1))
      (fun a => le_max_right (X a - hP.barSigmaAtScale hStruct 0) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) (hP.barSigmaAtScale hStruct 0))
      hX_meas hE_meas hE_pow_int

private theorem lambdaInvMomentAtScale_le_barSigmaStar_zero_inv_add_positiveExcessMomentAtScale_of_excess_pow_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m : ℤ} {s : ℝ} {ξ : ℕ}
    (hξ : 1 ≤ ξ) (hs : 0 < s)
    (hBarSigmaStar0_inv_nonneg : 0 ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹)
    (hExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ ξ) P) :
    Ch04.lambdaInvMomentAtScale P m s ξ ≤
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
        lambdaInvPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹
  let E : RegCoeffField d → ℝ :=
    fun a => max (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d m) hs
  have hE_meas : AEMeasurable E P := by
    exact (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hE_pow_int : Integrable (fun a => E a ^ ξ) P := by
    simpa [E, X] using hExcessPowInt
  simpa [Ch04.lambdaInvMomentAtScale, lambdaInvPositiveExcessMomentAtScale, X, E] using
    annealedMomentRoot_le_const_add_of_nonneg_le_of_error_pow_integrable
      (P := P) (ξ := ξ) (X := X) (E := E)
      (A := (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      hξ hBarSigmaStar0_inv_nonneg
      (fun a =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d m) a hs
            (by norm_num : (1 : ℝ) ≤ 1)))
      (fun a => le_max_right (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0)
      (fun a =>
        Section52.real_le_base_add_max_sub_base_zero
          (X a) ((hP.barSigmaStarAtScale hStruct 0)⁻¹))
      hX_meas hE_meas hE_pow_int

private theorem shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℤ} {rUpper rLower : ℝ}
    (hrUpper_pos : 0 < rUpper) (hrLower_pos : 0 < rLower)
    (hUpper :
      Ch04.LambdaMomentAtScale P m rUpper hP4.xi ≤
        hP.barSigmaAtScale hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct)
    (hLower :
      Ch04.lambdaInvMomentAtScale P m rLower hP4.xi ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct)
    (hUpper0 :
      hP.barSigmaAtScale hStruct 0 ≤
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLower0 :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0) :
    Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi ≤
      thetaAtScale hP hStruct 0 +
        LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
        lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
          lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct := by
  let Lm := Ch04.LambdaMomentAtScale P m rUpper hP4.xi
  let lm := Ch04.lambdaInvMomentAtScale P m rLower hP4.xi
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let b0 := hP.barSigmaAtScale hStruct 0
  let s0 := (hP.barSigmaStarAtScale hStruct 0)⁻¹
  let UE := LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct
  let LE := lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct
  have hLm_nonneg : 0 ≤ Lm := by
    simpa [Lm] using Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hrUpper_pos
  have hlm_nonneg : 0 ≤ lm := by
    simpa [lm] using Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hrLower_pos
  have hUE_nonneg : 0 ≤ UE := by
    simpa [UE] using
      Section52.LambdaPositiveExcessMomentAtScale_nonneg
        rUpper hP4.xi hP hStruct m
  have hLE_nonneg : 0 ≤ LE := by
    simpa [LE] using
      Section52.lambdaInvPositiveExcessMomentAtScale_nonneg
        rLower hP4.xi hP hStruct m
  have hUpper' : Lm ≤ b0 + UE := by
    simpa [Lm, b0, UE] using hUpper
  have hLower' : lm ≤ s0 + LE := by
    simpa [lm, s0, LE] using hLower
  have hUpper0' : b0 ≤ L0 := by
    simpa [b0, L0] using hUpper0
  have hLower0' : s0 ≤ l0 := by
    simpa [s0, l0] using hLower0
  have hUpperRhs_nonneg : 0 ≤ b0 + UE := by
    exact add_nonneg (by simpa [b0] using hBarSigma0_nonneg) hUE_nonneg
  have hProd : Lm * lm ≤ (b0 + UE) * (s0 + LE) :=
    mul_le_mul hUpper' hLower' hlm_nonneg hUpperRhs_nonneg
  have hUEs0 : UE * s0 ≤ UE * l0 :=
    mul_le_mul_of_nonneg_left hLower0' hUE_nonneg
  have hLEb0 : LE * b0 ≤ LE * L0 :=
    mul_le_mul_of_nonneg_left hUpper0' hLE_nonneg
  have hExpand :
      (b0 + UE) * (s0 + LE) ≤ b0 * s0 + UE * l0 + LE * L0 + UE * LE := by
    nlinarith
  calc
    Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi = Lm * lm := by
      simp [Ch04.widetildeThetaAtScale, Lm, lm]
    _ ≤ (b0 + UE) * (s0 + LE) := hProd
    _ ≤ b0 * s0 + UE * l0 + LE * L0 + UE * LE := hExpand
    _ =
        thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := by
      simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, s0]
    _ =
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct := by
      simp [UE, LE, L0, l0]

private theorem shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products_of_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P)
    (hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ)) hP4.sUpper (.finite 1) a) ^
              hP4.xi) P)
    (hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
              hP4.xi) P)
    {rUpper rLower : ℝ} (hrUpper_pos : 0 < rUpper) (hrLower_pos : 0 < rLower)
    (m : ℕ)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) rUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P) :
    Ch04.widetildeThetaAtScale P (m : ℤ) rUpper rLower hP4.xi ≤
      thetaAtScale hP hStruct 0 +
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0 := by
    rw [hP.barSigmaAtScale_eq_barBAtScale hStruct (0 : ℤ)]
    simpa [Ch04.RestrictionLawCarrier.barBAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
        (hBlock 0)
  have hBarSigmaStar0_inv_nonneg :
      0 ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹ := by
    have hstar := hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (0 : ℤ)
    rw [hstar, inv_inv]
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      (Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
        (hBlock 0)).le
  have hUpper0 :
      hP.barSigmaAtScale hStruct 0 ≤
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
    exact
      hP.barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
        hStruct hP4.sUpper_pos hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
        hBlock
        (fun l => hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (l : ℤ)) hP4.sUpper_pos)
        (fun l => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (l : ℤ)) hP4.sLower_pos)
        hUpperPowInt hLowerPowInt 0
  have hLower0 :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
    exact
      hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
        hStruct hP4.sUpper_pos hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
        hBlock
        (fun l => hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (l : ℤ)) hP4.sUpper_pos)
        (fun l => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (l : ℤ)) hP4.sLower_pos)
        hUpperPowInt hLowerPowInt 0
  have hUpper :
      Ch04.LambdaMomentAtScale P (m : ℤ) rUpper hP4.xi ≤
        hP.barSigmaAtScale hStruct 0 +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct :=
    LambdaMomentAtScale_le_barSigma_zero_add_positiveExcessMomentAtScale_of_excess_pow_integrable
      hP hStruct (Nat.succ_le_of_lt hP4.xi_pos) hrUpper_pos
      hBarSigma0_nonneg hUpperExcessPowInt
  have hLower :
      Ch04.lambdaInvMomentAtScale P (m : ℤ) rLower hP4.xi ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi
            hP hStruct :=
    lambdaInvMomentAtScale_le_barSigmaStar_zero_inv_add_positiveExcessMomentAtScale_of_excess_pow_integrable
      hP hStruct (Nat.succ_le_of_lt hP4.xi_pos) hrLower_pos
      hBarSigmaStar0_inv_nonneg hLowerExcessPowInt
  exact
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products
      hP hStruct hP4 hrUpper_pos hrLower_pos hUpper hLower hUpper0 hLower0
      hBarSigma0_nonneg

private theorem shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_positiveExcess_bounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℤ} {rUpper rLower coeffUpper coeffLower finalCoeff : ℝ}
    (hProduct :
      Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi ≤
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct)
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (_hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let UE := LambdaPositiveExcessMomentAtScale P m rUpper hP4.xi hP hStruct
  let LE := lambdaInvPositiveExcessMomentAtScale P m rLower hP4.xi hP hStruct
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using
      Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using
      Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUE_nonneg : 0 ≤ UE := by
    simpa [UE] using
      Section52.LambdaPositiveExcessMomentAtScale_nonneg
        rUpper hP4.xi hP hStruct m
  have hLE_nonneg : 0 ≤ LE := by
    simpa [LE] using
      Section52.lambdaInvPositiveExcessMomentAtScale_nonneg
        rLower hP4.xi hP hStruct m
  have hBase_nonneg : 0 ≤ L0 * l0 := mul_nonneg hL0_nonneg hl0_nonneg
  have hProduct' :
      Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi ≤
        thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := by
    simpa [UE, LE, L0, l0] using hProduct
  have hUE_le : UE ≤ coeffUpper * L0 := by
    simpa [UE, L0] using hUpperExcess
  have hLE_le : LE ≤ coeffLower * l0 := by
    simpa [LE, l0] using hLowerExcess
  have hTermUpper : UE * l0 ≤ coeffUpper * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hUE_le hl0_nonneg
    nlinarith
  have hTermLower : LE * L0 ≤ coeffLower * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hLE_le hL0_nonneg
    nlinarith
  have hTermMixed : UE * LE ≤ coeffUpper * coeffLower * (L0 * l0) := by
    have hUpperRhs_nonneg : 0 ≤ coeffUpper * L0 :=
      mul_nonneg hCoeffUpper_nonneg hL0_nonneg
    have h := mul_le_mul hUE_le hLE_le hLE_nonneg hUpperRhs_nonneg
    nlinarith
  have hError :
      UE * l0 + LE * L0 + UE * LE ≤
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by
    nlinarith
  have hCoeffError :
      (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) ≤
        finalCoeff * (L0 * l0) :=
    mul_le_mul_of_nonneg_right hCoeff hBase_nonneg
  calc
    Ch04.widetildeThetaAtScale P m rUpper rLower hP4.xi
        ≤ thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := hProduct'
    _ = thetaAtScale hP hStruct 0 + (UE * l0 + LE * L0 + UE * LE) := by ring
    _ ≤ thetaAtScale hP hStruct 0 +
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by
      nlinarith
    _ ≤ thetaAtScale hP hStruct 0 + finalCoeff * (L0 * l0) := by
      nlinarith
    _ = thetaAtScale hP hStruct 0 + finalCoeff * widetildeThetaAtScale P 0 hP4 := by
      simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]

private theorem shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_integrable_positiveExcess_bounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P)
    (hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ)) hP4.sUpper (.finite 1) a) ^
              hP4.xi) P)
    (hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
              hP4.xi) P)
    {rUpper rLower : ℝ} (hrUpper_pos : 0 < rUpper) (hrLower_pos : 0 < rLower)
    (m : ℕ)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) rUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P)
    {coeffUpper coeffLower finalCoeff : ℝ}
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi
          hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi
          hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    Ch04.widetildeThetaAtScale P (m : ℤ) rUpper rLower hP4.xi ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  have hProduct :
      Ch04.widetildeThetaAtScale P (m : ℤ) rUpper rLower hP4.xi ≤
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct :=
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products_of_integrable
      hP hStruct hP4 hBlock hUpperPowInt hLowerPowInt
      hrUpper_pos hrLower_pos m hUpperExcessPowInt hLowerExcessPowInt
  exact
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_positiveExcess_bounds
      hP hStruct hP4 hProduct hCoeffUpper_nonneg hCoeffLower_nonneg
      hUpperExcess hLowerExcess hCoeff

theorem shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_P4_positiveExcess_bounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {rUpper rLower : ℝ}
    (hrUpper_gt : hP4.sUpper < rUpper) (hrUpper_lt_one : rUpper < 1)
    (hrLower_gt : hP4.sLower < rLower) (hrLower_lt_one : rLower < 1)
    (m : ℕ)
    {coeffUpper coeffLower finalCoeff : ℝ}
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi
          hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi
          hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    Ch04.widetildeThetaAtScale P (m : ℤ) rUpper rLower hP4.xi ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  have hrUpper_pos : 0 < rUpper := hP4.sUpper_pos.trans hrUpper_gt
  have hrLower_pos : 0 < rLower := hP4.sLower_pos.trans hrLower_gt
  exact
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_integrable_positiveExcess_bounds
      hP hStruct hP4
      (fun l => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l)
      (fun l => Section52.upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l)
      (fun l => Section52.lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l)
      hrUpper_pos hrLower_pos m
      (Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hrUpper_gt hrUpper_lt_one m)
      (Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hrLower_gt hrLower_lt_one m)
      hCoeffUpper_nonneg hCoeffLower_nonneg hUpperExcess hLowerExcess hCoeff

theorem betaShiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_section52TwoExponent_error
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ),
        betaShiftedWidetildeThetaAtScale P (m : ℤ) hP4 ≤
          thetaAtScale hP hStruct 0 +
            (section52TwoExponentMomentBoundCoeff d hP4.xi C
                hP4.sUpper
                (hP4.sUpper + section53CoarseFluctuationBeta hP4) m +
              section52TwoExponentMomentBoundCoeff d hP4.xi C
                hP4.sLower
                (hP4.sLower + section53CoarseFluctuationBeta hP4) m +
              section52TwoExponentMomentBoundCoeff d hP4.xi C
                hP4.sUpper
                (hP4.sUpper + section53CoarseFluctuationBeta hP4) m *
                section52TwoExponentMomentBoundCoeff d hP4.xi C
                  hP4.sLower
                  (hP4.sLower + section53CoarseFluctuationBeta hP4) m) *
              widetildeThetaAtScale P 0 hP4 := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    Section52.multiscaleEllipticityMomentBounds_homogenizationScale (d := d)
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 m
  let β := section53CoarseFluctuationBeta hP4
  let coeffUpper : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sUpper
      (hP4.sUpper + β) m
  let coeffLower : ℝ :=
    section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sLower
      (hP4.sLower + β) m
  have hBounds :=
    hC hP hStruct hP4
      (hP4.sUpper + β) (hP4.sLower + β) m
      (by simpa [β] using sUpper_lt_sUpper_add_beta hP4)
      (by simpa [β] using sUpper_add_beta_lt_one hP4)
      (by simpa [β] using sLower_lt_sLower_add_beta hP4)
      (by simpa [β] using sLower_add_beta_lt_one hP4)
  have hCoeffUpper_nonneg : 0 ≤ coeffUpper := by
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4.xi) (m := m) (C := C)
      (s := hP4.sUpper) (r := hP4.sUpper + β)
      hC_nonneg hP4.sUpper_pos (by simpa [β] using sUpper_add_beta_lt_one hP4)
      hP4.two_le_dim
  have hCoeffLower_nonneg : 0 ≤ coeffLower := by
    exact section52TwoExponentMomentBoundCoeff_nonneg
      (d := d) (ξ := hP4.xi) (m := m) (C := C)
      (s := hP4.sLower) (r := hP4.sLower + β)
      hC_nonneg hP4.sLower_pos (by simpa [β] using sLower_add_beta_lt_one hP4)
      hP4.two_le_dim
  have hShifted :=
    shiftedWidetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_P4_positiveExcess_bounds
      hP hStruct hP4
      (by simpa [β] using sUpper_lt_sUpper_add_beta hP4)
      (by simpa [β] using sUpper_add_beta_lt_one hP4)
      (by simpa [β] using sLower_lt_sLower_add_beta hP4)
      (by simpa [β] using sLower_add_beta_lt_one hP4)
      m hCoeffUpper_nonneg hCoeffLower_nonneg hBounds.1 hBounds.2
      (le_rfl :
        coeffUpper + coeffLower + coeffUpper * coeffLower ≤
          coeffUpper + coeffLower + coeffUpper * coeffLower)
  simpa [betaShiftedWidetildeThetaAtScale, β, coeffUpper, coeffLower] using! hShifted

theorem section52TwoExponentMomentBoundCoeff_upper_beta_shift_le_loss_beta_decay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} {C : ℝ}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (hC_nonneg : 0 ≤ C)
    (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sUpper
        (hP4.sUpper + β) m ≤
      (C * section52MomentLossCoeff d hP4.xi hP4.sUpper
          (hP4.sUpper + β)) *
        Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hdecay := shiftedUpperDecay_le_betaDecay hP4 m
  have hloss_nonneg :
      0 ≤ section52MomentLossCoeff d hP4.xi hP4.sUpper
        (hP4.sUpper + β) :=
    section52MomentLossCoeff_nonneg_at_shift hP4 hP4.sUpper_pos
      (by simpa [β] using sUpper_lt_sUpper_add_beta hP4)
      (by simpa [β] using sUpper_add_beta_lt_one hP4)
  have hpref_nonneg :
      0 ≤ C * section52MomentLossCoeff d hP4.xi hP4.sUpper
        (hP4.sUpper + β) :=
    mul_nonneg hC_nonneg hloss_nonneg
  simpa [section52TwoExponentMomentBoundCoeff, β, mul_assoc] using
    mul_le_mul_of_nonneg_left hdecay hpref_nonneg

theorem section52TwoExponentMomentBoundCoeff_lower_beta_shift_le_loss_beta_decay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} {C : ℝ}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (hC_nonneg : 0 ≤ C)
    (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sLower
        (hP4.sLower + β) m ≤
      (C * section52MomentLossCoeff d hP4.xi hP4.sLower
          (hP4.sLower + β)) *
        Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hdecay := shiftedLowerDecay_le_betaDecay hP4 m
  have hloss_nonneg :
      0 ≤ section52MomentLossCoeff d hP4.xi hP4.sLower
        (hP4.sLower + β) :=
    section52MomentLossCoeff_nonneg_at_shift hP4 hP4.sLower_pos
      (by simpa [β] using sLower_lt_sLower_add_beta hP4)
      (by simpa [β] using sLower_add_beta_lt_one hP4)
  have hpref_nonneg :
      0 ≤ C * section52MomentLossCoeff d hP4.xi hP4.sLower
        (hP4.sLower + β) :=
    mul_nonneg hC_nonneg hloss_nonneg
  simpa [section52TwoExponentMomentBoundCoeff, β, mul_assoc] using
    mul_le_mul_of_nonneg_left hdecay hpref_nonneg

end

end Section55
end Ch05
end Book
end Homogenization
