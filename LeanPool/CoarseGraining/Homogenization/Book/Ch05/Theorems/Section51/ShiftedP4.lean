/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.EntryScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.Final

/-! # Shifted P4 -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section51

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Shifted `(P4)` data for the main theorem

The Section 5.5 localization produces smallness for the `2β`-shifted moment
quantity.  Since the Lean value of `β` is chosen with enough slack, these
shifted exponents still define valid `(P4)` data.  This file packages that
renaming of exponents.
-/

private theorem section53CoarseFluctuationBetaCoreParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaCoreParams params := by
  have hgap : 0 < 1 - params.sUpper - params.sLower := by
    linarith [params.sum_lt_one]
  have hupper : 0 < params.sUpper := params.sUpper_pos
  have hlower : 0 < params.sLower := params.sLower_pos
  have hupper_gain : 0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sUpper]
  have hlower_gain : 0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCoreParams
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

theorem section53CoarseFluctuationBetaParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams
  nlinarith [section53CoarseFluctuationBetaCoreParams_pos params]

private theorem section53CoarseFluctuationBetaCoreParams_le_sum_gap {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    section53CoarseFluctuationBetaCoreParams params ≤
      1 - params.sUpper - params.sLower := by
  unfold section53CoarseFluctuationBetaCoreParams
  exact min_le_left _ _

private theorem twoBetaShiftedParams_sum_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (params.sUpper + 2 * section53CoarseFluctuationBetaParams params) +
        (params.sLower + 2 * section53CoarseFluctuationBetaParams params) < 1 := by
  have hcore_le := section53CoarseFluctuationBetaCoreParams_le_sum_gap params
  have hsum := params.sum_lt_one
  unfold section53CoarseFluctuationBetaParams
  nlinarith

private theorem twoBetaShiftedParams_sUpper_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    params.sUpper + 2 * section53CoarseFluctuationBetaParams params < 1 := by
  have hsum := twoBetaShiftedParams_sum_lt_one params
  have hlower_nonneg :
      0 ≤ params.sLower + 2 * section53CoarseFluctuationBetaParams params := by
    have hβ := (section53CoarseFluctuationBetaParams_pos params).le
    nlinarith [params.sLower_nonneg]
  nlinarith

private theorem twoBetaShiftedParams_sLower_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    params.sLower + 2 * section53CoarseFluctuationBetaParams params < 1 := by
  have hsum := twoBetaShiftedParams_sum_lt_one params
  have hupper_nonneg :
      0 ≤ params.sUpper + 2 * section53CoarseFluctuationBetaParams params := by
    have hβ := (section53CoarseFluctuationBetaParams_pos params).le
    nlinarith [params.sUpper_nonneg]
  nlinarith

/-- Parameter-only `(P4)` data with both exponents shifted by `2β`. -/
def twoBetaShiftedParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := params.sUpper + 2 * section53CoarseFluctuationBetaParams params
  sLower := params.sLower + 2 * section53CoarseFluctuationBetaParams params
  xi := params.xi
  two_le_dim := params.two_le_dim
  sUpper_nonneg := by
    have hβ := (section53CoarseFluctuationBetaParams_pos params).le
    nlinarith [params.sUpper_nonneg]
  sUpper_lt_one := twoBetaShiftedParams_sUpper_lt_one params
  sLower_nonneg := by
    have hβ := (section53CoarseFluctuationBetaParams_pos params).le
    nlinarith [params.sLower_nonneg]
  sLower_lt_one := twoBetaShiftedParams_sLower_lt_one params
  xi_gt_two_mul_dim := params.xi_gt_two_mul_dim
  sum_lt_one := twoBetaShiftedParams_sum_lt_one params
  dim_div_xi_lt_min := by
    rw [lt_min_iff]
    constructor
    · have hβ := (section53CoarseFluctuationBetaParams_pos params).le
      linarith [params.dim_div_xi_lt_sUpper]
    · have hβ := (section53CoarseFluctuationBetaParams_pos params).le
      linarith [params.dim_div_xi_lt_sLower]

/-- Law-specific `(P4)` data with both exponents shifted by `2β`. -/
def twoBetaShiftedP4 {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    QuantitativeCoarseGrainedEllipticity P where
  sUpper := hP4.sUpper + 2 * section53CoarseFluctuationBeta hP4
  sLower := hP4.sLower + 2 * section53CoarseFluctuationBeta hP4
  xi := hP4.xi
  two_le_dim := hP4.two_le_dim
  sUpper_nonneg := by
    have hβ := (section53CoarseFluctuationBeta_pos hP4).le
    nlinarith [hP4.sUpper_nonneg]
  sUpper_lt_one := by
    have h :=
      twoBetaShiftedParams_sUpper_lt_one hP4.params
    simpa [section53CoarseFluctuationBetaParams_eq_of_P4 hP4] using h
  sLower_nonneg := by
    have hβ := (section53CoarseFluctuationBeta_pos hP4).le
    nlinarith [hP4.sLower_nonneg]
  sLower_lt_one := by
    have h :=
      twoBetaShiftedParams_sLower_lt_one hP4.params
    simpa [section53CoarseFluctuationBetaParams_eq_of_P4 hP4] using h
  xi_gt_two_mul_dim := hP4.xi_gt_two_mul_dim
  sum_lt_one := by
    have h :=
      twoBetaShiftedParams_sum_lt_one hP4.params
    simpa [section53CoarseFluctuationBetaParams_eq_of_P4 hP4] using h
  dim_div_xi_lt_min := by
    rw [lt_min_iff]
    constructor
    · have hβ := (section53CoarseFluctuationBeta_pos hP4).le
      linarith [hP4.dim_div_xi_lt_sUpper]
    · have hβ := (section53CoarseFluctuationBeta_pos hP4).le
      linarith [hP4.dim_div_xi_lt_sLower]
  upper_moment_integrable :=
    Section55.upperTwoBetaFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 0
  lower_inv_moment_integrable :=
    Section55.lowerTwoBetaFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 0

@[simp]
theorem twoBetaShiftedP4_params {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (twoBetaShiftedP4 hP hStruct hP4).params =
      twoBetaShiftedParams hP4.params := rfl

theorem widetildeThetaAtScale_twoBetaShiftedP4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (n : ℤ) :
    widetildeThetaAtScale P n (twoBetaShiftedP4 hP hStruct hP4) =
      Section55.shiftedWidetildeThetaAtScale P n hP4
        (2 * section53CoarseFluctuationBeta hP4) := by
  rfl

theorem widetildeThetaAtScale_zero_scaleNormalized_twoBetaShiftedP4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k : ℕ) :
    widetildeThetaAtScale (Ch04.restrictionScaleNormalizedLaw k P) (0 : ℤ)
        (twoBetaShiftedP4 (hP.scaleNormalized k) (hStruct.scaleNormalized k)
          (hP4.scaleNormalized hP hStruct k)) =
      Section55.shiftedWidetildeThetaAtScale P (k : ℤ) hP4
        (2 * section53CoarseFluctuationBeta hP4) := by
  have hβ :
      section53CoarseFluctuationBeta (hP4.scaleNormalized hP hStruct k) =
        section53CoarseFluctuationBeta hP4 := rfl
  have hshift :=
    Section55.shiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw
      hP hStruct hP4
      (η := 2 * section53CoarseFluctuationBeta hP4)
      (by
        have hβpos := section53CoarseFluctuationBeta_pos hP4
        nlinarith [hP4.sUpper_pos])
      (by
        have hβpos := section53CoarseFluctuationBeta_pos hP4
        nlinarith [hP4.sLower_pos])
      k 0
  simpa [widetildeThetaAtScale_twoBetaShiftedP4, hβ] using! hshift

end

end Section51
end Ch05
end Book
end Homogenization
