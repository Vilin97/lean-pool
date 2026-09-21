/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DilationLaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability

/-! # Dilated P4 -/

namespace Homogenization
namespace Book
namespace Ch05
namespace QuantitativeCoarseGrainedEllipticity

open MeasureTheory

noncomputable section

private theorem upperMomentIntegrable_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) hP4.sUpper (.finite 1) a) ^
          hP4.xi) (Ch04.restrictionScaleNormalizedLaw k P) := by
  let X : RegCoeffField d → ℝ := fun a =>
    (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) hP4.sUpper (.finite 1) a) ^
      hP4.xi
  have hX :
      AEStronglyMeasurable X (Ch04.restrictionScaleNormalizedLaw k P) := by
    simpa [X] using
      (((hP.scaleNormalized k).aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (0 : ℤ)) hP4.sUpper_pos).pow_const hP4.xi).aestronglyMeasurable
  rw [Ch04.integrable_restrictionScaleNormalizedLaw_iff k hX]
  have hbase := Section52.upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 k
  refine hbase.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  have hshift :=
    Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 hP4.sUpper (.finite 1)
  simpa [X] using (congrArg (fun z : ℝ => z ^ hP4.xi) hshift).symm

private theorem lowerInvMomentIntegrable_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
          hP4.xi) (Ch04.restrictionScaleNormalizedLaw k P) := by
  let X : RegCoeffField d → ℝ := fun a =>
    ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
      hP4.xi
  have hX :
      AEStronglyMeasurable X (Ch04.restrictionScaleNormalizedLaw k P) := by
    simpa [X] using
      (((hP.scaleNormalized k).aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (0 : ℤ)) hP4.sLower_pos).pow_const hP4.xi).aestronglyMeasurable
  rw [Ch04.integrable_restrictionScaleNormalizedLaw_iff k hX]
  have hbase := Section52.lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 k
  refine hbase.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  have hshift :=
    Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 hP4.sLower (.finite 1)
  simpa [X] using
    (congrArg (fun z : ℝ => z⁻¹ ^ hP4.xi) hshift).symm

/-- The Chapter 5 quantitative coarse-grained ellipticity hypothesis is stable
under Ch4 scale normalization.  The unit-scale moment assumptions for the
pushed law are exactly the arbitrary-scale moment consequences of `(P4)` for
the original law. -/
def scaleNormalized {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (k : ℕ) :
    QuantitativeCoarseGrainedEllipticity (Ch04.restrictionScaleNormalizedLaw k P) where
  sUpper := hP4.sUpper
  sLower := hP4.sLower
  xi := hP4.xi
  two_le_dim := hP4.two_le_dim
  sUpper_nonneg := hP4.sUpper_nonneg
  sUpper_lt_one := hP4.sUpper_lt_one
  sLower_nonneg := hP4.sLower_nonneg
  sLower_lt_one := hP4.sLower_lt_one
  xi_gt_two_mul_dim := hP4.xi_gt_two_mul_dim
  sum_lt_one := hP4.sum_lt_one
  dim_div_xi_lt_min := hP4.dim_div_xi_lt_min
  upper_moment_integrable :=
    upperMomentIntegrable_restrictionScaleNormalizedLaw hP hStruct hP4 k
  lower_inv_moment_integrable :=
    lowerInvMomentIntegrable_restrictionScaleNormalizedLaw hP hStruct hP4 k

end

end QuantitativeCoarseGrainedEllipticity
end Ch05
end Book
end Homogenization
