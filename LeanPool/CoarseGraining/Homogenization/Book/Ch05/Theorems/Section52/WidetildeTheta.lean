/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.Coefficients

/-! # Widetilde Theta -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: WidetildeTheta

Widetilde-theta product consequences.
-/

/-- Product assembly for the Section 5.2 moment lemma, with the scalar
Minkowski decomposition and the unit-scale base comparisons proved from the
Chapter 4 law-facing surfaces.

The remaining analytic inputs are exactly the two positive-excess power
integrability facts; the quantitative bounds on those positive-excess roots are
the genuine partition-average fluctuation step. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products_of_integrable
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
    (m : ℕ)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) hP4.sUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) hP4.sLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P) :
    widetildeThetaAtScale P (m : ℤ) hP4 ≤
      thetaAtScale hP hStruct 0 +
        LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi
            hP hStruct *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi
            hP hStruct *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi
            hP hStruct *
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi
            hP hStruct := by
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
      Ch04.LambdaMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi ≤
        hP.barSigmaAtScale hStruct 0 +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi hP hStruct :=
    LambdaMomentAtScale_le_barSigma_zero_add_positiveExcessMomentAtScale
      hP hStruct (Nat.succ_le_of_lt hP4.xi_pos) hP4.sUpper_pos
      hBarSigma0_nonneg
      (hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (m : ℤ)) hP4.sUpper_pos)
      (hUpperPowInt m) hUpperExcessPowInt
  have hLower :
      Ch04.lambdaInvMomentAtScale P (m : ℤ) hP4.sLower hP4.xi ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi
            hP hStruct :=
    lambdaInvMomentAtScale_le_barSigmaStar_zero_inv_add_positiveExcessMomentAtScale
      hP hStruct (Nat.succ_le_of_lt hP4.xi_pos) hP4.sLower_pos
      hBarSigmaStar0_inv_nonneg
      (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (m : ℤ)) hP4.sLower_pos)
      (hLowerPowInt m) hLowerExcessPowInt
  simpa using
    widetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products
      hP hStruct hP4 (m : ℤ) hUpper hLower hUpper0 hLower0 hBarSigma0_nonneg

/-- The `widetildeTheta` consequence of the Section 5.2 moment lemma from
quantitative positive-excess estimates, with all scalar root decomposition and
unit-scale factor comparisons discharged from the Chapter 4 surfaces. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_integrable_positiveExcess_bounds
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
    (m : ℕ)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) hP4.sUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) hP4.sLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P)
    {coeffUpper coeffLower finalCoeff : ℝ}
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi
          hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi
          hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    widetildeThetaAtScale P (m : ℤ) hP4 ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  have hProduct :
      widetildeThetaAtScale P (m : ℤ) hP4 ≤
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi hP hStruct := by
    simpa using
      widetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products_of_integrable
        hP hStruct hP4 hBlock hUpperPowInt hLowerPowInt
        m hUpperExcessPowInt hLowerExcessPowInt
  have h :=
    widetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_positiveExcess_product_bound
      hP hStruct hP4 (m : ℤ) hProduct hCoeffUpper_nonneg hCoeffLower_nonneg
      hUpperExcess hLowerExcess
      hCoeff
  simpa using h

/-- The displayed Section 5.2 `widetildeTheta` estimate from the two
positive-excess estimates with their manuscript coefficients. The probabilistic
content is exactly the two positive-excess bounds supplied as hypotheses. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_section52_error_of_integrable_positiveExcess_bounds
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
    (m : ℕ)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) hP4.sUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) hP4.sLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P)
    {CUpper CLower CTheta : ℝ}
    (hCUpper_nonneg : 0 ≤ CUpper)
    (hCLower_nonneg : 0 ≤ CLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) hP4.sUpper hP4.xi
          hP hStruct ≤
        section52MomentBoundCoeff d hP4.xi CUpper hP4.sUpper m *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) hP4.sLower hP4.xi
          hP hStruct ≤
        section52MomentBoundCoeff d hP4.xi CLower hP4.sLower m *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCTheta :
      CUpper / (((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sUpper) +
          CLower / (((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sLower) +
          (CUpper / (((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sUpper)) *
            (CLower / (((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sLower)) ≤
        CTheta) :
    widetildeThetaAtScale P (m : ℤ) hP4 ≤
      thetaAtScale hP hStruct 0 +
        section52WidetildeThetaErrorCoeff d hP4.xi CTheta
          (min hP4.sUpper hP4.sLower) m *
          widetildeThetaAtScale P 0 hP4 := by
  have hUpperDenom := hP4.upperMomentDenom_pos
  have hLowerDenom := hP4.lowerMomentDenom_pos
  have hCoeff :
      section52MomentBoundCoeff d hP4.xi CUpper hP4.sUpper m +
          section52MomentBoundCoeff d hP4.xi CLower hP4.sLower m +
          section52MomentBoundCoeff d hP4.xi CUpper hP4.sUpper m *
            section52MomentBoundCoeff d hP4.xi CLower hP4.sLower m ≤
        section52WidetildeThetaErrorCoeff d hP4.xi CTheta
          (min hP4.sUpper hP4.sLower) m :=
    section52_coefficients_mixed_le_widetildeThetaErrorCoeff
      (d := d) (ξ := hP4.xi) (m := m)
      (CUpper := CUpper) (CLower := CLower) (CTheta := CTheta)
      (sUpper := hP4.sUpper) (sLower := hP4.sLower)
      (Nat.succ_le_of_lt hP4.xi_pos) hCUpper_nonneg hCLower_nonneg
      hP4.dim_div_xi_lt_sUpper hP4.dim_div_xi_lt_sLower
      hUpperDenom hLowerDenom hCTheta
  exact
    widetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_integrable_positiveExcess_bounds
      hP hStruct hP4 hBlock hUpperPowInt hLowerPowInt
      m hUpperExcessPowInt hLowerExcessPowInt
      (section52MomentBoundCoeff_nonneg hCUpper_nonneg hUpperDenom)
      (section52MomentBoundCoeff_nonneg hCLower_nonneg hLowerDenom)
      hUpperExcess hLowerExcess hCoeff

end

end Section52
end Ch05
end Book
end Homogenization
