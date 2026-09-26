/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.RHSCompression

/-! # Assembly -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Assembly of the one-step contraction

This file combines the Section 5.3 centered-response estimate, the good-scale
RHS compression, and the centered-response identity to prove the public
Section 5.4 one-step contraction proposition.
-/

open Section53.JUpperBoundCoarseFluctuations

private def unitCoordinateVector {d : ℕ} [NeZero d] : Vec d :=
  Pi.single (0 : Fin d) 1

private theorem unitCoordinateVector_vecNormSq {d : ℕ} [NeZero d] :
    vecNormSq (unitCoordinateVector : Vec d) = 1 := by
  rw [unitCoordinateVector, vecNormSq, vecDot, Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem unitCoordinateVector_vecNorm {d : ℕ} [NeZero d] :
    Ch02.vecNorm (unitCoordinateVector : Vec d) = 1 := by
  have hsq :
      Ch02.vecNorm (unitCoordinateVector : Vec d) ^ (2 : ℕ) = 1 := by
    simpa [unitCoordinateVector_vecNormSq] using
      Ch02.vecNorm_sq_eq_vecNormSq (unitCoordinateVector : Vec d)
  have hnonneg :
      0 ≤ Ch02.vecNorm (unitCoordinateVector : Vec d) :=
    Ch02.vecNorm_nonneg _
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · linarith

/-- Parameter-only one-step scale-separation constant. -/
noncomputable def oneStepScaleSeparationConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  2 * (section53CoarseFluctuationBetaParams params * Real.log 3)⁻¹

/-- Parameter-only linear budget constant for Section 5.3-beta full-block
sums. -/
noncomputable def oneStepCoarsePairLinearBudgetConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  16 *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 params.xi *
        (geometricDiscount
          (VarianceBoundGoodScale.lpVarianceDecayParams d params -
            section53CoarseFluctuationBetaParams params) 1)⁻¹ +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 params.xi *
        (geometricDiscount
          (VarianceBoundGoodScale.sqrtVarianceDecay d -
            section53CoarseFluctuationBetaParams params) 1)⁻¹)

/-- Parameter-only refined budget constant for Section 5.3-beta full-block
sums. -/
noncomputable def oneStepWeightedRefinedBudgetConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (geometricDiscount (section53CoarseFluctuationBetaParams params) 1)⁻¹ +
    2 * oneStepCoarsePairLinearBudgetConstParams params +
      2 * VarianceBoundGoodScale.pairPointwiseBudgetConstParams params *
        oneStepCoarsePairLinearBudgetConstParams params

/-- Parameter-only full-block constant for the one-step RHS compression. -/
noncomputable def oneStepCoarseFullBlockConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  3 *
    (VarianceBoundGoodScale.refinedMatrixBudgetConst d *
      oneStepWeightedRefinedBudgetConstParams params)

/-- Parameter-only tau-sum constant for the one-step RHS compression. -/
noncomputable def oneStepCoarseTauSumConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  3 * (geometricDiscount (section53CoarseFluctuationBetaParams params) 1)⁻¹

/-- Parameter-only multiplier compressing the Section 5.3 manuscript RHS.  The
outer `max` gives a nonnegative witness without exposing any proof package. -/
noncomputable def oneStepCompressionMultiplierParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  max 0
    (3 +
      (section53CoarseFluctuationBetaParams params)⁻¹ *
          oneStepCoarseFullBlockConstParams params +
        (section53CoarseFluctuationBetaParams params ^ 2)⁻¹ *
            oneStepCoarseTauSumConstParams params +
          (params.xi : ℝ) *
              (section53CoarseFluctuationBetaParams params ^ 3)⁻¹ * 4 +
            (section53CoarseFluctuationBetaParams params ^ 2)⁻¹ * 3)

@[simp]
theorem oneStepScaleSeparationConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    oneStepScaleSeparationConstParams hP4.params =
      oneStepScaleSeparationConst hP4 := rfl

@[simp]
theorem oneStepCoarsePairLinearBudgetConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    oneStepCoarsePairLinearBudgetConstParams hP4.params =
      oneStepCoarsePairLinearBudgetConst hP4 := rfl

@[simp]
theorem oneStepWeightedRefinedBudgetConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    oneStepWeightedRefinedBudgetConstParams hP4.params =
      oneStepWeightedRefinedBudgetConst hP4 := rfl

@[simp]
theorem oneStepCoarseFullBlockConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    oneStepCoarseFullBlockConstParams hP4.params =
      oneStepCoarseFullBlockConst hP4 := rfl

@[simp]
theorem oneStepCoarseTauSumConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    oneStepCoarseTauSumConstParams hP4.params =
      oneStepCoarseTauSumConst hP4 := rfl

private theorem oneStepCompressionMultiplierParams_nonneg {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 ≤ oneStepCompressionMultiplierParams params := by
  unfold oneStepCompressionMultiplierParams
  exact le_max_left _ _

/-- Compressed form of the Section 5.3 input at a good scale. -/
theorem exists_expectedCenteredResponseJAtScale_special_le_compressed
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {Csep delta epsilon : ℝ} {m : ℕ},
        oneStepScaleSeparationConstParams params ≤ Csep →
        0 < delta → delta ≤ 1 / 2 →
        Csep * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ) →
        0 < epsilon → epsilon ≤ 1 →
        hP.barSigmaAtScale hStruct 0 ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ) →
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
          (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ →
        ∀ e : Vec d, Ch02.vecNorm e = 1 →
          expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
            (specialPAtScale hP hStruct (m : ℤ) e)
            (specialQAtScale hP hStruct (m : ℤ) e) ≤
          K * ((epsilon + epsilon⁻¹ * Real.sqrt delta) *
            thetaAtScale hP hStruct (0 : ℤ)) := by
  rcases
    exists_expectedCenteredResponseJAtScale_special_le_coarseFluctuationRHS_zero_uniform
      params with
    ⟨C0, hC0_nonneg, hC0⟩
  let Mparams : ℝ := oneStepCompressionMultiplierParams params
  refine ⟨C0 * Mparams,
    mul_nonneg hC0_nonneg (oneStepCompressionMultiplierParams_nonneg params), ?_⟩
  intro P hP hStruct hP4 hparams Csep delta epsilon m hCsep hdelta_pos hdelta_le hsep
      hepsilon_pos hepsilon_le hgood_upper hgood_lower e he
  subst params
  let M : ℝ :=
    3 +
      (section53CoarseFluctuationBeta hP4)⁻¹ *
          oneStepCoarseFullBlockConst hP4 +
        (section53CoarseFluctuationBeta hP4 ^ 2)⁻¹ *
            oneStepCoarseTauSumConst hP4 +
          (hP4.xi : ℝ) *
              (section53CoarseFluctuationBeta hP4 ^ 3)⁻¹ * 4 +
            (section53CoarseFluctuationBeta hP4 ^ 2)⁻¹ * 3
  have hCsep_law : oneStepScaleSeparationConst hP4 ≤ Csep := by
    simpa using hCsep
  have hsep_law :
      Csep * (hP4.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (hP4.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ) := by
    simpa using hsep
  have hm_pos :
      0 < m :=
    oneStepScaleSeparation_m_pos hP4 hCsep_law hdelta_pos hsep_law
  have hJ :=
    hC0 hP hStruct hP4 rfl hm_pos e he hepsilon_pos hepsilon_le
  have hRHS :=
    coarseFluctuationManuscriptRHSAtScale_zero_le_compressed
      hP hStruct hP4 hC0_nonneg hCsep_law hdelta_pos hdelta_le hsep_law
      hepsilon_pos hepsilon_le hgood_upper hgood_lower e he
      (C0 := C0) (Csep := Csep)
  have hM_le : M ≤ Mparams := by
    dsimp [Mparams, oneStepCompressionMultiplierParams]
    simp [M]
  have hθ0_nonneg :
      0 ≤ thetaAtScale hP hStruct (0 : ℤ) :=
    le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hterm_nonneg :
      0 ≤ (epsilon + epsilon⁻¹ * Real.sqrt delta) *
        thetaAtScale hP hStruct (0 : ℤ) := by
    have hsum_nonneg :
        0 ≤ epsilon + epsilon⁻¹ * Real.sqrt delta := by
      exact add_nonneg hepsilon_pos.le
        (mul_nonneg (inv_nonneg.mpr hepsilon_pos.le) (Real.sqrt_nonneg delta))
    exact mul_nonneg hsum_nonneg hθ0_nonneg
  calc
    expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
        (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e) ≤
      C0 * M * ((epsilon + epsilon⁻¹ * Real.sqrt delta) *
        thetaAtScale hP hStruct (0 : ℤ)) :=
        hJ.trans (by simpa [M] using hRHS)
    _ ≤ C0 * Mparams * ((epsilon + epsilon⁻¹ * Real.sqrt delta) *
        thetaAtScale hP hStruct (0 : ℤ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM_le hC0_nonneg) hterm_nonneg

/-- Proposition `p.one.step.contraction.homogenization.scale` from the
manuscript. -/
theorem oneStepContraction_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta : ℝ}, 0 < delta → delta ≤ 1 / 2 →
      ∀ {m : ℕ},
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (m : ℝ) →
        hP.barSigmaAtScale hStruct 0 ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ) →
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
          (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ →
        thetaAtScale hP hStruct (m : ℤ) ≤
          1 + C * Real.rpow delta (1 / 4 : ℝ) *
            thetaAtScale hP hStruct 0 := by
  rcases
    exists_expectedCenteredResponseJAtScale_special_le_compressed
      params with
    ⟨K, hK_nonneg, hK⟩
  let C : ℝ := max (oneStepScaleSeparationConstParams params) (max (4 * K) 1)
  have hC_pos : 0 < C := by
    have hle : (1 : ℝ) ≤ C := by
      dsimp [C]
      exact le_trans (le_max_right (4 * K) 1)
        (le_max_right (oneStepScaleSeparationConstParams params) (max (4 * K) 1))
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams delta hdelta_pos hdelta_le m hsep hgood_upper hgood_lower
  subst params
  let ε := oneStepContractionEpsilon delta
  let e : Vec d := unitCoordinateVector
  have he : Ch02.vecNorm e = 1 := by
    simpa [e] using (unitCoordinateVector_vecNorm (d := d))
  have hCsep : oneStepScaleSeparationConstParams hP4.params ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hK_le_C : 4 * K ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left (4 * K) 1)
      (le_max_right (oneStepScaleSeparationConst hP4) (max (4 * K) 1))
  have hε_pos : 0 < ε := by
    simpa [ε] using oneStepContractionEpsilon_pos hdelta_pos
  have hε_le : ε ≤ 1 := by
    simpa [ε] using oneStepContractionEpsilon_le_one hdelta_pos hdelta_le
  have hθ0_nonneg :
      0 ≤ thetaAtScale hP hStruct (0 : ℤ) :=
    le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hJ :=
    hK hP hStruct hP4 rfl hCsep hdelta_pos hdelta_le hsep hε_pos hε_le
      hgood_upper hgood_lower e he
  have hε_abs :
      ε + ε⁻¹ * Real.sqrt delta ≤ 2 * ε := by
    simpa [ε] using oneStepContractionEpsilon_add_inv_mul_sqrt_le hdelta_pos
  have htarget_le :
      (ε + ε⁻¹ * Real.sqrt delta) *
          thetaAtScale hP hStruct (0 : ℤ) ≤
        2 * ε * thetaAtScale hP hStruct (0 : ℤ) := by
    exact mul_le_mul_of_nonneg_right hε_abs hθ0_nonneg
  have hcenter :=
    thetaAtScale_sub_one_eq_two_centeredResponse_special
      hP hStruct hP4 m e he
  have hsub_le :
      thetaAtScale hP hStruct (m : ℤ) - 1 ≤
        C * ε * thetaAtScale hP hStruct (0 : ℤ) := by
    calc
      thetaAtScale hP hStruct (m : ℤ) - 1 =
          2 *
            expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
              (specialPAtScale hP hStruct (m : ℤ) e)
              (specialQAtScale hP hStruct (m : ℤ) e) := hcenter
      _ ≤ 2 * (K *
            ((ε + ε⁻¹ * Real.sqrt delta) *
              thetaAtScale hP hStruct (0 : ℤ))) :=
          mul_le_mul_of_nonneg_left hJ (by norm_num)
      _ ≤ 2 * (K * (2 * ε * thetaAtScale hP hStruct (0 : ℤ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htarget_le hK_nonneg) (by norm_num)
      _ = (4 * K) * ε * thetaAtScale hP hStruct (0 : ℤ) := by ring
      _ ≤ C * ε * thetaAtScale hP hStruct (0 : ℤ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hK_le_C hε_pos.le) hθ0_nonneg
  calc
    thetaAtScale hP hStruct (m : ℤ) =
        1 + (thetaAtScale hP hStruct (m : ℤ) - 1) := by ring
    _ ≤ 1 + C * ε * thetaAtScale hP hStruct (0 : ℤ) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hsub_le 1
    _ = 1 + C * Real.rpow delta (1 / 4 : ℝ) *
        thetaAtScale hP hStruct 0 := by
        simp [ε, oneStepContractionEpsilon]

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
