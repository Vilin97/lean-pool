/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ScaleErrors

/-! # Tau Sum -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open scoped BigOperators

noncomputable section

/-!
# Tau-sum absorption for the one-step contraction

The Section 5.3 coarse-fluctuation estimate contains a beta-weighted sum of
additivity defects multiplied by a scalar coefficient combination.  At a good
scale this term is `O(delta * Theta_0)`, hence also
`O(sqrt(delta) * Theta_0)` in the manuscript range.
-/

/-- The Section 5.4 beta-weighted additivity-defect sum used in the one-step
contraction proof. -/
noncomputable def oneStepTauSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) : ℝ :=
  let β := VarianceBoundGoodScale.section54VarianceBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  ∑ j ∈ Finset.Icc 1 m,
    VarianceBoundGoodScale.varianceWeight β m j *
      tauAtScale P (m : ℤ) (j : ℤ) p_e q_e

/-- The harmless geometric constant for the one-step tau-sum absorption. -/
noncomputable def oneStepTauSumConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  3 * (geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1)⁻¹

/-- The tau-sum constant is nonnegative. -/
theorem oneStepTauSumConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ oneStepTauSumConst hP4 := by
  unfold oneStepTauSumConst
  have hgeo :
      0 < geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1 :=
    geometricDiscount_pos
      (by simpa using VarianceBoundGoodScale.section54VarianceBeta_pos hP4)
  positivity

/-- The scalar weight multiplying the tau sum is nonnegative. -/
theorem oneStepScalarWeightAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ oneStepScalarWeightAtScale hP hStruct m := by
  have hσ : 0 < sigmaHatAtScale hP hStruct (m : ℤ) :=
    GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hb0 : 0 < hP.barSigmaAtScale hStruct 0 :=
    Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0 : 0 < hP.barSigmaStarAtScale hStruct 0 :=
    Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  dsimp [oneStepScalarWeightAtScale]
  positivity

/-- At a good scale, the weighted tau sum is bounded by the geometric tail
times `delta * sqrt(Theta_0)`. -/
theorem oneStepTauSumAtScale_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    oneStepTauSumAtScale hP hStruct hP4 m e ≤
      (geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1)⁻¹ *
        (delta * Real.sqrt (thetaAtScale hP hStruct 0)) := by
  let β := VarianceBoundGoodScale.section54VarianceBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let K := delta * Real.sqrt (thetaAtScale hP hStruct 0)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hdelta_pos.le (Real.sqrt_nonneg _)
  have hpoint :
      ∀ j, j ∈ Finset.Icc 1 m →
        tauAtScale P (m : ℤ) (j : ℤ) p_e q_e ≤ K := by
    intro j hj
    have hj_le : j ≤ m := (Finset.mem_Icc.mp hj).2
    simpa [p_e, q_e, K] using
      goodScale_tau_le hP hStruct hP4 hdelta_pos hdelta_le
        (m := m) (j := j) hj_le hgood_upper hgood_lower e he
  have hsum_const :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j *
          tauAtScale P (m : ℤ) (j : ℤ) p_e q_e) ≤
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j) * K :=
    VarianceBoundGoodScale.sum_Icc_varianceWeight_mul_le_const_mul
      (β := β) (C := K) (m := m)
      (f := fun j => tauAtScale P (m : ℤ) (j : ℤ) p_e q_e) hpoint
  have hweights :
      (∑ j ∈ Finset.Icc 1 m,
        VarianceBoundGoodScale.varianceWeight β m j) ≤
        (geometricDiscount β 1)⁻¹ :=
    VarianceBoundGoodScale.sum_Icc_varianceWeight_le_inv_geometricDiscount
      (by simpa [β] using VarianceBoundGoodScale.section54VarianceBeta_pos hP4) m
  calc
    oneStepTauSumAtScale hP hStruct hP4 m e =
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            tauAtScale P (m : ℤ) (j : ℤ) p_e q_e := by
          simp [oneStepTauSumAtScale, β, p_e, q_e]
    _ ≤
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j) * K :=
        hsum_const
    _ ≤ (geometricDiscount β 1)⁻¹ * K :=
        mul_le_mul_of_nonneg_right hweights hK_nonneg
    _ =
        (geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1)⁻¹ *
          (delta * Real.sqrt (thetaAtScale hP hStruct 0)) := by
        rfl

/-- At a good scale, the scalar-weighted tau sum is
`O(delta * Theta_0)`. -/
theorem oneStepScalarWeight_mul_tauSum_le_delta_theta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    oneStepScalarWeightAtScale hP hStruct m *
        oneStepTauSumAtScale hP hStruct hP4 m e ≤
      oneStepTauSumConst hP4 * delta * thetaAtScale hP hStruct 0 := by
  let θ0 := thetaAtScale hP hStruct 0
  let sqrtθ0 := Real.sqrt θ0
  let B := (geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1)⁻¹
  have hscalar_nonneg :
      0 ≤ oneStepScalarWeightAtScale hP hStruct m :=
    oneStepScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hscalar_le :
      oneStepScalarWeightAtScale hP hStruct m ≤ 3 * sqrtθ0 := by
    simpa [sqrtθ0] using!
      goodScale_oneStepScalarWeight_le hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
  have htau_le :
      oneStepTauSumAtScale hP hStruct hP4 m e ≤ B * (delta * sqrtθ0) := by
    simpa [B, sqrtθ0] using!
      oneStepTauSumAtScale_le hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hgeo :
        0 < geometricDiscount (VarianceBoundGoodScale.section54VarianceBeta hP4) 1 :=
      geometricDiscount_pos
        (by simpa using VarianceBoundGoodScale.section54VarianceBeta_pos hP4)
    positivity
  have htau_bound_nonneg : 0 ≤ B * (delta * sqrtθ0) := by
    exact mul_nonneg hB_nonneg
      (mul_nonneg hdelta_pos.le (by dsimp [sqrtθ0]; exact Real.sqrt_nonneg _))
  have hsqrt_nonneg : 0 ≤ sqrtθ0 := by
    dsimp [sqrtθ0]
    exact Real.sqrt_nonneg _
  have htheta_nonneg : 0 ≤ θ0 := by
    dsimp [θ0]
    exact le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hsqrt_sq : sqrtθ0 * sqrtθ0 = θ0 := by
    dsimp [sqrtθ0]
    exact Real.mul_self_sqrt htheta_nonneg
  calc
    oneStepScalarWeightAtScale hP hStruct m *
        oneStepTauSumAtScale hP hStruct hP4 m e ≤
        oneStepScalarWeightAtScale hP hStruct m *
          (B * (delta * sqrtθ0)) :=
        mul_le_mul_of_nonneg_left htau_le hscalar_nonneg
    _ ≤ (3 * sqrtθ0) * (B * (delta * sqrtθ0)) :=
        mul_le_mul_of_nonneg_right hscalar_le htau_bound_nonneg
    _ = 3 * B * delta * (sqrtθ0 * sqrtθ0) := by ring
    _ = 3 * B * delta * θ0 := by rw [hsqrt_sq]
    _ = oneStepTauSumConst hP4 * delta * thetaAtScale hP hStruct 0 := by
        simp [oneStepTauSumConst, B, θ0]

/-- At a good scale, the scalar-weighted tau sum is also
`O(sqrt(delta) * Theta_0)`. -/
theorem oneStepScalarWeight_mul_tauSum_le_sqrt_delta_theta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    oneStepScalarWeightAtScale hP hStruct m *
        oneStepTauSumAtScale hP hStruct hP4 m e ≤
      oneStepTauSumConst hP4 * Real.sqrt delta *
        thetaAtScale hP hStruct 0 := by
  have hdelta_le_sqrt :
      delta ≤ Real.sqrt delta :=
    delta_le_sqrt_of_pos_of_le_half hdelta_pos hdelta_le
  have hC_nonneg : 0 ≤ oneStepTauSumConst hP4 :=
    oneStepTauSumConst_nonneg hP4
  have htheta_nonneg :
      0 ≤ thetaAtScale hP hStruct 0 :=
    le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  calc
    oneStepScalarWeightAtScale hP hStruct m *
        oneStepTauSumAtScale hP hStruct hP4 m e ≤
      oneStepTauSumConst hP4 * delta * thetaAtScale hP hStruct 0 :=
        oneStepScalarWeight_mul_tauSum_le_delta_theta
          hP hStruct hP4 hdelta_pos hdelta_le hgood_upper hgood_lower e he
    _ ≤ oneStepTauSumConst hP4 * Real.sqrt delta *
        thetaAtScale hP hStruct 0 := by
        calc
          oneStepTauSumConst hP4 * delta * thetaAtScale hP hStruct 0 =
              (oneStepTauSumConst hP4 * thetaAtScale hP hStruct 0) * delta := by
              ring
          _ ≤ (oneStepTauSumConst hP4 * thetaAtScale hP hStruct 0) *
                Real.sqrt delta :=
              mul_le_mul_of_nonneg_left hdelta_le_sqrt
                (mul_nonneg hC_nonneg htheta_nonneg)
          _ = oneStepTauSumConst hP4 * Real.sqrt delta *
                thetaAtScale hP hStruct 0 := by
              ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
