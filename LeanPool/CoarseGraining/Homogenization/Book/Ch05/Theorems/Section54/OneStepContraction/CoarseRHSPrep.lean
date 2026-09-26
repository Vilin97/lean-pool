/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.BetaBridge
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.TauSum
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Assembly

/-! # Coarse RHSPrep -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Preparing the Section 5.3 coarse-fluctuation RHS

This file records the pieces of the final one-step contraction assembly that
can be proved before the final Section 5.3 estimate lands.  The dependencies
on Section 5.3 remain local to the one-step-contraction directory.
-/

open Section53.JUpperBoundCoarseFluctuations

/-- The scalar weight in the Section 5.3 coarse-fluctuation RHS is exactly the
one used by the Section 5.4 one-step contraction proof. -/
theorem coarseFluctuationScalarWeightAtScale_eq_oneStepScalarWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℕ) :
    coarseFluctuationScalarWeightAtScale hP hStruct m =
      oneStepScalarWeightAtScale hP hStruct m := by
  rfl

private theorem int_toNat_nat_sub_of_le {j m : ℕ} (hjm : j ≤ m) :
    Int.toNat ((m : ℤ) - (j : ℤ)) = m - j := by
  have hnonneg : 0 ≤ (m : ℤ) - (j : ℤ) := by
    omega
  have hto :
      ((Int.toNat ((m : ℤ) - (j : ℤ)) : ℕ) : ℤ) =
        (m : ℤ) - (j : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hsub : ((m - j : ℕ) : ℤ) = (m : ℤ) - (j : ℤ) := by
    omega
  exact Int.ofNat.inj (hto.trans hsub.symm)

private theorem sum_int_Icc_one_nat_eq_sum_nat_Icc (m : ℕ) (F : ℤ → ℝ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) (m : ℤ), F n) =
      ∑ j ∈ Finset.Icc 1 m, F (j : ℤ) := by
  classical
  refine
    Finset.sum_bij'
      (fun n _hn => Int.toNat n)
      (fun j _hj => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by linarith
    have hto : ((Int.toNat n : ℕ) : ℤ) = n :=
      Int.toNat_of_nonneg hn_nonneg
    exact Finset.mem_Icc.mpr
      ⟨by
        have hcast : (1 : ℤ) ≤ ((Int.toNat n : ℕ) : ℤ) := by
          simpa [hto] using hn_bounds.1
        exact_mod_cast hcast,
       by
        have hcast : ((Int.toNat n : ℕ) : ℤ) ≤ (m : ℤ) := by
          simpa [hto] using hn_bounds.2
        exact_mod_cast hcast⟩
  · intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr
      ⟨by
        change (1 : ℤ) ≤ (j : ℤ)
        exact_mod_cast hj_bounds.1,
       by
        change (j : ℤ) ≤ (m : ℤ)
        exact_mod_cast hj_bounds.2⟩
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by linarith
    exact Int.toNat_of_nonneg hn_nonneg
  · intro j _hj
    simp
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by linarith
    rw [Int.toNat_of_nonneg hn_nonneg]

/-- The Section 5.3-beta tau sum, reindexed over natural lower scales. -/
noncomputable def oneStepCoarseTauSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  ∑ j ∈ Finset.Icc 1 m,
    VarianceBoundGoodScale.varianceWeight β m j *
      tauAtScale P (m : ℤ) (j : ℤ) p_e q_e

/-- At `k = 0`, the Section 5.3 tau sum is the natural-scale sum used by the
one-step proof, with the Section 5.3 beta. -/
theorem coarseFluctuationTauSumAtScale_zero_eq_oneStepCoarseTauSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) :
    coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e =
      oneStepCoarseTauSumAtScale hP hStruct hP4 m e := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  unfold coarseFluctuationTauSumAtScale oneStepCoarseTauSumAtScale
  dsimp only
  rw [show ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) by norm_num]
  rw [sum_int_Icc_one_nat_eq_sum_nat_Icc]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  simp [VarianceBoundGoodScale.varianceWeight, int_toNat_nat_sub_of_le hjm]

/-- The Section 5.3-beta full-block fluctuation sum, reindexed over natural
lower scales. -/
noncomputable def oneStepCoarseFullBlockSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  ∑ j ∈ Finset.Icc 1 m,
    VarianceBoundGoodScale.varianceWeight β m j *
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P

/-- At `k = 0`, the Section 5.3 full-block fluctuation sum is the natural-scale
sum used by the one-step proof, with the Section 5.3 beta. -/
theorem coarseFluctuationFullBlockSumAtScale_zero_eq_oneStepCoarseFullBlockSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 0 m =
      oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m := by
  classical
  let β := section53CoarseFluctuationBeta hP4
  unfold coarseFluctuationFullBlockSumAtScale oneStepCoarseFullBlockSumAtScale
  dsimp only
  rw [show ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) by norm_num]
  rw [sum_int_Icc_one_nat_eq_sum_nat_Icc]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  simp [VarianceBoundGoodScale.varianceWeight, int_toNat_nat_sub_of_le hjm]

/-- The reindexed Section 5.3-beta full-block fluctuation sum is
nonnegative. -/
theorem oneStepCoarseFullBlockSumAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ oneStepCoarseFullBlockSumAtScale hP hStruct hP4 m := by
  unfold oneStepCoarseFullBlockSumAtScale
  refine VarianceBoundGoodScale.sum_Icc_varianceWeight_mul_nonneg ?_
  intro j _hj
  exact integral_nonneg fun a =>
    by
      simpa using!
        VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a

/-- The harmless geometric constant for the Section 5.3-beta tau sum. -/
noncomputable def oneStepCoarseTauSumConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  3 * (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹

/-- The Section 5.3-beta tau-sum constant is nonnegative. -/
theorem oneStepCoarseTauSumConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ oneStepCoarseTauSumConst hP4 := by
  unfold oneStepCoarseTauSumConst
  have hgeo : 0 < geometricDiscount (section53CoarseFluctuationBeta hP4) 1 :=
    geometricDiscount_pos (by simpa using section53CoarseFluctuationBeta_pos hP4)
  positivity

/-- At a good scale, the Section 5.3-beta tau sum is bounded by the
geometric tail times `delta * sqrt(Theta_0)`. -/
theorem oneStepCoarseTauSumAtScale_le
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
    oneStepCoarseTauSumAtScale hP hStruct hP4 m e ≤
      (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹ *
        (delta * Real.sqrt (thetaAtScale hP hStruct 0)) := by
  let β := section53CoarseFluctuationBeta hP4
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
      (by simpa [β] using section53CoarseFluctuationBeta_pos hP4) m
  calc
    oneStepCoarseTauSumAtScale hP hStruct hP4 m e =
        ∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j *
            tauAtScale P (m : ℤ) (j : ℤ) p_e q_e := by
          simp [oneStepCoarseTauSumAtScale, β, p_e, q_e]
    _ ≤
        (∑ j ∈ Finset.Icc 1 m,
          VarianceBoundGoodScale.varianceWeight β m j) * K :=
        hsum_const
    _ ≤ (geometricDiscount β 1)⁻¹ * K :=
        mul_le_mul_of_nonneg_right hweights hK_nonneg
    _ =
        (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹ *
          (delta * Real.sqrt (thetaAtScale hP hStruct 0)) := by
        rfl

/-- At a good scale, the scalar-weighted Section 5.3 tau sum at `k = 0` is
`O(delta * Theta_0)`. -/
theorem coarseFluctuationScalarWeight_mul_tauSum_zero_le_delta_theta
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
    coarseFluctuationScalarWeightAtScale hP hStruct m *
        coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e ≤
      oneStepCoarseTauSumConst hP4 * delta * thetaAtScale hP hStruct 0 := by
  let θ0 := thetaAtScale hP hStruct 0
  let sqrtθ0 := Real.sqrt θ0
  let B := (geometricDiscount (section53CoarseFluctuationBeta hP4) 1)⁻¹
  have hscalar_nonneg :
      0 ≤ oneStepScalarWeightAtScale hP hStruct m :=
    oneStepScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hscalar_le :
      oneStepScalarWeightAtScale hP hStruct m ≤ 3 * sqrtθ0 := by
    simpa [sqrtθ0] using!
      goodScale_oneStepScalarWeight_le hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
  have htau_le :
      oneStepCoarseTauSumAtScale hP hStruct hP4 m e ≤
        B * (delta * sqrtθ0) := by
    simpa [B, sqrtθ0] using!
      oneStepCoarseTauSumAtScale_le hP hStruct hP4 hdelta_pos hdelta_le
        hgood_upper hgood_lower e he
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hgeo : 0 < geometricDiscount (section53CoarseFluctuationBeta hP4) 1 :=
      geometricDiscount_pos (by simpa using section53CoarseFluctuationBeta_pos hP4)
    positivity
  have htau_bound_nonneg : 0 ≤ B * (delta * sqrtθ0) := by
    exact mul_nonneg hB_nonneg
      (mul_nonneg hdelta_pos.le (by dsimp [sqrtθ0]; exact Real.sqrt_nonneg _))
  have htheta_nonneg : 0 ≤ θ0 := by
    dsimp [θ0]
    exact le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  have hsqrt_sq : sqrtθ0 * sqrtθ0 = θ0 := by
    dsimp [sqrtθ0]
    exact Real.mul_self_sqrt htheta_nonneg
  calc
    coarseFluctuationScalarWeightAtScale hP hStruct m *
        coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e =
        oneStepScalarWeightAtScale hP hStruct m *
          oneStepCoarseTauSumAtScale hP hStruct hP4 m e := by
          rw [coarseFluctuationScalarWeightAtScale_eq_oneStepScalarWeightAtScale,
            coarseFluctuationTauSumAtScale_zero_eq_oneStepCoarseTauSumAtScale]
    _ ≤
        oneStepScalarWeightAtScale hP hStruct m *
          (B * (delta * sqrtθ0)) :=
        mul_le_mul_of_nonneg_left htau_le hscalar_nonneg
    _ ≤ (3 * sqrtθ0) * (B * (delta * sqrtθ0)) :=
        mul_le_mul_of_nonneg_right hscalar_le htau_bound_nonneg
    _ = 3 * B * delta * (sqrtθ0 * sqrtθ0) := by ring
    _ = 3 * B * delta * θ0 := by rw [hsqrt_sq]
    _ = oneStepCoarseTauSumConst hP4 * delta *
        thetaAtScale hP hStruct 0 := by
        simp [oneStepCoarseTauSumConst, B, θ0]

/-- At a good scale, the scalar-weighted Section 5.3 tau sum at `k = 0` is
also `O(sqrt(delta) * Theta_0)`. -/
theorem coarseFluctuationScalarWeight_mul_tauSum_zero_le_sqrt_delta_theta
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
    coarseFluctuationScalarWeightAtScale hP hStruct m *
        coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e ≤
      oneStepCoarseTauSumConst hP4 * Real.sqrt delta *
        thetaAtScale hP hStruct 0 := by
  have hdelta_le_sqrt :
      delta ≤ Real.sqrt delta :=
    delta_le_sqrt_of_pos_of_le_half hdelta_pos hdelta_le
  have hC_nonneg : 0 ≤ oneStepCoarseTauSumConst hP4 :=
    oneStepCoarseTauSumConst_nonneg hP4
  have htheta_nonneg :
      0 ≤ thetaAtScale hP hStruct 0 :=
    le_trans zero_le_one (one_le_thetaAtScale_zero_of_P4 hP hStruct hP4)
  calc
    coarseFluctuationScalarWeightAtScale hP hStruct m *
        coarseFluctuationTauSumAtScale hP hStruct hP4 0 m e ≤
      oneStepCoarseTauSumConst hP4 * delta *
        thetaAtScale hP hStruct 0 :=
        coarseFluctuationScalarWeight_mul_tauSum_zero_le_delta_theta
          hP hStruct hP4 hdelta_pos hdelta_le hgood_upper hgood_lower e he
    _ ≤ oneStepCoarseTauSumConst hP4 * Real.sqrt delta *
        thetaAtScale hP hStruct 0 := by
        calc
          oneStepCoarseTauSumConst hP4 * delta *
              thetaAtScale hP hStruct 0 =
              (oneStepCoarseTauSumConst hP4 *
                thetaAtScale hP hStruct 0) * delta := by
              ring
          _ ≤ (oneStepCoarseTauSumConst hP4 *
                thetaAtScale hP hStruct 0) * Real.sqrt delta :=
              mul_le_mul_of_nonneg_left hdelta_le_sqrt
                (mul_nonneg hC_nonneg htheta_nonneg)
          _ = oneStepCoarseTauSumConst hP4 * Real.sqrt delta *
                thetaAtScale hP hStruct 0 := by
              ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
