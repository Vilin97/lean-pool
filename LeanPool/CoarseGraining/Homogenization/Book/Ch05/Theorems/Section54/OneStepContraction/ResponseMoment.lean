/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CoarseRHSPrep
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.EllipticityMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ResponseMomentIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ProbeMomentCompression

/-! # Response Moment -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Unit-scale response moment bridge

This file proves the local bridge used in the one-step contraction proof: for
the special vectors at scale `m`, the unit-cube `L^ζ` response moment is
controlled by the unit-scale `(P4)` ellipticity moment weight with the matched
normalizations `sigma^{-1} Lambda + sigma lambda^{-1}`.
-/

open Section53.JUpperBoundCoarseFluctuations

private theorem blockPosDef_quadratic_nonneg
    {d : ℕ} {A : BlockMat d} (hA : Ch02.BlockPosDef A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  by_cases hX : X = 0
  · subst X
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · exact (hA X hX).le

private theorem block_cross_abs_le_half_quadratics
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) (p q : Vec d) :
    |vecDot q (matVecMul A.lowerLeft p)| ≤
      (1 / 2 : ℝ) *
        (vecDot p (matVecMul A.upperLeft p) +
          vecDot q (matVecMul A.lowerRight q)) := by
  let X : BlockVec d := (0, q)
  let Y : BlockVec d := (p, 0)
  have hcomm :
      blockVecDot Y (blockMatVecMul A X) =
        blockVecDot X (blockMatVecMul A Y) := by
    exact (blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hSymm Y X)
  have hXX :
      blockVecDot X (blockMatVecMul A X) =
        vecDot q (matVecMul A.lowerRight q) := by
    simp [X, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hYY :
      blockVecDot Y (blockMatVecMul A Y) =
        vecDot p (matVecMul A.upperLeft p) := by
    simp [Y, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hXY :
      blockVecDot X (blockMatVecMul A Y) =
        vecDot q (matVecMul A.lowerLeft p) := by
    simp [X, Y, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hYX :
      blockVecDot Y (blockMatVecMul A X) =
        vecDot q (matVecMul A.lowerLeft p) := by
    rw [hcomm, hXY]
  let z := vecDot q (matVecMul A.lowerLeft p)
  let a := vecDot q (matVecMul A.lowerRight q)
  let b := vecDot p (matVecMul A.upperLeft p)
  have hplus :
      0 ≤ a + z + z + b := by
    have hnonneg := blockPosDef_quadratic_nonneg hPos (X + Y)
    have hraw :
        0 ≤ a + z + (z + b) := by
      simpa [z, a, b, blockMatVecMul_add, blockVecDot_add_left,
        blockVecDot_add_right, hXX, hYY, hXY, hYX] using hnonneg
    nlinarith
  have hminus :
      0 ≤ a - z - z + b := by
    have hnonneg := blockPosDef_quadratic_nonneg hPos (X - Y)
    have hnegMul : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
      simpa using blockMatVecMul_smul A (-1) Y
    have hnegDotL :
        blockVecDot (-Y) (blockMatVecMul A X) =
          -blockVecDot Y (blockMatVecMul A X) := by
      simpa using blockVecDot_smul_left (-1) Y (blockMatVecMul A X)
    have hnegDotR :
        blockVecDot X (-blockMatVecMul A Y) =
          -blockVecDot X (blockMatVecMul A Y) := by
      simpa using blockVecDot_smul_right X (blockMatVecMul A Y) (-1)
    have hnegYY :
        blockVecDot (-Y) (-blockMatVecMul A Y) =
          blockVecDot Y (blockMatVecMul A Y) := by
      calc
        blockVecDot (-Y) (-blockMatVecMul A Y) =
            -blockVecDot (-Y) (blockMatVecMul A Y) := by
              simpa using blockVecDot_smul_right (-Y) (blockMatVecMul A Y) (-1)
        _ = blockVecDot Y (blockMatVecMul A Y) := by
              rw [show blockVecDot (-Y) (blockMatVecMul A Y) =
                  -blockVecDot Y (blockMatVecMul A Y) by
                    simpa using blockVecDot_smul_left (-1) Y (blockMatVecMul A Y)]
              ring
    have hraw :
        0 ≤ a + -z + (-z + b) := by
      simpa [sub_eq_add_neg, z, a, b, blockMatVecMul_add, hnegMul,
        blockVecDot_add_left, blockVecDot_add_right, hXX, hYY, hXY, hYX,
        hnegDotL, hnegDotR, hnegYY] using hnonneg
    nlinarith
  have habs : 2 * |z| ≤ a + b := by
    have hz_abs : |z| ≤ (a + b) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    nlinarith
  have htarget : |z| ≤ (1 / 2 : ℝ) * (b + a) := by
    nlinarith
  simpa [z, a, b, add_comm] using htarget

private theorem responseJ_special_pointwise_le_weighted_factors
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (he : Ch02.vecNorm e = 1) :
    (fun a : RegCoeffField d =>
        Ch04.restrictionResponseJObservableCubeSet (originCube d 0)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) a)
      ≤ᵐ[P]
        fun a =>
          (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            sigmaHatAtScale hP hStruct (m : ℤ) *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹ := by
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hσ_pos : 0 < σ := by
    simpa [σ] using GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have he_sq : vecNormSq e = 1 :=
    GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have he_dot : vecDot e e = 1 := by
    simpa [vecNormSq] using he_sq
  have hp_norm :
      vecNormSq p_e = σ⁻¹ := by
    change
      vecNormSq
        (((sigmaHatAtScale hP hStruct (m : ℤ)) ^ (-(1 / 2 : ℝ))) • e) = σ⁻¹
    rw [show sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
    rw [vecNormSq_smul]
    rw [GoodScale.rpow_neg_half_sq_eq_inv hσ_pos, he_sq, mul_one]
  have hq_norm :
      vecNormSq q_e = σ := by
    change
      vecNormSq
        (((sigmaHatAtScale hP hStruct (m : ℤ)) ^ (1 / 2 : ℝ)) • e) = σ
    rw [show sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
    rw [vecNormSq_smul]
    rw [GoodScale.rpow_half_sq_eq_self hσ_pos, he_sq, mul_one]
  have hdot_nonneg : 0 ≤ vecDot p_e q_e := by
    have hpq :
        vecDot p_e q_e = 1 := by
      change
        vecDot
          (((sigmaHatAtScale hP hStruct (m : ℤ)) ^ (-(1 / 2 : ℝ))) • e)
          (((sigmaHatAtScale hP hStruct (m : ℤ)) ^ (1 / 2 : ℝ)) • e) = 1
      rw [show sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
      simp [vecDot_smul_left, vecDot_smul_right]
      have hcross :
          σ ^ (1 / 2 : ℝ) * (σ ^ (-(1 / 2 : ℝ)) * vecDot e e) = 1 := by
        rw [← mul_assoc, mul_comm (σ ^ (1 / 2 : ℝ)) (σ ^ (-(1 / 2 : ℝ)))]
        rw [GoodScale.rpow_neg_half_mul_rpow_half_eq_one hσ_pos, one_mul, he_dot]
      have hcross2 :
          σ ^ (2⁻¹ : ℝ) * (σ ^ (-2⁻¹ : ℝ) * vecDot e e) = 1 := by
        convert hcross using 1
        norm_num
      simpa using hcross2
    rw [hpq]
    norm_num
  filter_upwards
    [Ch04.restrictionResponseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
      hP (originCube d 0) p_e q_e,
     hP.ae_locallyUniformlyEllipticField] with a hJ ha
  let Q : TriadicCube d := originCube d 0
  let A : BlockMat d := coarseBlockMatrix (cubeSet Q) a.toFun
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      A = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [A, F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hSymm : IsSymmetricBlockMat A := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hPos : Ch02.BlockPosDef A := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q)
        (F.coeffOn Q)).block_matrix_posDef
  let upperQuad := vecDot p_e (matVecMul A.upperLeft p_e)
  let lowerQuad := vecDot q_e (matVecMul A.lowerRight q_e)
  have hcross :
      |vecDot q_e (matVecMul A.lowerLeft p_e)| ≤
        (1 / 2 : ℝ) * (upperQuad + lowerQuad) := by
    simpa [upperQuad, lowerQuad, add_comm] using
      block_cross_abs_le_half_quadratics hSymm hPos p_e q_e
  have hJ_le_quads :
      Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a ≤ upperQuad + lowerQuad := by
    calc
      Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a =
          (1 / 2 : ℝ) * lowerQuad - vecDot p_e q_e -
            vecDot q_e (matVecMul A.lowerLeft p_e) +
            (1 / 2 : ℝ) * upperQuad := by
            simpa [Q, A, upperQuad, lowerQuad] using hJ
      _ ≤ (1 / 2 : ℝ) * lowerQuad +
            |vecDot q_e (matVecMul A.lowerLeft p_e)| +
            (1 / 2 : ℝ) * upperQuad := by
            nlinarith [hdot_nonneg, neg_le_abs (vecDot q_e (matVecMul A.lowerLeft p_e))]
      _ ≤ (1 / 2 : ℝ) * lowerQuad +
            (1 / 2 : ℝ) * (upperQuad + lowerQuad) +
            (1 / 2 : ℝ) * upperQuad := by
            nlinarith
      _ = upperQuad + lowerQuad := by ring
  have hUL_norm :
      Ch02.matrixOperatorNorm A.upperLeft ≤
        Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
    calc
      Ch02.matrixOperatorNorm A.upperLeft =
          Ch02.coarseBMatrixNorm Q F := by
            rw [hEq]
            rfl
      _ ≤ Ch02.LambdaSq Q hP4.sUpper (.finite 1) F :=
            Ch02.oneCube_b_le_LambdaSq_finite Q F hP4.sUpper_pos
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
            simp [Ch04.LambdaSqCoeffField, ha, F]
  have hLR_norm :
      Ch02.matrixOperatorNorm A.lowerRight ≤
        (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
    calc
      Ch02.matrixOperatorNorm A.lowerRight =
          Ch02.coarseSigmaStarInvMatrixNorm Q F := by
            rw [hEq]
            rfl
      _ ≤ (Ch02.lambdaSq Q hP4.sLower (.finite 1) F)⁻¹ :=
            Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q F hP4.sLower_pos
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
            simp [Ch04.lambdaSqCoeffField, ha, F]
  have hUpperQuad_le :
      upperQuad ≤ σ⁻¹ * Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
    have hraw :=
      Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        A.upperLeft p_e
    have hle :
        upperQuad ≤ Ch02.matrixOperatorNorm A.upperLeft * vecNormSq p_e :=
      (le_abs_self upperQuad).trans hraw
    calc
      upperQuad ≤ Ch02.matrixOperatorNorm A.upperLeft * vecNormSq p_e := hle
      _ = Ch02.matrixOperatorNorm A.upperLeft * σ⁻¹ := by rw [hp_norm]
      _ ≤ Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a * σ⁻¹ := by
            exact mul_le_mul_of_nonneg_right hUL_norm (inv_pos.mpr hσ_pos).le
      _ = σ⁻¹ * Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by ring
  have hLowerQuad_le :
      lowerQuad ≤ σ *
        (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
    have hraw :=
      Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        A.lowerRight q_e
    have hle :
        lowerQuad ≤ Ch02.matrixOperatorNorm A.lowerRight * vecNormSq q_e :=
      (le_abs_self lowerQuad).trans hraw
    calc
      lowerQuad ≤ Ch02.matrixOperatorNorm A.lowerRight * vecNormSq q_e := hle
      _ = Ch02.matrixOperatorNorm A.lowerRight * σ := by rw [hq_norm]
      _ ≤ (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ * σ := by
            exact mul_le_mul_of_nonneg_right hLR_norm hσ_pos.le
      _ = σ * (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by ring
  exact hJ_le_quads.trans (add_le_add hUpperQuad_le hLowerQuad_le)

private theorem realRpowMomentRoot_le_natAnnealedMomentRoot_of_ae_le
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ζ : ℝ} {ξ : ℕ} {X Y : RegCoeffField d → ℝ}
    (hζ_pos : 0 < ζ) (hζ_le_ξ : ζ ≤ (ξ : ℝ)) (hξ_one : 1 ≤ ξ)
    (hX_meas : AEMeasurable X P)
    (hX_nonneg : ∀ a, 0 ≤ X a) (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hY_memξ : MemLp Y (ξ : ENNReal) P)
    (hXY : X ≤ᵐ[P] Y) :
    Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ ≤
      Ch04.annealedMomentRoot P ξ Y := by
  have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
  have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by
    simp
  have hζ_le_enn : ENNReal.ofReal ζ ≤ (ξ : ENNReal) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hζ_le_ξ
  have hY_memζ : MemLp Y (ENNReal.ofReal ζ) P :=
    hY_memξ.mono_exponent hζ_le_enn
  have hX_memζ : MemLp X (ENNReal.ofReal ζ) P := by
    refine hY_memζ.mono hX_meas.aestronglyMeasurable ?_
    filter_upwards [hXY] with a hle
    rw [Real.norm_of_nonneg (hX_nonneg a),
      Real.norm_of_nonneg (hY_nonneg a)]
    exact hle
  have hcmp₁ :
      eLpNorm X (ENNReal.ofReal ζ) P ≤
        eLpNorm Y (ENNReal.ofReal ζ) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hXY] with a hle
    rw [Real.norm_of_nonneg (hX_nonneg a),
      Real.norm_of_nonneg (hY_nonneg a)]
    exact hle
  have hcmp₂ :
      eLpNorm Y (ENNReal.ofReal ζ) P ≤ eLpNorm Y (ξ : ENNReal) P :=
    eLpNorm_le_eLpNorm_of_exponent_le hζ_le_enn
      hY_memξ.aestronglyMeasurable
  have hcmp :
      eLpNorm X (ENNReal.ofReal ζ) P ≤ eLpNorm Y (ξ : ENNReal) P :=
    hcmp₁.trans hcmp₂
  have hcmp_toReal :
      (eLpNorm X (ENNReal.ofReal ζ) P).toReal ≤
        (eLpNorm Y (ξ : ENNReal) P).toReal :=
    ENNReal.toReal_mono hY_memξ.2.ne hcmp
  have hleft :
      (eLpNorm X (ENNReal.ofReal ζ) P).toReal =
        Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ := by
    rw [hX_memζ.eLpNorm_eq_integral_rpow_norm hζ_ne_zero hζ_ne_top]
    have hnonneg :
        0 ≤
          (∫ a, ‖X a‖ ^ (ENNReal.ofReal ζ).toReal ∂P) ^
            (ENNReal.ofReal ζ).toReal⁻¹ := by
      positivity
    rw [ENNReal.toReal_ofReal hnonneg]
    congr 1
    · exact integral_congr_ae (by
        filter_upwards with a
        rw [ENNReal.toReal_ofReal hζ_pos.le,
          Real.norm_of_nonneg (hX_nonneg a), Real.rpow_eq_pow])
    · rw [ENNReal.toReal_ofReal hζ_pos.le]
  have hright :
      (eLpNorm Y (ξ : ENNReal) P).toReal =
        Ch04.annealedMomentRoot P ξ Y := by
    calc
      (eLpNorm Y (ξ : ENNReal) P).toReal =
          (∫ a, ‖Y a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := Y) (p := ξ) hξ_one hY_memξ
      _ = (∫ a, Y a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            congr 1
            exact integral_congr_ae (by
              filter_upwards with a
              rw [Real.norm_of_nonneg (hY_nonneg a)])
      _ = Ch04.annealedMomentRoot P ξ Y := rfl
  calc
    Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ =
        (eLpNorm X (ENNReal.ofReal ζ) P).toReal := hleft.symm
    _ ≤ (eLpNorm Y (ξ : ENNReal) P).toReal := hcmp_toReal
    _ = Ch04.annealedMomentRoot P ξ Y := hright

/-- Unit-scale response-moment bridge for the special vectors in the
one-step proof.  The constant is `1`; the important point is that the
normalizations remain matched as
`\widehat\sigma_m^{-1} \Lambda + \widehat\sigma_m \lambda^{-1}`. -/
theorem coarseFluctuationResponseMomentAtScale_zero_le_unitMomentWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (he : Ch02.vecNorm e = 1) :
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e ≤
      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
  let : IsProbabilityMeasure P := hP.isProbability
  let ζ := section53CoarseFluctuationZeta hP4
  let ξ := hP4.xi
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let L : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a
  let I : RegCoeffField d → ℝ :=
    fun a =>
      (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹
  let YUpper : RegCoeffField d → ℝ := fun a => σ⁻¹ * L a
  let YLower : RegCoeffField d → ℝ := fun a => σ * I a
  let Y : RegCoeffField d → ℝ := fun a => YUpper a + YLower a
  let X : RegCoeffField d → ℝ :=
    fun a =>
      Ch04.restrictionResponseJObservableCubeSet (originCube d 0)
        (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e) a
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hζ_le_ξ : ζ ≤ (ξ : ℝ) := by
    dsimp [ζ, ξ, section53CoarseFluctuationZeta]
    have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by
      exact_mod_cast hP4.two_le_xi
    have hden_pos : 0 < (hP4.xi : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hξ_one : 1 ≤ ξ :=
    le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hξ_pos : 0 < ξ := lt_of_lt_of_le (by norm_num : 0 < 1) hξ_one
  have hσ_pos : 0 < σ := by
    simpa [σ] using GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := (inv_pos.mpr hσ_pos).le
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  have hL_nonneg : ∀ a, 0 ≤ L a := fun a =>
    Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hP4.sUpper_pos
      (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : ∀ a, 0 ≤ I a := fun a =>
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hP4.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hYUpper_nonneg : ∀ a, 0 ≤ YUpper a := fun a =>
    mul_nonneg hσ_inv_nonneg (hL_nonneg a)
  have hYLower_nonneg : ∀ a, 0 ≤ YLower a := fun a =>
    mul_nonneg hσ_nonneg (hI_nonneg a)
  have hY_nonneg : ∀ a, 0 ≤ Y a := fun a =>
    add_nonneg (hYUpper_nonneg a) (hYLower_nonneg a)
  have hX_nonneg : ∀ a, 0 ≤ X a := fun a =>
    by
      dsimp [X]
      exact
        Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d 0)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) a
  have hX_meas : AEMeasurable X P := by
    simpa [X] using!
      hP.aemeasurable_restrictionResponseJObservableCubeSet
        (originCube d 0)
        (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e)
  have hL_meas : AEMeasurable L P := by
    simpa [L] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hP4.sUpper_pos
  have hI_meas : AEMeasurable I P := by
    simpa [I] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hP4.sLower_pos
  have hYUpper_meas : AEMeasurable YUpper P := hL_meas.const_mul σ⁻¹
  have hYLower_meas : AEMeasurable YLower P := hI_meas.const_mul σ
  have hL_int : Integrable (fun a => L a ^ ξ) P := by
    simpa [L, ξ] using
      Section52.upperFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hI_int : Integrable (fun a => I a ^ ξ) P := by
    simpa [I, ξ] using
      Section52.lowerFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hL_mem : MemLp L (ξ : ENNReal) P := by
    simpa [ξ] using
      memLp_of_integrable_nonneg_nat_pow hξ_pos hL_meas
        (Filter.Eventually.of_forall hL_nonneg) hL_int
  have hI_mem : MemLp I (ξ : ENNReal) P := by
    simpa [ξ] using
      memLp_of_integrable_nonneg_nat_pow hξ_pos hI_meas
        (Filter.Eventually.of_forall hI_nonneg) hI_int
  have hYUpper_mem : MemLp YUpper (ξ : ENNReal) P := by
    simpa [YUpper] using hL_mem.const_mul σ⁻¹
  have hYLower_mem : MemLp YLower (ξ : ENNReal) P := by
    simpa [YLower] using hI_mem.const_mul σ
  have hY_mem : MemLp Y (ξ : ENNReal) P := by
    simpa [Y] using! hYUpper_mem.add hYLower_mem
  have hpoint : X ≤ᵐ[P] Y := by
    simpa [X, Y, YUpper, YLower, L, I, σ] using
      responseJ_special_pointwise_le_weighted_factors
        hP hStruct hP4 m e he
  have hmoment_to_Y :
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e ≤
        Ch04.annealedMomentRoot P ξ Y := by
    simpa [coarseFluctuationResponseMomentAtScale, X, ζ, ξ] using
      realRpowMomentRoot_le_natAnnealedMomentRoot_of_ae_le
        (P := P) (ζ := ζ) (ξ := ξ) (X := X) (Y := Y)
        hζ_pos hζ_le_ξ hξ_one hX_meas hX_nonneg hY_nonneg hY_mem hpoint
  have hYUpper_int : Integrable (fun a => YUpper a ^ ξ) P := by
    have hξ_ne : ξ ≠ 0 := Nat.ne_of_gt hξ_pos
    have hint := hYUpper_mem.integrable_norm_pow hξ_ne
    refine hint.congr ?_
    filter_upwards with a
    rw [Real.norm_of_nonneg (hYUpper_nonneg a)]
  have hYLower_int : Integrable (fun a => YLower a ^ ξ) P := by
    have hξ_ne : ξ ≠ 0 := Nat.ne_of_gt hξ_pos
    have hint := hYLower_mem.integrable_norm_pow hξ_ne
    refine hint.congr ?_
    filter_upwards with a
    rw [Real.norm_of_nonneg (hYLower_nonneg a)]
  have hY_root :
      Ch04.annealedMomentRoot P ξ Y ≤
        σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper ξ +
          σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower ξ := by
    have hY_add :
        Ch04.annealedMomentRoot P ξ Y ≤
          Ch04.annealedMomentRoot P ξ YUpper +
            Ch04.annealedMomentRoot P ξ YLower := by
      simpa [Y] using
        VarianceBoundGoodScale.section54_annealedMomentRoot_add_le
          (P := P) (ξ := ξ) (X := YUpper) (Y := YLower)
          hξ_one hYUpper_nonneg hYLower_nonneg hYUpper_meas hYLower_meas
          hYUpper_int hYLower_int
    have hUpper_eq :
        Ch04.annealedMomentRoot P ξ YUpper =
          σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper ξ := by
      simpa [YUpper, L, Ch04.LambdaMomentAtScale] using
        Section52.section52_annealedMomentRoot_const_mul_of_nonneg
          (P := P) (ξ := ξ) (c := σ⁻¹) (X := L)
          hξ_one hσ_inv_nonneg hL_nonneg
    have hLower_eq :
        Ch04.annealedMomentRoot P ξ YLower =
          σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower ξ := by
      simpa [YLower, I, Ch04.lambdaInvMomentAtScale] using
        Section52.section52_annealedMomentRoot_const_mul_of_nonneg
          (P := P) (ξ := ξ) (c := σ) (X := I)
          hξ_one hσ_nonneg hI_nonneg
    simpa [hUpper_eq, hLower_eq] using hY_add
  calc
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
        ≤ Ch04.annealedMomentRoot P ξ Y := hmoment_to_Y
    _ ≤ σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper ξ +
          σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower ξ := hY_root
    _ = coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
          simp [coarseFluctuationUnitMomentWeightAtScale, σ, ξ, add_comm]

/-- Product form of the unit-scale response-moment bridge, matching the
positive-excess term in the Section 5.3 RHS. -/
theorem coarseFluctuationUnitMomentWeight_mul_responseMoment_zero_le_sq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Vec d) (he : Ch02.vecNorm e = 1) :
    coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e ≤
      (coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m) ^ (2 : ℕ) := by
  have hunit_nonneg :
      0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
    have hσ_nonneg :
        0 ≤ sigmaHatAtScale hP hStruct (m : ℤ) :=
      Real.sqrt_nonneg _
    have hσ_inv_nonneg :
        0 ≤ (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ :=
      inv_nonneg.mpr hσ_nonneg
    have hLower :
        0 ≤ Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi :=
      Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
    have hUpper :
        0 ≤ Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi :=
      Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
    dsimp [coarseFluctuationUnitMomentWeightAtScale]
    exact add_nonneg (mul_nonneg hσ_nonneg hLower)
      (mul_nonneg hσ_inv_nonneg hUpper)
  have hresp_le :=
    coarseFluctuationResponseMomentAtScale_zero_le_unitMomentWeightAtScale
      hP hStruct hP4 m e he
  calc
    coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 0 m e
        ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
          exact mul_le_mul_of_nonneg_left hresp_le hunit_nonneg
    _ = (coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m) ^ (2 : ℕ) := by
          ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
