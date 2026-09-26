/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.ErrorBounds

/-! # Triangle -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

theorem norm_add_sq_le_two_sq_add_two_sq {E : Type*} [SeminormedAddCommGroup E]
    (x y : E) :
    ‖x + y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  have hnorm : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hsq :
      ‖x + y‖ ^ (2 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem descendantsAverageFullBlockMat_operatorNormSq_le_descendantsAverage_operatorNormSq
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → FullBlockMat d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (descendantsAverageFullBlockMat Q j F)‖ ^ (2 : ℕ) ≤
      descendantsAverage Q j
        (fun R =>
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (F R)‖ ^
            (2 : ℕ)) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let c : ℝ := (D.card : ℝ)⁻¹
  let T : TriadicCube d → EuclideanSpace ℝ (BlockCoord d) →L[ℝ]
      EuclideanSpace ℝ (BlockCoord d) :=
    fun R => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (F R)
  let S : ℝ := D.sum fun R => ‖T R‖
  let S₂ : ℝ := D.sum fun R => ‖T R‖ ^ (2 : ℕ)
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hcard_ne : (D.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hmat :
      descendantsAverageFullBlockMat Q j F = c • D.sum F := by
    ext α β
    change descendantsAverage Q j (fun R => F R α β) = c * (D.sum F) α β
    rw [Matrix.sum_apply]
    simp [descendantsAverage, D, c]
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (descendantsAverageFullBlockMat Q j F)‖ ≤ c * S := by
    calc
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (descendantsAverageFullBlockMat Q j F)‖
          = ‖c • D.sum T‖ := by
              rw [hmat]
              simp [T]
      _ = c * ‖D.sum T‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard_pos)]
      _ ≤ c * S := by
              exact mul_le_mul_of_nonneg_left
                (norm_sum_le D (fun R => T R)) (inv_nonneg.mpr hcard_pos.le)
  have hsq_norm :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (descendantsAverageFullBlockMat Q j F)‖ ^ (2 : ℕ) ≤
        (c * S) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hsum_sq :
      S ^ (2 : ℕ) ≤ (D.card : ℝ) * S₂ := by
    simpa [S, S₂] using
      sq_sum_le_card_mul_sum_sq (s := D) (f := fun R => ‖T R‖)
  have havg_sq : (c * S) ^ (2 : ℕ) ≤ c * S₂ := by
    calc
      (c * S) ^ (2 : ℕ) = c ^ (2 : ℕ) * S ^ (2 : ℕ) := by ring
      _ ≤ c ^ (2 : ℕ) * ((D.card : ℝ) * S₂) := by
            exact mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg c)
      _ = c * S₂ := by
            dsimp [c]
            field_simp [hcard_ne]
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (descendantsAverageFullBlockMat Q j F)‖ ^ (2 : ℕ)
        ≤ (c * S) ^ (2 : ℕ) := hsq_norm
    _ ≤ c * S₂ := havg_sq
    _ =
      descendantsAverage Q j
        (fun R =>
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (F R)‖ ^
            (2 : ℕ)) := by
        simp [descendantsAverage, D, c, S₂, T]

/-- Jensen/convexity bound for the squared operator norm of the normalized
descendant-average fluctuation. -/
theorem descendantsAverageNormalizedFluctuationOperatorNormSq_le_descendantsAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    descendantsAverageNormalizedFluctuationOperatorNormSq hP hStruct center Q j a ≤
      descendantsAverage Q j
        (fun R =>
          Ch04.fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
            (cubeSet R) a) := by
  simpa [descendantsAverageNormalizedFluctuationOperatorNormSq,
    descendantsAverageNormalizedFluctuationMatrix,
    Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq]
    using
      descendantsAverageFullBlockMat_operatorNormSq_le_descendantsAverage_operatorNormSq
        (Q := Q) (j := j)
        (F := fun R =>
          Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
            hP hStruct center (cubeSet R) a)

theorem aemeasurable_fullBlockNormalizedFluctuationMatrix_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
          hP hStruct center (cubeSet Q) a) P := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  let g : FullBlockMat d → FullBlockMat d := fun M => D * (M - Abar) * D
  have hg : Measurable g := by
    have hcont : Continuous g := by
      dsimp [g]
      fun_prop
    exact hcont.measurable
  have hM :
      AEMeasurable
        (fun a : RegCoeffField d =>
          toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  simpa [Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix,
    b, c, D, Abar, g] using! hg.comp_aemeasurable hM

theorem aemeasurable_descendantsAverageNormalizedFluctuationMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a) P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      AEMeasurable
        (fun a : RegCoeffField d =>
          ∑ R ∈ D,
            Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
              hP hStruct center (cubeSet R) a) P := by
    refine (Finset.aemeasurable_sum D (fun R _hR =>
        aemeasurable_fullBlockNormalizedFluctuationMatrix_cubeSet
          hP hStruct center R)).congr ?_
    filter_upwards with a
    simp
  have hscaled :
      AEMeasurable
        (fun a : RegCoeffField d =>
          ((D.card : ℝ)⁻¹) •
            (∑ R ∈ D,
              Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
                hP hStruct center (cubeSet R) a)) P :=
    hsum.const_smul ((D.card : ℝ)⁻¹)
  refine hscaled.congr ?_
  filter_upwards with a
  rw [descendantsAverageNormalizedFluctuationMatrix,
    descendantsAverageFullBlockMat_eq_smul_sum]

theorem aemeasurable_descendantsAverageNormalizedFluctuationOperatorNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct center Q j a) P := by
  let g : FullBlockMat d → ℝ :=
    fun M => ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ)
  have hg : Measurable g := by
    have hcont : Continuous g :=
      ((continuous_norm.comp
        ((LinearEquiv.toLinearMap
          (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            |>.toAlgEquiv |>.toLinearEquiv)).continuous_of_finiteDimensional)).pow 2)
    exact hcont.measurable
  simpa [descendantsAverageNormalizedFluctuationOperatorNormSq, g] using!
    hg.comp_aemeasurable
      (aemeasurable_descendantsAverageNormalizedFluctuationMatrix
        hP hStruct center Q j)

theorem integrable_descendantsAverageNormalizedFluctuationOperatorNormSq_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (_hk : k ≤ n) :
    Integrable
      (descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct (m : ℤ) (originCube d (n : ℤ)) (n - k)) P := by
  classical
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  have hdomInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage Q j
            (fun R =>
              Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct (m : ℤ) R a)) P := by
    refine Ch04.integrable_descendantsAverage ?_
    intro R hR
    have hR_nonneg : 0 ≤ R.scale := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      have hQscale : Q.scale = (n : ℤ) := by simp [Q, originCube]
      rw [hscale, hQscale]
      have hj_le : j ≤ n := by
        dsimp [j]
        exact Nat.sub_le n k
      exact sub_nonneg.mpr (by exact_mod_cast hj_le)
    exact
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg_scale
          hP hStruct hP4 (m : ℤ) R hR_nonneg
  refine Integrable.mono' hdomInt
    (aemeasurable_descendantsAverageNormalizedFluctuationOperatorNormSq
      hP hStruct (m : ℤ) Q j).aestronglyMeasurable ?_
  filter_upwards with a
  have hle :=
    descendantsAverageNormalizedFluctuationOperatorNormSq_le_descendantsAverage
      hP hStruct (m : ℤ) Q j a
  have hleft_nonneg :
      0 ≤ descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct (m : ℤ) Q j a := by
    simp [descendantsAverageNormalizedFluctuationOperatorNormSq]
  have hright_nonneg :
      0 ≤
        descendantsAverage Q j
          (fun R =>
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) R a) := by
    exact descendantsAverage_nonneg Q j
      (fun R =>
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) R a)
      (fun R _hR =>
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
            hP hStruct (m : ℤ) R a)
  rw [Real.norm_of_nonneg (by simpa [Q, j] using hleft_nonneg)]
  simpa [Q, j, Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale] using hle

/-- Jensen/convexity bound for the squared operator norm of the
arbitrary-normalizer descendant-average fluctuation. -/
theorem descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_descendantsAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) :
    descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct center S Q j a ≤
      descendantsAverage Q j
        (fun R =>
          fullBlockFluctuationOperatorNormSqWithNormalizer
            hP hStruct center S (cubeSet R) a) := by
  simpa [descendantsAverageFluctuationOperatorNormSqWithNormalizer,
    descendantsAverageFluctuationMatrixWithNormalizer,
    fullBlockFluctuationOperatorNormSqWithNormalizer]
    using
      descendantsAverageFullBlockMat_operatorNormSq_le_descendantsAverage_operatorNormSq
        (Q := Q) (j := j)
        (F := fun R =>
          fullBlockFluctuationMatrixWithNormalizer
            hP hStruct center S (cubeSet R) a)

/-- Pointwise variance triangle for an arbitrary deterministic normalizer. -/
theorem fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_two_error
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) :
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        hP hStruct center S Q a ≤
      2 * descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct center S Q j a +
      2 * coarseAverageErrorOperatorNormSqWithNormalizer
        hP hStruct center S Q j a := by
  let parentMatrix : FullBlockMat d :=
    fullBlockFluctuationMatrixWithNormalizer hP hStruct center S (cubeSet Q) a
  let averageMatrix : FullBlockMat d :=
    descendantsAverageFluctuationMatrixWithNormalizer hP hStruct center S Q j a
  let errorMatrix : FullBlockMat d :=
    coarseAverageErrorMatrixWithNormalizer hP hStruct center S Q j a
  let parentCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) parentMatrix
  let averageCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) averageMatrix
  let errorCLM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) errorMatrix
  have hparent : parentMatrix = averageMatrix + errorMatrix := by
    dsimp [parentMatrix, averageMatrix, errorMatrix, coarseAverageErrorMatrixWithNormalizer]
    abel
  have hclm : parentCLM = averageCLM + errorCLM := by
    dsimp [parentCLM, averageCLM, errorCLM]
    rw [hparent, map_add]
  calc
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        hP hStruct center S Q a
        = ‖parentCLM‖ ^ (2 : ℕ) := by
          rfl
    _ = ‖averageCLM + errorCLM‖ ^ (2 : ℕ) := by
          rw [hclm]
    _ ≤ 2 * ‖averageCLM‖ ^ (2 : ℕ) + 2 * ‖errorCLM‖ ^ (2 : ℕ) :=
          norm_add_sq_le_two_sq_add_two_sq averageCLM errorCLM
    _ =
        2 * descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct center S Q j a +
        2 * coarseAverageErrorOperatorNormSqWithNormalizer
          hP hStruct center S Q j a := by
          rfl

/-- A version whose first term is the descendant average of the
arbitrary-normalizer fluctuation observable. -/
theorem fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverage_add_two_error
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) :
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        hP hStruct center S Q a ≤
      2 * descendantsAverage Q j
        (fun R =>
          fullBlockFluctuationOperatorNormSqWithNormalizer
            hP hStruct center S (cubeSet R) a) +
      2 * coarseAverageErrorOperatorNormSqWithNormalizer
        hP hStruct center S Q j a := by
  have htriangle :=
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_two_error
      hP hStruct center S Q j a
  have hjensen :=
    descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_descendantsAverage
      hP hStruct center S Q j a
  nlinarith

/-- Section 5.6 variance estimate with quadratic `J` error and arbitrary
deterministic normalizers.  The manuscript specialization is
`S = B^{-1/2}` and `T = B^{1/2}`. -/
theorem fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_eight_blockJTraceAverageSqWithNormalizers_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        hP hStruct center S Q a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      2 * descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct center S Q j a +
      8 * blockJTraceAverageSqWithNormalizers S T Q j a := by
  filter_upwards
    [coarseAverageErrorOperatorNormSqWithNormalizer_le_four_blockJTraceAverageSqWithNormalizers_ae
      hP hStruct center S T Q j] with a herror
  have htriangle :=
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_two_error
      hP hStruct center S Q j a
  nlinarith

/-- Jensen-relaxed version of the arbitrary-normalizer variance estimate. -/
theorem fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverage_add_eight_blockJTraceAverageSqWithNormalizers_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
        hP hStruct center S Q a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      2 * descendantsAverage Q j
        (fun R =>
          fullBlockFluctuationOperatorNormSqWithNormalizer
            hP hStruct center S (cubeSet R) a) +
      8 * blockJTraceAverageSqWithNormalizers S T Q j a := by
  filter_upwards
    [coarseAverageErrorOperatorNormSqWithNormalizer_le_four_blockJTraceAverageSqWithNormalizers_ae
      hP hStruct center S T Q j] with a herror
  have htriangle :=
    fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverage_add_two_error
      hP hStruct center S Q j a
  nlinarith
end

end Section56
end Ch05
end Book
end Homogenization
