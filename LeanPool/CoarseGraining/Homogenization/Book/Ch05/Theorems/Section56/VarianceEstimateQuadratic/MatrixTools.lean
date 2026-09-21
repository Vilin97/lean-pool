/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.TraceBudget

/-! # Matrix Tools -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

theorem normalizedInvSqrtBlockProbe_inl_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (i : Fin d) :
    normalizedInvSqrtBlockProbe hP hStruct center (Sum.inl i) =
      ((Real.sqrt (hP.barSigmaAtScale hStruct center))⁻¹ • Pi.single i 1, 0) := by
  ext k
  · by_cases hki : k = i
    · subst k
      simp [normalizedInvSqrtBlockProbe, Ch04.scalarFullBlockInvSqrtDiag,
        ofFullBlockVec, Pi.single, smul_eq_mul]
    · simp [normalizedInvSqrtBlockProbe, Ch04.scalarFullBlockInvSqrtDiag,
        ofFullBlockVec, Pi.single, smul_eq_mul, hki]
  · simp [normalizedInvSqrtBlockProbe, Ch04.scalarFullBlockInvSqrtDiag,
      ofFullBlockVec, Pi.single]

theorem normalizedSqrtBlockProbe_inl_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (i : Fin d) :
    normalizedSqrtBlockProbe hP hStruct center (Sum.inl i) =
      (Real.sqrt (hP.barSigmaAtScale hStruct center) • Pi.single i 1, 0) := by
  ext k
  · by_cases hki : k = i
    · subst k
      simp [normalizedSqrtBlockProbe, scalarFullBlockSqrtDiag,
        ofFullBlockVec, Pi.single, smul_eq_mul]
    · simp [normalizedSqrtBlockProbe, scalarFullBlockSqrtDiag,
        ofFullBlockVec, Pi.single, smul_eq_mul, hki]
  · simp [normalizedSqrtBlockProbe, scalarFullBlockSqrtDiag,
      ofFullBlockVec, Pi.single]

theorem fullBlockOperatorNorm_le_trace_of_posSemidef
    {d : ℕ} (M : FullBlockMat d) (hM : M.PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ≤
      Ch02.fullBlockTrace M := by
  classical
  let hHerm : M.IsHermitian := hM.isHermitian
  have heig_nonneg : ∀ α : BlockCoord d, 0 ≤ hHerm.eigenvalues α :=
    hM.eigenvalues_nonneg
  have hsum_nonneg : 0 ≤ ∑ α : BlockCoord d, hHerm.eigenvalues α :=
    Finset.sum_nonneg fun α _hα => heig_nonneg α
  let D : FullBlockMat d := Matrix.diagonal hHerm.eigenvalues
  have hspectral : M = Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D := by
    simpa [D] using hHerm.spectral_theorem
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖
        = ‖M‖ := Matrix.l2_opNorm_toEuclideanCLM M
    _ = ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ :=
          congrArg (fun N : FullBlockMat d => ‖N‖) hspectral
    _ = ‖D‖ := by
          calc
            ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ =
                ‖(hHerm.eigenvectorUnitary : FullBlockMat d) * D *
                  star (hHerm.eigenvectorUnitary : FullBlockMat d)‖ := by
                  simp [Unitary.conjStarAlgAut_apply]
            _ = ‖D * star (hHerm.eigenvectorUnitary : FullBlockMat d)‖ := by
                  rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
            _ = ‖D * (star hHerm.eigenvectorUnitary : unitary (FullBlockMat d))‖ := by
                  simp
            _ = ‖D‖ := by
                  rw [CStarRing.norm_mul_coe_unitary]
    _ = ‖hHerm.eigenvalues‖ := by
          simp [D]
    _ ≤ ∑ α : BlockCoord d, hHerm.eigenvalues α := by
          refine (pi_norm_le_iff_of_nonneg hsum_nonneg).mpr ?_
          intro α
          calc
            ‖hHerm.eigenvalues α‖ = hHerm.eigenvalues α := by
              simp [Real.norm_eq_abs, abs_of_nonneg (heig_nonneg α)]
            _ ≤ ∑ β : BlockCoord d, hHerm.eigenvalues β :=
              Finset.single_le_sum (fun β _hβ => heig_nonneg β) (Finset.mem_univ α)
    _ = Ch02.fullBlockTrace M := by
          symm
          calc
            Ch02.fullBlockTrace M = M.trace := by
              simp [Ch02.fullBlockTrace, Matrix.trace]
            _ = ∑ α : BlockCoord d, hHerm.eigenvalues α := by
              simpa using hHerm.trace_eq_sum_eigenvalues

theorem fullBlockOperatorNormSq_le_trace_sq_of_posSemidef
    {d : ℕ} (M : FullBlockMat d) (hM : M.PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) ≤
      Ch02.fullBlockTrace M ^ (2 : ℕ) := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (fullBlockOperatorNorm_le_trace_of_posSemidef M hM) 2

theorem blockSub_posSemidef_of_blockMatLoewnerLE
    {d : ℕ} {A B : BlockMat d}
    (hAB : BlockMatLoewnerLE A B)
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    (toFullBlockMat B - toFullBlockMat A).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?hHerm ?hquad
  · have hA_full : (toFullBlockMat A).IsSymm :=
      isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
    have hB_full : (toFullBlockMat B).IsSymm :=
      isSymm_toFullBlockMat_of_isSymmetricBlockMat hB
    have hdiff : (toFullBlockMat B - toFullBlockMat A).IsSymm := hB_full.sub hA_full
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hdiff
  · intro q
    let X : BlockVec d := ofFullBlockVec q
    have hquad_eq :
        Section54.VarianceBoundGoodScale.fullBlockQuadratic
            (toFullBlockMat B - toFullBlockMat A) q =
          blockVecDot X
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
      unfold Section54.VarianceBoundGoodScale.fullBlockQuadratic
      rw [← dotProduct_toFullBlockVec X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
      rw [toFullBlockVec_blockMatVecMul]
      simp [X]
    have hdiff_dot :
        blockVecDot X
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
          blockVecDot X (blockMatVecMul B X) -
            blockVecDot X (blockMatVecMul A X) := by
      simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
    have horder := hAB X
    change 0 ≤
      Section54.VarianceBoundGoodScale.fullBlockQuadratic
        (toFullBlockMat B - toFullBlockMat A) q
    rw [hquad_eq, hdiff_dot]
    nlinarith

theorem transpose_blockSub_posSemidef_of_blockMatLoewnerLE
    {d : ℕ} (S : FullBlockMat d) {A B : BlockMat d}
    (hAB : BlockMatLoewnerLE A B)
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    (Matrix.transpose S * (toFullBlockMat B - toFullBlockMat A) * S).PosSemidef := by
  have hPSD := blockSub_posSemidef_of_blockMatLoewnerLE hAB hA hB
  simpa [Matrix.conjTranspose] using! hPSD.conjTranspose_mul_mul_same S

theorem diagonal_blockSub_posSemidef_of_blockMatLoewnerLE
    {d : ℕ} {A B : BlockMat d} (r : BlockCoord d → ℝ)
    (hAB : BlockMatLoewnerLE A B)
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
        Matrix.diagonal r).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?hHerm ?hquad
  · have hA_full : (toFullBlockMat A).IsSymm :=
      isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
    have hB_full : (toFullBlockMat B).IsSymm :=
      isSymm_toFullBlockMat_of_isSymmetricBlockMat hB
    have hdiff : (toFullBlockMat B - toFullBlockMat A).IsSymm := hB_full.sub hA_full
    have hsymm :=
      Section54.VarianceBoundGoodScale.isSymm_diagonal_mul_fullBlockMat_mul_diagonal
        r hdiff
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsymm
  · intro q
    let X : BlockVec d := ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q)
    have hquad_eq :
        Section54.VarianceBoundGoodScale.fullBlockQuadratic
            (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
              Matrix.diagonal r) q =
          blockVecDot X
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
      simpa [X] using
        Section54.VarianceBoundGoodScale.fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
          r (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) q
    have hdiff_dot :
        blockVecDot X
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
          blockVecDot X (blockMatVecMul B X) -
            blockVecDot X (blockMatVecMul A X) := by
      simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
    have horder := hAB X
    change 0 ≤
      Section54.VarianceBoundGoodScale.fullBlockQuadratic
        (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
          Matrix.diagonal r) q
    rw [hquad_eq, hdiff_dot]
    nlinarith

theorem toFullBlockMat_descendantsAverageBlockMat
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → BlockMat d) :
    toFullBlockMat (descendantsAverageBlockMat Q j F) =
      descendantsAverageFullBlockMat Q j (fun R => toFullBlockMat (F R)) := by
  ext α β
  cases α <;> cases β <;>
    simp [descendantsAverageFullBlockMat, descendantsAverageBlockMat,
      descendantsAverageMat, toFullBlockMat]

theorem descendantsAverageFullBlockMat_eq_smul_sum
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → FullBlockMat d) :
    descendantsAverageFullBlockMat Q j F =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ •
        (descendantsAtDepth Q j).sum F := by
  ext α β
  simp [descendantsAverageFullBlockMat, descendantsAverage, Matrix.sum_apply]

theorem descendantsAverageFullBlockMat_const
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (M : FullBlockMat d) :
    descendantsAverageFullBlockMat Q j (fun _ => M) = M := by
  ext α β
  simp [descendantsAverageFullBlockMat]

theorem descendantsAverageFullBlockMat_sub
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → FullBlockMat d) :
    descendantsAverageFullBlockMat Q j (fun R => F R - G R) =
      descendantsAverageFullBlockMat Q j F -
        descendantsAverageFullBlockMat Q j G := by
  rw [descendantsAverageFullBlockMat_eq_smul_sum,
    descendantsAverageFullBlockMat_eq_smul_sum,
    descendantsAverageFullBlockMat_eq_smul_sum]
  simp [Finset.sum_sub_distrib, smul_sub]

private def diagonalCongrLinearMap {d : ℕ} (D : FullBlockMat d) :
    FullBlockMat d →ₗ[ℝ] FullBlockMat d where
  toFun M := D * M * D
  map_add' M N := by
    simp [mul_add, add_mul]
  map_smul' c M := by
    simp

private def transposeCongrLinearMap {d : ℕ} (S : FullBlockMat d) :
    FullBlockMat d →ₗ[ℝ] FullBlockMat d where
  toFun M := Matrix.transpose S * M * S
  map_add' M N := by
    simp [mul_add, add_mul]
  map_smul' c M := by
    simp

theorem descendantsAverageFullBlockMat_linearMap
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (L : FullBlockMat d →ₗ[ℝ] FullBlockMat d)
    (F : TriadicCube d → FullBlockMat d) :
    descendantsAverageFullBlockMat Q j (fun R => L (F R)) =
      L (descendantsAverageFullBlockMat Q j F) := by
  rw [descendantsAverageFullBlockMat_eq_smul_sum,
    descendantsAverageFullBlockMat_eq_smul_sum]
  simp

theorem descendantsAverageFullBlockMat_diagonal_sub_const_mul_diagonal
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (D C : FullBlockMat d) (F : TriadicCube d → FullBlockMat d) :
    descendantsAverageFullBlockMat Q j
        (fun R => D * (F R - C) * D) =
      D * (descendantsAverageFullBlockMat Q j F - C) * D := by
  let L := diagonalCongrLinearMap (d := d) D
  calc
    descendantsAverageFullBlockMat Q j
        (fun R => D * (F R - C) * D)
        = descendantsAverageFullBlockMat Q j (fun R => L (F R - C)) := rfl
    _ = L (descendantsAverageFullBlockMat Q j (fun R => F R - C)) :=
          descendantsAverageFullBlockMat_linearMap Q j L (fun R => F R - C)
    _ = L (descendantsAverageFullBlockMat Q j F -
          descendantsAverageFullBlockMat Q j (fun _ => C)) := by
          rw [descendantsAverageFullBlockMat_sub]
    _ = D * (descendantsAverageFullBlockMat Q j F - C) * D := by
          simp [L, diagonalCongrLinearMap, descendantsAverageFullBlockMat_const]

theorem descendantsAverageFullBlockMat_transpose_sub_const_mul
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (S C : FullBlockMat d) (F : TriadicCube d → FullBlockMat d) :
    descendantsAverageFullBlockMat Q j
        (fun R => Matrix.transpose S * (F R - C) * S) =
      Matrix.transpose S * (descendantsAverageFullBlockMat Q j F - C) * S := by
  let L := transposeCongrLinearMap (d := d) S
  calc
    descendantsAverageFullBlockMat Q j
        (fun R => Matrix.transpose S * (F R - C) * S)
        = descendantsAverageFullBlockMat Q j (fun R => L (F R - C)) := rfl
    _ = L (descendantsAverageFullBlockMat Q j (fun R => F R - C)) :=
          descendantsAverageFullBlockMat_linearMap Q j L (fun R => F R - C)
    _ = L (descendantsAverageFullBlockMat Q j F -
          descendantsAverageFullBlockMat Q j (fun _ => C)) := by
          rw [descendantsAverageFullBlockMat_sub]
    _ = Matrix.transpose S * (descendantsAverageFullBlockMat Q j F - C) * S := by
          simp [L, transposeCongrLinearMap, descendantsAverageFullBlockMat_const]

theorem normalizedCoarseAveragePositiveErrorMatrix_eq_diagonal_blockSub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let D : FullBlockMat d :=
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    normalizedCoarseAveragePositiveErrorMatrix hP hStruct center Q j a =
      D *
        (toFullBlockMat
            (descendantsAverageBlockMat Q j
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
          toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) *
        D := by
  classical
  intro b c D
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  let F : TriadicCube d → FullBlockMat d :=
    fun R => toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun)
  have hAvg :
      descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a =
        D * (descendantsAverageFullBlockMat Q j F - Abar) * D := by
    simpa [descendantsAverageNormalizedFluctuationMatrix, F, Abar,
      Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix,
      D, b, c] using
      descendantsAverageFullBlockMat_diagonal_sub_const_mul_diagonal
        (Q := Q) (j := j) D Abar F
  have hParent :
      Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
          hP hStruct center (cubeSet Q) a =
        D * (F Q - Abar) * D := by
    simp [F, Abar, Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix,
      D, b, c]
  calc
    normalizedCoarseAveragePositiveErrorMatrix hP hStruct center Q j a
        = D * (descendantsAverageFullBlockMat Q j F - Abar) * D -
            D * (F Q - Abar) * D := by
          simp [normalizedCoarseAveragePositiveErrorMatrix, hAvg, hParent]
    _ = D * (descendantsAverageFullBlockMat Q j F - F Q) * D := by
          noncomm_ring
    _ =
        D *
          (toFullBlockMat
              (descendantsAverageBlockMat Q j
                (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) *
          D := by
          rw [toFullBlockMat_descendantsAverageBlockMat]

theorem coarseAveragePositiveErrorMatrixWithNormalizer_eq_transpose_blockSub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) :
    coarseAveragePositiveErrorMatrixWithNormalizer hP hStruct center S Q j a =
      Matrix.transpose S *
        (toFullBlockMat
            (descendantsAverageBlockMat Q j
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
          toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) *
        S := by
  classical
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  let F : TriadicCube d → FullBlockMat d :=
    fun R => toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun)
  have hAvg :
      descendantsAverageFluctuationMatrixWithNormalizer hP hStruct center S Q j a =
        Matrix.transpose S * (descendantsAverageFullBlockMat Q j F - Abar) * S := by
    simpa [descendantsAverageFluctuationMatrixWithNormalizer,
      fullBlockFluctuationMatrixWithNormalizer, F, Abar] using
      descendantsAverageFullBlockMat_transpose_sub_const_mul
        (Q := Q) (j := j) S Abar F
  have hParent :
      fullBlockFluctuationMatrixWithNormalizer hP hStruct center S (cubeSet Q) a =
        Matrix.transpose S * (F Q - Abar) * S := by
    simp [F, Abar, fullBlockFluctuationMatrixWithNormalizer]
  calc
    coarseAveragePositiveErrorMatrixWithNormalizer hP hStruct center S Q j a
        = Matrix.transpose S * (descendantsAverageFullBlockMat Q j F - Abar) * S -
            Matrix.transpose S * (F Q - Abar) * S := by
          simp [coarseAveragePositiveErrorMatrixWithNormalizer, hAvg, hParent]
    _ = Matrix.transpose S * (descendantsAverageFullBlockMat Q j F - F Q) * S := by
          noncomm_ring
    _ =
        Matrix.transpose S *
          (toFullBlockMat
              (descendantsAverageBlockMat Q j
                (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) *
          S := by
          rw [toFullBlockMat_descendantsAverageBlockMat]
end

end Section56
end Ch05
end Book
end Homogenization
