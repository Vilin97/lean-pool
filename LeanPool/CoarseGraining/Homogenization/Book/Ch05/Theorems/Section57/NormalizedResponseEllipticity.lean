/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitJTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.SmallTail

/-! # Normalized Response Ellipticity -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped BigOperators MatrixOrder

/-!
# Normalized response from coarse ellipticity

This file supplies the deterministic estimate used to control negative-scale sampled
responses in the finite-`q` homogenization-error corollary.  The estimate is
pointwise and contains no stochastic input.
-/

noncomputable section

/-- The two scalar normalizers used in the normalized response are dual. -/
theorem blockVecDot_scalarConstantNormalizers_eq_fullBlockVecNormSq
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ : 0 < σ) (e : FullBlockVec d) :
    blockVecDot
        (ofFullBlockVec
          (Matrix.mulVec
            (Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) σ)) e))
        (ofFullBlockVec
          (Matrix.mulVec
            (Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) σ)) e)) =
      Ch02.fullBlockVecNormSq e := by
  rw [← dotProduct_toFullBlockVec]
  rw [toFullBlockVec_ofFullBlockVec, toFullBlockVec_ofFullBlockVec]
  rw [constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt hσ]
  rw [constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt hσ]
  unfold dotProduct Ch02.fullBlockVecNormSq
  refine Finset.sum_congr rfl ?_
  intro α _hα
  cases α with
  | inl i =>
      simp [Matrix.mulVec, Ch04.scalarFullBlockInvSqrtDiag,
        Section56.scalarFullBlockSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
  | inr i =>
      simp [Matrix.mulVec, Ch04.scalarFullBlockInvSqrtDiag,
        Section56.scalarFullBlockSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]

/-- One-cube normalized response is bounded by the scalar-weighted coarse
ellipticity of that cube. -/
theorem normalizedBlockResponseMax_scalarMatrix_le_weightedCoarseEllipticity
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    {σ : ℝ} (hσ : 0 < σ) :
    Ch02.normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        (σ⁻¹ * Ch02.coarseBMatrixNorm Q a +
          σ * Ch02.coarseSigmaStarInvMatrixNorm Q a) := by
  classical
  let A : BlockMat d := Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (a.coeffOn Q)
  let W : ℝ :=
    σ⁻¹ * Ch02.coarseBMatrixNorm Q a +
      σ * Ch02.coarseSigmaStarInvMatrixNorm Q a
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  have hB_nonneg : 0 ≤ Ch02.coarseBMatrixNorm Q a :=
    Ch02.coarseBMatrixNorm_nonneg Q a
  have hS_nonneg : 0 ≤ Ch02.coarseSigmaStarInvMatrixNorm Q a :=
    Ch02.coarseSigmaStarInvMatrixNorm_nonneg Q a
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact add_nonneg
      (mul_nonneg (inv_pos.mpr hσ).le hB_nonneg)
      (mul_nonneg hσ.le hS_nonneg)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hSymm : IsSymmetricBlockMat A := by
    dsimp [A]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q) (a.coeffOn Q)
  have hPos : Ch02.BlockPosDef A := by
    dsimp [A]
    exact (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q)
      (a.coeffOn Q)).block_matrix_posDef
  have hUL :
      ∀ i j : Fin d, |A.upperLeft i j| ≤ Ch02.coarseBMatrixNorm Q a := by
    intro i j
    dsimp [A, Ch02.coarseBMatrixNorm]
    simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
      Ch02.abs_entry_le_matrixOperatorNorm
        (Ch02.bCoarse (Ch02.cubeDomain Q) (a.coeffOn Q)) i j
  have hLR :
      ∀ i j : Fin d,
        |A.lowerRight i j| ≤ Ch02.coarseSigmaStarInvMatrixNorm Q a := by
    intro i j
    dsimp [A, Ch02.coarseSigmaStarInvMatrixNorm]
    simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
      Ch02.abs_entry_le_matrixOperatorNorm
        (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) (a.coeffOn Q)) i j
  unfold Ch02.normalizedBlockResponseMax
  refine csSup_le
    (Ch02.normalizedBlockResponseValueSet_nonempty Q a (scalarMatrix (d := d) σ)) ?_
  rintro y ⟨e, he, rfl⟩
  let D : FullBlockMat d :=
    Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ)
  let T : FullBlockMat d :=
    Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) σ σ)
  let Pvec : BlockVec d :=
    ofFullBlockVec
      (Matrix.mulVec
        (Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) σ)) e)
  let Qvec : BlockVec d :=
    ofFullBlockVec
      (Matrix.mulVec
        (Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) σ)) e)
  have he_dot : dotProduct e e ≤ 1 := by
    have heq : dotProduct e e = Ch02.fullBlockVecNormSq e := by
      simp [dotProduct, Ch02.fullBlockVecNormSq, pow_two]
    rw [heq, he]
  have hcoord : ∀ α : BlockCoord d, |e α| ≤ 1 :=
    abs_fullBlockVec_coord_le_one_of_dotProduct_le_one e he_dot
  have hentryD :
      ∀ α β : BlockCoord d, |(D * toFullBlockMat A * D) α β| ≤ W := by
    intro α β
    simpa [D, W] using
      abs_invSqrtConj_toFullBlockMat_entry_le_weighted
        (A := A) (L := σ)
        (Λ := Ch02.coarseBMatrixNorm Q a)
        (I := Ch02.coarseSigmaStarInvMatrixNorm Q a)
        hSymm hPos hσ hB_nonneg hS_nonneg hUL hLR α β
  have hentryT :
      ∀ α β : BlockCoord d,
        |(T * toFullBlockMat (blockReflect A) * T) α β| ≤ W := by
    intro α β
    simpa [T, W] using
      abs_sqrtConj_reflect_toFullBlockMat_entry_le_weighted
        (A := A) (L := σ)
        (Λ := Ch02.coarseBMatrixNorm Q a)
        (I := Ch02.coarseSigmaStarInvMatrixNorm Q a)
        hSymm hPos hσ hB_nonneg hS_nonneg hUL hLR α β
  have hquadD_abs :
      |Ch04.fullBlockQuadraticCh04 (D * toFullBlockMat A * D) e| ≤ C * W := by
    simpa [C] using
      abs_fullBlockQuadraticCh04_le_card_sq_mul_of_entry_abs_le
        (D * toFullBlockMat A * D) e hW_nonneg hentryD hcoord
  have hquadT_abs :
      |Ch04.fullBlockQuadraticCh04 (T * toFullBlockMat (blockReflect A) * T) e|
        ≤ C * W := by
    simpa [C] using
      abs_fullBlockQuadraticCh04_le_card_sq_mul_of_entry_abs_le
        (T * toFullBlockMat (blockReflect A) * T) e hW_nonneg hentryT hcoord
  have hPquad :
      blockVecDot Pvec (blockMatVecMul A Pvec) ≤ C * W := by
    have hq :=
      fullBlockQuadraticCh04_diagonal_toFullBlockMat
        (Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ) A e
    have hEq :
        blockVecDot Pvec (blockMatVecMul A Pvec) =
          Ch04.fullBlockQuadraticCh04 (D * toFullBlockMat A * D) e := by
      rw [← Ch04.fullBlockQuadraticCh04_toFullBlockMat A Pvec]
      simpa [Pvec, D,
        constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt hσ]
        using hq
    rw [hEq]
    exact (le_abs_self _).trans hquadD_abs
  have hQquad :
      blockVecDot Qvec (blockMatVecMul (blockReflect A) Qvec) ≤ C * W := by
    have hq :=
      fullBlockQuadraticCh04_diagonal_toFullBlockMat
        (Section56.scalarFullBlockSqrtDiag (d := d) σ σ) (blockReflect A) e
    have hEq :
        blockVecDot Qvec (blockMatVecMul (blockReflect A) Qvec) =
          Ch04.fullBlockQuadraticCh04
            (T * toFullBlockMat (blockReflect A) * T) e := by
      rw [← Ch04.fullBlockQuadraticCh04_toFullBlockMat (blockReflect A) Qvec]
      simpa [Qvec, T,
        constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt hσ]
        using hq
    rw [hEq]
    exact (le_abs_self _).trans hquadT_abs
  have hpair_nonneg : 0 ≤ blockVecDot Pvec Qvec := by
    have hpair :=
      blockVecDot_scalarConstantNormalizers_eq_fullBlockVecNormSq
        (d := d) hσ e
    rw [show blockVecDot Pvec Qvec = Ch02.fullBlockVecNormSq e by
      simpa [Pvec, Qvec] using hpair]
    rw [he]
    norm_num
  have hsplit :=
    (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q) (a.coeffOn Q)).doubled_response_splitting
      Pvec Qvec
  have hreflect :=
    (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q) (a.coeffOn Q)).starred_inverse_formula
  calc
    Ch02.doubledResponseJ (Ch02.cubeDomain Q) (a.coeffOn Q) Pvec Qvec
        =
          (1 / 2 : ℝ) * blockVecDot Pvec (blockMatVecMul A Pvec) +
            (1 / 2 : ℝ) * blockVecDot Qvec (blockMatVecMul (blockReflect A) Qvec) -
              blockVecDot Pvec Qvec := by
          rw [hsplit]
          rw [hreflect]
    _ ≤ C * W := by
          nlinarith

/-- Descendant-scale normalized response is bounded by the corresponding
weighted descendant ellipticity maxima. -/
theorem maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_weightedEllipticity
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
        (scalarMatrix (d := d) σ) ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        (σ⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k a +
          σ * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a) := by
  classical
  let W : ℝ :=
    σ⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k a +
      σ * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  unfold Ch02.maxDescendantNormalizedBlockResponseAtScale Ch02.finsetSupReal
  have hne :
      ((fun R => Ch02.normalizedBlockResponseMax R a (scalarMatrix (d := d) σ)) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases hD with ⟨R, hR⟩
    exact ⟨Ch02.normalizedBlockResponseMax R a (scalarMatrix (d := d) σ),
      ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro y ⟨R, hR, rfl⟩
  have hRone :=
    normalizedBlockResponseMax_scalarMatrix_le_weightedCoarseEllipticity
      R a hσ
  have hB :
      Ch02.coarseBMatrixNorm R a ≤
        Ch02.maxDescendantBMatrixNormAtScale Q k a :=
    Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale
      a hR
  have hS :
      Ch02.coarseSigmaStarInvMatrixNorm R a ≤
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a :=
    Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
      a hR
  have hweighted :
      σ⁻¹ * Ch02.coarseBMatrixNorm R a +
          σ * Ch02.coarseSigmaStarInvMatrixNorm R a ≤ W := by
    dsimp [W]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hB (inv_pos.mpr hσ).le)
      (mul_le_mul_of_nonneg_left hS hσ.le)
  exact hRone.trans (mul_le_mul_of_nonneg_left hweighted hC_nonneg)

/-- Square-root scale-response form of
`maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_weightedEllipticity`. -/
theorem scaleResponseAtScale_scalarMatrix_le_sqrt_weightedEllipticity
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    Ch02.scaleResponseAtScale Q k Ch02.MultiscaleExponent.infinity a
        (scalarMatrix (d := d) σ) ≤
      Real.sqrt
        ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          (σ⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k a +
            σ * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a)) := by
  have hmax :=
    maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_weightedEllipticity
      Q hk a hσ
  calc
    Ch02.scaleResponseAtScale Q k Ch02.MultiscaleExponent.infinity a
        (scalarMatrix (d := d) σ)
        =
          Real.sqrt
            (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
              (scalarMatrix (d := d) σ)) := by
            rw [Ch02.scaleResponseAtScale_infinity_eq]
            simp [Real.sqrt_eq_rpow]
    _ ≤
        Real.sqrt
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
            (σ⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k a +
              σ * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a)) :=
          Real.sqrt_le_sqrt hmax

/-- One negative-scale row of the scalar-normalized response is controlled by
the two Ch2 unit-ellipticity square-root rows. -/
theorem weighted_scaleResponseAtScale_originCube_neg_nat_scalarMatrix_le_ellipticityRows
    {d : ℕ} [NeZero d]
    (m j : ℕ) {s σ : ℝ} (hs : 0 ≤ s) (hσ : 0 < σ)
    (a : Ch02.TriadicCoeffFamily d) :
    Ch02.geometricWeight s 1 (j + m) *
        Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
      Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        (Real.sqrt σ⁻¹ *
            (Ch02.geometricWeight s 1 (j + m) *
              Real.rpow
                (Ch02.maxDescendantBMatrixNormAtScale
                  (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ)) a)
                (1 / 2 : ℝ)) +
          Real.sqrt σ *
            (Ch02.geometricWeight s 1 (j + m) *
              Real.rpow
                (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                  (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ)) a)
                (1 / 2 : ℝ))) := by
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let B : ℝ := Ch02.maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a
  let I : ℝ := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let w : ℝ := Ch02.geometricWeight s 1 (j + m)
  have hk : -(j : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    omega
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q hk a
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk a
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    simpa [Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_nonneg
        (s := s) (q := 1) (j + m) (by simpa using hs)
  have hinv_nonneg : 0 ≤ σ⁻¹ := (inv_pos.mpr hσ).le
  have hσ_nonneg : 0 ≤ σ := hσ.le
  have htermB_nonneg : 0 ≤ σ⁻¹ * B := mul_nonneg hinv_nonneg hB_nonneg
  have htermI_nonneg : 0 ≤ σ * I := mul_nonneg hσ_nonneg hI_nonneg
  have hscale :
      Ch02.scaleResponseAtScale Q (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
        Real.sqrt (C * (σ⁻¹ * B + σ * I)) := by
    simpa [Q, B, I, C] using
      scaleResponseAtScale_scalarMatrix_le_sqrt_weightedEllipticity
        Q hk a hσ
  have hsqrt_split :
      Real.sqrt (C * (σ⁻¹ * B + σ * I)) ≤
        Real.sqrt C *
          (Real.sqrt σ⁻¹ * Real.rpow B (1 / 2 : ℝ) +
            Real.sqrt σ * Real.rpow I (1 / 2 : ℝ)) := by
    calc
      Real.sqrt (C * (σ⁻¹ * B + σ * I))
          = Real.sqrt C * Real.sqrt (σ⁻¹ * B + σ * I) := by
              exact Real.sqrt_mul hC_nonneg _
      _ ≤ Real.sqrt C *
            (Real.sqrt (σ⁻¹ * B) + Real.sqrt (σ * I)) := by
              exact mul_le_mul_of_nonneg_left
                (sqrt_add_le_add_sqrt_of_nonneg htermB_nonneg htermI_nonneg)
                (Real.sqrt_nonneg C)
      _ =
          Real.sqrt C *
            (Real.sqrt σ⁻¹ * Real.rpow B (1 / 2 : ℝ) +
              Real.sqrt σ * Real.rpow I (1 / 2 : ℝ)) := by
              rw [Real.sqrt_mul hinv_nonneg, Real.sqrt_mul hσ_nonneg]
              simp [Real.sqrt_eq_rpow]
  calc
    w * Ch02.scaleResponseAtScale Q (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ)
        ≤ w *
            (Real.sqrt C *
              (Real.sqrt σ⁻¹ * Real.rpow B (1 / 2 : ℝ) +
                Real.sqrt σ * Real.rpow I (1 / 2 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (hscale.trans hsqrt_split) hw_nonneg
    _ =
      Real.sqrt C *
        (Real.sqrt σ⁻¹ *
            (w * Real.rpow B (1 / 2 : ℝ)) +
          Real.sqrt σ *
            (w * Real.rpow I (1 / 2 : ℝ))) := by
        ring

end

end Section57
end Ch05
end Book
end Homogenization
