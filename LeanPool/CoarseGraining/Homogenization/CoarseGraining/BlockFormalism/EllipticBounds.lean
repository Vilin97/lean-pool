/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.MatrixIdentities

/-! # Elliptic Bounds -/

namespace Homogenization

/-!
# Block formalism -- symmetric and elliptic matrix bounds

Symmetric block-matrix identities, symmPartInv lower / upper bound and
positivity under IsEllipticMatrix, blockMatrixOfCoeff_half_quadratic_ge_vecDot,
blockMatrixOfCoeff_quadratic positivity / lower / upper / plainUpperBound,
coercivity, and the image bounds used by the response functional.
-/

theorem blockMatrixOfCoeff_upperLeft_isSymm {d : ℕ} (A : Mat d) :
    matTranspose (blockMatrixOfCoeff A).upperLeft = (blockMatrixOfCoeff A).upperLeft := by
  change
    Matrix.transpose
        (symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A) =
      symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv]
  rw [show Matrix.transpose (symmPart A) = symmPart A by
        simpa [matTranspose] using (matTranspose_symmPart A)]
  simp [matTranspose, Matrix.mul_assoc]

theorem blockMatrixOfCoeff_upperRight_transpose {d : ℕ} (A : Mat d) :
    matTranspose (blockMatrixOfCoeff A).upperRight = (blockMatrixOfCoeff A).lowerLeft := by
  change Matrix.transpose (-((matTranspose (skewPart A)) * (symmPart A)⁻¹)) =
      -((symmPart A)⁻¹ * skewPart A)
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  rw [show Matrix.transpose (symmPart A) = symmPart A by
        simpa [matTranspose] using (matTranspose_symmPart A)]
  simp [matTranspose]

theorem blockMatrixOfCoeff_lowerRight_isSymm {d : ℕ} (A : Mat d) :
    matTranspose (blockMatrixOfCoeff A).lowerRight = (blockMatrixOfCoeff A).lowerRight := by
  change Matrix.transpose ((symmPart A)⁻¹) = (symmPart A)⁻¹
  rw [Matrix.transpose_nonsing_inv]
  rw [show Matrix.transpose (symmPart A) = symmPart A by
        simpa [matTranspose] using (matTranspose_symmPart A)]

theorem isSymm_toFullBlockMat_of_isSymmetricBlockMat {d : ℕ} {B : BlockMat d}
    (hB : IsSymmetricBlockMat B) : (toFullBlockMat B).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat, blockMatEntry] using (hB (Sum.inl i) (Sum.inl j)).symm
      | inr j =>
          simpa [toFullBlockMat, blockMatEntry] using (hB (Sum.inl i) (Sum.inr j)).symm
  | inr i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat, blockMatEntry] using (hB (Sum.inr i) (Sum.inl j)).symm
      | inr j =>
          simpa [toFullBlockMat, blockMatEntry] using (hB (Sum.inr i) (Sum.inr j)).symm

theorem blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat {d : ℕ} {B : BlockMat d}
    (hB : IsSymmetricBlockMat B) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul B Y) = blockVecDot Y (blockMatVecMul B X) := by
  let M := toFullBlockMat B
  have hM : M.IsSymm := by
    simpa [M] using isSymm_toFullBlockMat_of_isSymmetricBlockMat hB
  calc
    blockVecDot X (blockMatVecMul B Y)
      = dotProduct (toFullBlockVec X) (Matrix.mulVec M (toFullBlockVec Y)) := by
          rw [← dotProduct_toFullBlockVec X (blockMatVecMul B Y)]
          simp [M, toFullBlockVec_blockMatVecMul]
    _ = dotProduct (Matrix.vecMul (toFullBlockVec X) M) (toFullBlockVec Y) := by
          rw [Matrix.dotProduct_mulVec]
    _ = dotProduct (Matrix.vecMul (toFullBlockVec X) (Matrix.transpose M)) (toFullBlockVec Y) := by
          rw [hM.eq]
    _ = dotProduct (Matrix.mulVec M (toFullBlockVec X)) (toFullBlockVec Y) := by
          have hvecT :
              Matrix.vecMul (toFullBlockVec X) (Matrix.transpose M) =
                Matrix.mulVec M (toFullBlockVec X) := by
            simpa using (Matrix.vecMul_transpose M (toFullBlockVec X))
          rw [hvecT]
    _ = dotProduct (toFullBlockVec Y) (Matrix.mulVec M (toFullBlockVec X)) := by
          rw [dotProduct_comm]
    _ = blockVecDot Y (blockMatVecMul B X) := by
          rw [← toFullBlockVec_blockMatVecMul B X, dotProduct_toFullBlockVec]

theorem isSymmetricBlockMat_blockMatrixOfCoeff {d : ℕ} (A : Mat d) :
    IsSymmetricBlockMat (blockMatrixOfCoeff A) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have h := congrArg (fun M => M i j) (blockMatrixOfCoeff_upperLeft_isSymm A)
          simpa [matTranspose, blockMatEntry, blockMatrixOfCoeff] using h.symm
      | inr j =>
          have h := congrArg (fun M => M j i) (blockMatrixOfCoeff_upperRight_transpose A)
          simpa [matTranspose, blockMatEntry, blockMatrixOfCoeff] using h
  | inr i =>
      cases β with
      | inl j =>
          have h := congrArg (fun M => M i j) (blockMatrixOfCoeff_upperRight_transpose A)
          simpa [matTranspose, blockMatEntry, blockMatrixOfCoeff] using h.symm
      | inr j =>
          have h := congrArg (fun M => M i j) (blockMatrixOfCoeff_lowerRight_isSymm A)
          simpa [matTranspose, blockMatEntry, blockMatrixOfCoeff] using h.symm

theorem blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm {d : ℕ} (A : Mat d)
    (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) Y) =
      blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff A) X) :=
  blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
    (isSymmetricBlockMat_blockMatrixOfCoeff A) X Y

theorem isUnit_symmPart_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) : IsUnit (symmPart A) := by
  exact ((symmPart A).isUnit_iff_isUnit_det).mpr
    (isUnit_det_symmPart_of_isEllipticMatrix hA)

theorem symmPart_inv_nonneg_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    0 ≤ vecDot ξ (matVecMul ((symmPart A)⁻¹) ξ) := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  rcases hA with ⟨hlam_pos, -, -, -⟩
  have hηnonneg : 0 ≤ vecNormSq η := vecNormSq_nonneg η
  have hξη_nonneg : 0 ≤ vecDot ξ η := by
    exact (mul_nonneg hlam_pos.le hηnonneg).trans hmain
  simpa [η] using hξη_nonneg

theorem lowerBound_symmPartInv_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    (lam * (Lam⁻¹ * Lam⁻¹)) * vecNormSq ξ ≤
      vecDot ξ (matVecMul ((symmPart A)⁻¹) ξ) := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hηupper : vecNormSq ξ ≤ Lam ^ 2 * vecNormSq η := by
    simpa [s, η, hsη] using vecNormSq_matVecMul_symmPart_le_of_isEllipticMatrix hA η
  have hηlower : (Lam⁻¹ * Lam⁻¹) * vecNormSq ξ ≤ vecNormSq η := by
    rcases hA with ⟨hlam_pos, hlamLam, -, -⟩
    have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
    have hLamInvSq_nonneg : 0 ≤ Lam⁻¹ * Lam⁻¹ := by
      positivity
    have hmul :
        (Lam⁻¹ * Lam⁻¹) * vecNormSq ξ ≤
          (Lam⁻¹ * Lam⁻¹) * (Lam ^ 2 * vecNormSq η) := by
      exact mul_le_mul_of_nonneg_left hηupper hLamInvSq_nonneg
    have hcancel : (Lam⁻¹ * Lam⁻¹) * (Lam ^ 2 * vecNormSq η) = vecNormSq η := by
      field_simp [hLam_pos.ne']
    calc
      (Lam⁻¹ * Lam⁻¹) * vecNormSq ξ ≤ (Lam⁻¹ * Lam⁻¹) * (Lam ^ 2 * vecNormSq η) := hmul
      _ = vecNormSq η := hcancel
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  rcases hA with ⟨hlam_pos, -, -, -⟩
  have hscaled :
      lam * ((Lam⁻¹ * Lam⁻¹) * vecNormSq ξ) ≤ lam * vecNormSq η := by
    exact mul_le_mul_of_nonneg_left hηlower (le_of_lt hlam_pos)
  have hfinal : (lam * (Lam⁻¹ * Lam⁻¹)) * vecNormSq ξ ≤ vecDot ξ η := by
    calc
      (lam * (Lam⁻¹ * Lam⁻¹)) * vecNormSq ξ
        = lam * ((Lam⁻¹ * Lam⁻¹) * vecNormSq ξ) := by ring
      _ ≤ lam * vecNormSq η := hscaled
      _ ≤ vecDot ξ η := hmain
  simpa [η] using hfinal

theorem vecNormSq_matVecMul_symmPartInv_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul ((symmPart A)⁻¹) ξ) ≤
      (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  have hCS :
      vecDot ξ η ^ 2 ≤ vecNormSq ξ * vecNormSq η :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq ξ η
  have hξη_nonneg : 0 ≤ vecDot ξ η := symmPart_inv_nonneg_of_isEllipticMatrix hA ξ
  rcases hA with ⟨hlam_pos, -, -, -⟩
  by_cases hη0 : vecNormSq η = 0
  · rw [hη0]
    have hlam_inv_sq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := by
      positivity
    nlinarith [hlam_inv_sq_nonneg, vecNormSq_nonneg ξ]
  · have hηpos : 0 < vecNormSq η := by
      exact lt_of_le_of_ne (vecNormSq_nonneg η) (by simpa [eq_comm] using hη0)
    have hsq : (lam * vecNormSq η) ^ 2 ≤ vecNormSq ξ * vecNormSq η := by
      have hsq' : (lam * vecNormSq η) ^ 2 ≤ vecDot ξ η ^ 2 := by
        have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
        have hlamη_nonneg : 0 ≤ lam * vecNormSq η := mul_nonneg hlam_nonneg (vecNormSq_nonneg η)
        nlinarith [hmain, hξη_nonneg, hlamη_nonneg]
      exact le_trans hsq' hCS
    have hlam_sq_bound : lam ^ 2 * vecNormSq η ≤ vecNormSq ξ := by
      nlinarith [hsq, hηpos, le_of_lt hlam_pos]
    have hlam_inv_sq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := by
      positivity
    have hmul :
        (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) ≤
          (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
      exact mul_le_mul_of_nonneg_left hlam_sq_bound hlam_inv_sq_nonneg
    have hcancel : (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) = vecNormSq η := by
      field_simp [hlam_pos.ne']
    calc
      vecNormSq (matVecMul ((symmPart A)⁻¹) ξ) = vecNormSq η := by
        rfl
      _ = (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) := by
        exact hcancel.symm
      _ ≤ (lam⁻¹ * lam⁻¹) * vecNormSq ξ := hmul

theorem symmPart_inv_upperBound_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecDot ξ (matVecMul ((symmPart A)⁻¹) ξ) ≤ lam⁻¹ * vecNormSq ξ := by
  let s := symmPart A
  let η := matVecMul s⁻¹ ξ
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = ξ := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
  have hmain : lam * vecNormSq η ≤ vecDot ξ η := by
    simpa [s, η, hsη, vecDot_comm] using hlower
  have hCS :
      vecDot ξ η ^ 2 ≤ vecNormSq ξ * vecNormSq η :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq ξ η
  have hξη_nonneg : 0 ≤ vecDot ξ η := symmPart_inv_nonneg_of_isEllipticMatrix hA ξ
  rcases hA with ⟨hlam_pos, -, -, -⟩
  have hηbound : vecNormSq η ≤ (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
    by_cases hη0 : vecNormSq η = 0
    · rw [hη0]
      have hlam_inv_nonneg : 0 ≤ lam⁻¹ := by positivity
      nlinarith [hlam_inv_nonneg, vecNormSq_nonneg ξ]
    · have hηpos : 0 < vecNormSq η := by
        exact lt_of_le_of_ne (vecNormSq_nonneg η) (by simpa [eq_comm] using hη0)
      have hsq : (lam * vecNormSq η) ^ 2 ≤ vecNormSq ξ * vecNormSq η := by
        have hsq' : (lam * vecNormSq η) ^ 2 ≤ vecDot ξ η ^ 2 := by
          have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
          have hlamη_nonneg : 0 ≤ lam * vecNormSq η := mul_nonneg hlam_nonneg (vecNormSq_nonneg η)
          nlinarith [hmain, hξη_nonneg, hlamη_nonneg]
        exact le_trans hsq' hCS
      have hξnonneg : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
      have hlam_sq_bound : lam ^ 2 * vecNormSq η ≤ vecNormSq ξ := by
        nlinarith [hsq, hηpos, le_of_lt hlam_pos]
      have hlam_inv_sq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := by
        positivity
      have hmul :
          (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) ≤
            (lam⁻¹ * lam⁻¹) * vecNormSq ξ := by
        exact mul_le_mul_of_nonneg_left hlam_sq_bound hlam_inv_sq_nonneg
      have hcancel : (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) = vecNormSq η := by
        field_simp [hlam_pos.ne']
      calc
        vecNormSq η = (lam⁻¹ * lam⁻¹) * (lam ^ 2 * vecNormSq η) := by
          exact hcancel.symm
        _ ≤ (lam⁻¹ * lam⁻¹) * vecNormSq ξ := hmul
  have hmainSq : vecDot ξ η ^ 2 ≤ (lam⁻¹ * vecNormSq ξ) ^ 2 := by
    have hmul :
        vecNormSq ξ * vecNormSq η ≤ vecNormSq ξ * (((lam⁻¹ * lam⁻¹) * vecNormSq ξ)) := by
      exact mul_le_mul_of_nonneg_left hηbound (vecNormSq_nonneg ξ)
    have hsq := le_trans hCS hmul
    nlinarith
  have hright_nonneg : 0 ≤ lam⁻¹ * vecNormSq ξ := by
    have hlam_inv_nonneg : 0 ≤ lam⁻¹ := by positivity
    exact mul_nonneg hlam_inv_nonneg (vecNormSq_nonneg ξ)
  have habs : |vecDot ξ η| ≤ |lam⁻¹ * vecNormSq ξ| := by
    exact sq_le_sq.mp hmainSq
  have hleft_abs : |vecDot ξ η| = vecDot ξ η := abs_of_nonneg hξη_nonneg
  have hright_abs : |lam⁻¹ * vecNormSq ξ| = lam⁻¹ * vecNormSq ξ :=
    abs_of_nonneg hright_nonneg
  simpa [η] using (show vecDot ξ η ≤ lam⁻¹ * vecNormSq ξ by nlinarith [habs, hleft_abs, hright_abs])

theorem vecDot_matVecMul_skewPart_self_eq_zero {d : ℕ} (A : Mat d) (p : Vec d) :
    vecDot p (matVecMul (skewPart A) p) = 0 := by
  have htranspose :
      vecDot p (matVecMul (matTranspose (skewPart A)) p) =
        vecDot p (matVecMul (skewPart A) p) := by
    rw [vecDot_matVecMul_transpose]
    rw [vecDot_comm]
  have hneg :
      vecDot p (matVecMul (skewPart A) p) =
        -vecDot p (matVecMul (skewPart A) p) := by
    calc
      vecDot p (matVecMul (skewPart A) p)
        = vecDot p (matVecMul (matTranspose (skewPart A)) p) := by
            exact htranspose.symm
      _ = vecDot p (matVecMul (-skewPart A) p) := by
            rw [matTranspose_skewPart]
      _ = -vecDot p (matVecMul (skewPart A) p) := by
            rw [neg_matVecMul, vecDot_neg_right]
  linarith

theorem blockMatrixOfCoeff_half_quadratic_ge_vecDot_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    vecDot p q ≤
      (1 / 2 : ℝ) * blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
  let s := symmPart A
  let r := q - matVecMul (skewPart A) p
  let η := matVecMul s⁻¹ r
  have hs : IsUnit s := isUnit_symmPart_of_isEllipticMatrix hA
  have hsdet : IsUnit s.det := (Matrix.isUnit_iff_isUnit_det (A := s)).mp hs
  have hsη : matVecMul s η = r := by
    dsimp [η]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv s hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hp_nonneg : 0 ≤ vecDot p (matVecMul s p) := by
    have hp_lower := lowerBound_symmPart_of_isEllipticMatrix hA p
    rcases hA with ⟨hlam_pos, -, -, -⟩
    exact (mul_nonneg hlam_pos.le (vecNormSq_nonneg p)).trans hp_lower
  have hr_nonneg : 0 ≤ vecDot r (matVecMul s⁻¹ r) := by
    simpa [s] using symmPart_inv_nonneg_of_isEllipticMatrix hA r
  have hsq :
      vecDot p r ^ 2 ≤
        vecDot p (matVecMul s p) * vecDot r (matVecMul s⁻¹ r) := by
    have hsymm :
        vecDot p (matVecMul s η) ^ 2 ≤
          vecDot p (matVecMul s p) * vecDot η (matVecMul s η) := by
      simpa [s] using sq_vecDot_matVecMul_symmPart_le_of_isEllipticMatrix hA p η
    simpa [η, hsη, vecDot_comm] using hsymm
  have hyoung :
      2 * vecDot p r ≤ vecDot p (matVecMul s p) + vecDot r (matVecMul s⁻¹ r) := by
    have hsq_nonneg :
        0 ≤ (vecDot p (matVecMul s p) - vecDot r (matVecMul s⁻¹ r)) ^ 2 := by
      positivity
    nlinarith
  have hpair : vecDot p q = vecDot p r := by
    dsimp [r]
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right,
      vecDot_matVecMul_skewPart_self_eq_zero]
    ring
  calc
    vecDot p q = vecDot p r := hpair
    _ ≤ (1 / 2 : ℝ) * (vecDot p (matVecMul s p) + vecDot r (matVecMul s⁻¹ r)) := by
          nlinarith
    _ =
        (1 / 2 : ℝ) * blockVecDot (p, q)
          (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
          rw [blockMatrixOfCoeff_quadratic_eq]

theorem blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} {p q : Vec d} (hA : IsEllipticMatrix lam Lam A) (hpq : (p, q) ≠ 0) :
    0 < blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
  let r := q - matVecMul (skewPart A) p
  rw [blockMatrixOfCoeff_quadratic_eq]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq0
      apply hpq
      ext <;> simp [hp, hq0]
    have hr : r = q := by
      simp [r, hp, matVecMul_zero]
    have hqnorm : 0 < vecNormSq q := by
      have hqnorm_ne : vecNormSq q ≠ 0 := by
        intro hqnorm0
        apply hq
        exact vecNormSq_eq_zero hqnorm0
      exact lt_of_le_of_ne (vecNormSq_nonneg q) (by simpa [eq_comm] using hqnorm_ne)
    have hterm_pos :
        0 < vecDot q (matVecMul ((symmPart A)⁻¹) q) := by
      have hlam_pos : 0 < lam := hA.1
      let η := matVecMul ((symmPart A)⁻¹) q
      have hs : IsUnit (symmPart A) := isUnit_symmPart_of_isEllipticMatrix hA
      have hsdet : IsUnit (symmPart A).det :=
        (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp hs
      have hsη : matVecMul (symmPart A) η = q := by
        dsimp [η]
        rw [matVecMul_mul, Matrix.mul_nonsing_inv (symmPart A) hsdet]
        funext i
        simp [matVecMul, Matrix.one_apply]
      have hηne : η ≠ 0 := by
        intro hη0
        apply hq
        simpa [η, hη0, matVecMul_zero] using hsη.symm
      have hηnorm_pos : 0 < vecNormSq η := by
        have hηnorm_ne : vecNormSq η ≠ 0 := by
          intro hηnorm0
          apply hηne
          exact vecNormSq_eq_zero hηnorm0
        exact lt_of_le_of_ne (vecNormSq_nonneg η) (by simpa [eq_comm] using hηnorm_ne)
      have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
      have hmain : lam * vecNormSq η ≤ vecDot q η := by
        simpa [η, hsη, vecDot_comm] using hlower
      exact lt_of_lt_of_le (mul_pos hlam_pos hηnorm_pos) hmain
    simpa [hp, hr, matVecMul_zero, vecDot_zero_left] using hterm_pos
  · have hpnorm : 0 < vecNormSq p := by
      have hpnorm_ne : vecNormSq p ≠ 0 := by
        intro hpnorm0
        apply hp
        exact vecNormSq_eq_zero hpnorm0
      exact lt_of_le_of_ne (vecNormSq_nonneg p) (by simpa [eq_comm] using hpnorm_ne)
    have hpterm :=
      lowerBound_symmPart_of_isEllipticMatrix hA p
    have hrterm_nonneg :=
      symmPart_inv_nonneg_of_isEllipticMatrix hA r
    rcases hA with ⟨hlam_pos, -, -, -⟩
    have hpterm_pos : 0 < vecDot p (matVecMul (symmPart A) p) := by
      exact lt_of_lt_of_le (mul_pos hlam_pos hpnorm) hpterm
    nlinarith [blockMatrixOfCoeff_quadratic_eq (A := A) (p := p) (q := q), hpterm_pos,
      hrterm_nonneg]

theorem blockMatrixOfCoeff_quadratic_lowerBound_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (p, q) (p, q) ≤
      blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
  let r := q - matVecMul (skewPart A) p
  let kp := matVecMul (skewPart A) p
  have hpterm := lowerBound_symmPart_of_isEllipticMatrix hA p
  have hrterm := lowerBound_symmPartInv_of_isEllipticMatrix hA r
  have hqbound :
      vecNormSq q ≤ 2 * vecNormSq r + 2 * Lam ^ 2 * vecNormSq p := by
    have hqeq : q = r + kp := by
      simp [r, kp, sub_eq_add_neg, add_assoc]
    have hsub : vecNormSq q ≤ 2 * (vecNormSq r + vecNormSq kp) := by
      rw [hqeq]
      exact vecNormSq_add_le r kp
    have hskew := vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA p
    nlinarith
  have hnorm :
      blockVecDot (p, q) (p, q) ≤ (1 + 2 * Lam ^ 2) * vecNormSq p + 2 * vecNormSq r := by
    change vecNormSq p + vecNormSq q ≤ (1 + 2 * Lam ^ 2) * vecNormSq p + 2 * vecNormSq r
    nlinarith
  let c : ℝ := lam / (1 + 2 * Lam ^ 2)
  have hc_nonneg : 0 ≤ c := by
    rcases hA with ⟨hlam_pos, -, -, -⟩
    dsimp [c]
    positivity
  have hc_p : c * ((1 + 2 * Lam ^ 2) * vecNormSq p) = lam * vecNormSq p := by
    rcases hA with ⟨hlam_pos, hlamLam, -, -⟩
    have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
    have hden_ne : 1 + 2 * Lam ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg Lam]
    dsimp [c]
    field_simp [hden_ne]
  have hc_r : 2 * c ≤ lam * (Lam⁻¹ * Lam⁻¹) := by
    rcases hA with ⟨hlam_pos, hlamLam, -, -⟩
    have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
    have hden_ne : 1 + 2 * Lam ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg Lam]
    dsimp [c]
    field_simp [hLam_pos.ne', hden_ne]
    nlinarith [sq_nonneg Lam]
  have hscaled :
      c * blockVecDot (p, q) (p, q) ≤
        c * ((1 + 2 * Lam ^ 2) * vecNormSq p + 2 * vecNormSq r) := by
    exact mul_le_mul_of_nonneg_left hnorm hc_nonneg
  calc
    (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (p, q) (p, q)
      = c * blockVecDot (p, q) (p, q) := by rfl
    _ ≤ c * ((1 + 2 * Lam ^ 2) * vecNormSq p + 2 * vecNormSq r) := hscaled
    _ = lam * vecNormSq p + 2 * c * vecNormSq r := by
      rw [mul_add, hc_p]
      ring
    _ ≤ lam * vecNormSq p + (lam * (Lam⁻¹ * Lam⁻¹)) * vecNormSq r := by
      have hr_nonneg : 0 ≤ vecNormSq r := vecNormSq_nonneg r
      nlinarith
    _ ≤ blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) := by
      rw [blockMatrixOfCoeff_quadratic_eq]
      nlinarith

theorem blockMatrixOfCoeff_coercive_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    (lam / (1 + 2 * Lam ^ 2)) * blockVecDot X X ≤
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) := by
  rcases X with ⟨p, q⟩
  simpa using blockMatrixOfCoeff_quadratic_lowerBound_of_isEllipticMatrix hA p q

theorem blockMatrixOfCoeff_quadratic_upperBound_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) ≤
      Lam * vecNormSq p + lam⁻¹ * vecNormSq (q - matVecMul (skewPart A) p) := by
  rw [blockMatrixOfCoeff_quadratic_eq]
  have hpterm := upperBound_symmPart_of_isEllipticMatrix hA p
  have hqterm :=
    symmPart_inv_upperBound_of_isEllipticMatrix hA
      (q - matVecMul (skewPart A) p)
  linarith

theorem blockMatrixOfCoeff_quadratic_plainUpperBound_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) ≤
      (Lam + 2 * lam⁻¹ * Lam ^ 2) * vecNormSq p + 2 * lam⁻¹ * vecNormSq q := by
  have hupper := blockMatrixOfCoeff_quadratic_upperBound_of_isEllipticMatrix hA p q
  have hsub :
      vecNormSq (q - matVecMul (skewPart A) p) ≤
        2 * (vecNormSq q + vecNormSq (matVecMul (skewPart A) p)) :=
    vecNormSq_sub_le q (matVecMul (skewPart A) p)
  have hskew :=
    vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA p
  have hshift :
      lam⁻¹ * vecNormSq (q - matVecMul (skewPart A) p) ≤
        lam⁻¹ * (2 * (vecNormSq q + vecNormSq (matVecMul (skewPart A) p))) := by
    have hlam_pos : 0 < lam := hA.1
    have hlam_nonneg : 0 ≤ lam⁻¹ := by
      positivity
    exact mul_le_mul_of_nonneg_left hsub hlam_nonneg
  have hshift' :
      lam⁻¹ * vecNormSq (q - matVecMul (skewPart A) p) ≤
        2 * lam⁻¹ * vecNormSq q + 2 * lam⁻¹ * Lam ^ 2 * vecNormSq p := by
    have hlam_pos : 0 < lam := hA.1
    have hlam_nonneg : 0 ≤ lam⁻¹ := by
      positivity
    nlinarith [hskew, vecNormSq_nonneg q, vecNormSq_nonneg p, hlam_nonneg]
  linarith

theorem blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    q =
      matVecMul (symmPart A) ((blockMatVecMul (blockMatrixOfCoeff A) (p, q)).2) +
        matVecMul (skewPart A) p := by
  rw [blockMatVecMul_blockMatrixOfCoeff_snd]
  have hsInvMul :
      matVecMul (symmPart A)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) =
        q - matVecMul (skewPart A) p := by
    rw [matVecMul_mul]
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_symmPart_of_isEllipticMatrix hA)]
    funext i
    simp [matVecMul, Matrix.one_apply]
  calc
    q = (q - matVecMul (skewPart A) p) + matVecMul (skewPart A) p := by
      ext i
      simp [sub_eq_add_neg]
    _ = matVecMul (symmPart A)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) +
        matVecMul (skewPart A) p := by
          rw [hsInvMul]

theorem blockMatrixOfCoeff_image_plainUpperBound_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (p q : Vec d) :
    blockVecDot (blockMatVecMul (blockMatrixOfCoeff A) (p, q))
        (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) ≤
      (2 * Lam ^ 2 + 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * Lam ^ 2) * vecNormSq p +
        (2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹)) * vecNormSq q := by
  let Y := blockMatVecMul (blockMatrixOfCoeff A) (p, q)
  let lower := matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)
  have hY2 : Y.2 = lower := by
    simpa [Y, lower] using blockMatVecMul_blockMatrixOfCoeff_snd A p q
  have hY1 : Y.1 = matVecMul (symmPart A) p + matVecMul (skewPart A) lower := by
    simpa [Y, lower] using blockMatVecMul_blockMatrixOfCoeff_fst A p q
  have hlower :
      vecNormSq lower ≤
        2 * (lam⁻¹ * lam⁻¹) * vecNormSq q +
          2 * (lam⁻¹ * lam⁻¹) * Lam ^ 2 * vecNormSq p := by
    have hsInv :=
      vecNormSq_matVecMul_symmPartInv_le_of_isEllipticMatrix hA
        (q - matVecMul (skewPart A) p)
    have hsub :
        vecNormSq (q - matVecMul (skewPart A) p) ≤
          2 * (vecNormSq q + vecNormSq (matVecMul (skewPart A) p)) :=
      vecNormSq_sub_le q (matVecMul (skewPart A) p)
    have hskew := vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA p
    nlinarith
  have hupper :
      vecNormSq Y.1 ≤ 2 * Lam ^ 2 * vecNormSq p + 2 * Lam ^ 2 * vecNormSq lower := by
    rw [hY1]
    have hsymm := vecNormSq_matVecMul_symmPart_le_of_isEllipticMatrix hA p
    have hskew := vecNormSq_matVecMul_skewPart_le_of_isEllipticMatrix hA lower
    have hadd := vecNormSq_add_le (matVecMul (symmPart A) p) (matVecMul (skewPart A) lower)
    nlinarith
  calc
    blockVecDot Y Y = vecNormSq Y.1 + vecNormSq Y.2 := by
      rfl
    _ = vecNormSq Y.1 + vecNormSq lower := by rw [hY2]
    _ ≤ (2 * Lam ^ 2 * vecNormSq p + 2 * Lam ^ 2 * vecNormSq lower) + vecNormSq lower := by
      linarith
    _ ≤ (2 * Lam ^ 2 * vecNormSq p +
          2 * Lam ^ 2 *
            (2 * (lam⁻¹ * lam⁻¹) * vecNormSq q +
              2 * (lam⁻¹ * lam⁻¹) * Lam ^ 2 * vecNormSq p)) +
          (2 * (lam⁻¹ * lam⁻¹) * vecNormSq q +
            2 * (lam⁻¹ * lam⁻¹) * Lam ^ 2 * vecNormSq p) := by
      gcongr
    _ ≤ (2 * Lam ^ 2 + 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * Lam ^ 2) * vecNormSq p +
          (2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹)) * vecNormSq q := by
      nlinarith

noncomputable def blockMatrixOfCoeffNormSqBound (lam Lam : ℝ) : ℝ :=
  2 * Lam ^ 2 + 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * (Lam ^ 2 + 1)

theorem blockMatrixOfCoeff_image_bound_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (blockMatrixOfCoeff A) X)
        (blockMatVecMul (blockMatrixOfCoeff A) X) ≤
      blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot X X := by
  rcases X with ⟨p, q⟩
  have hplain := blockMatrixOfCoeff_image_plainUpperBound_of_isEllipticMatrix hA p q
  let α : ℝ := 2 * Lam ^ 2 + 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * Lam ^ 2
  let β : ℝ := 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹)
  have hlamInvSq_nonneg : 0 ≤ lam⁻¹ * lam⁻¹ := mul_self_nonneg _
  have hLamSq_nonneg : 0 ≤ Lam ^ 2 := by positivity
  have hTwo_nonneg : 0 ≤ (2 : ℝ) := by positivity
  have hLamTerm_nonneg : 0 ≤ 2 * Lam ^ 2 := by positivity
  have hFactor_nonneg : 0 ≤ 2 * Lam ^ 2 + 1 := by positivity
  have hMixed_nonneg : 0 ≤ 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * Lam ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hTwo_nonneg hFactor_nonneg) hlamInvSq_nonneg)
      hLamSq_nonneg
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact add_nonneg hLamTerm_nonneg hMixed_nonneg
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact mul_nonneg (mul_nonneg hTwo_nonneg hFactor_nonneg) hlamInvSq_nonneg
  have hp_le : α * vecNormSq p ≤ α * (vecNormSq p + vecNormSq q) := by
    refine mul_le_mul_of_nonneg_left ?_ hα_nonneg
    exact le_add_of_nonneg_right (vecNormSq_nonneg q)
  have hq_le : β * vecNormSq q ≤ β * (vecNormSq p + vecNormSq q) := by
    refine mul_le_mul_of_nonneg_left ?_ hβ_nonneg
    exact le_add_of_nonneg_left (vecNormSq_nonneg p)
  have hαβ :
      α + β = blockMatrixOfCoeffNormSqBound lam Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    dsimp [α, β]
    ring_nf
  simp only [blockVecDot] at hplain ⊢
  calc
    blockVecDot (blockMatVecMul (blockMatrixOfCoeff A) (p, q))
        (blockMatVecMul (blockMatrixOfCoeff A) (p, q))
        ≤ α * vecNormSq p + β * vecNormSq q := hplain
    _ ≤ α * (vecNormSq p + vecNormSq q) + β * (vecNormSq p + vecNormSq q) := by
      linarith
    _ = (α + β) * (vecNormSq p + vecNormSq q) := by ring
    _ = blockMatrixOfCoeffNormSqBound lam Lam * (vecNormSq p + vecNormSq q) := by
      rw [hαβ]
    _ = blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot (p, q) (p, q) := by
      rw [show blockVecDot (p, q) (p, q) = vecNormSq p + vecNormSq q by rfl]

end Homogenization
