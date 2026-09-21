/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.Basic

/-! # Diagonal Sandwich -/

namespace Homogenization

/-!
# Diagonal sandwich (A8 lower) and two-field comparison (A9)

The lower half of the diagonal sandwich A8 and the two-field comparison A9 of
Proposition 2.1 of the high-moment paper (Armstrong–Kuusi–Loher, in
preparation).  These require the block Fenchel duality: `bfA` is symmetric,
positive definite, and its inverse is the block reflection `blockReflect bfA`.
We establish that inverse identity by an explicit block-matrix computation and
feed it through a pointwise Young/Fenchel inequality.

Continuation of `SharpBlockBounds/Basic.lean`.
-/

open Homogenization.Book.Ch02

variable {d : ℕ}

/-! ## Block composition and the reflection inverse -/

/-- `blockMatMul` composes with the doubled action. -/
theorem blockMatVecMul_blockMatMul (A B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockMatMul A B) X = blockMatVecMul A (blockMatVecMul B X) := by
  rcases X with ⟨p, q⟩
  refine Prod.ext ?_ ?_
  · show matVecMul (blockMatMul A B).upperLeft p + matVecMul (blockMatMul A B).upperRight q =
        matVecMul A.upperLeft (matVecMul B.upperLeft p + matVecMul B.upperRight q) +
          matVecMul A.upperRight (matVecMul B.lowerLeft p + matVecMul B.lowerRight q)
    simp only [blockMatMul, add_matVecMul, matVecMul_add, ← matVecMul_mul]; abel
  · show matVecMul (blockMatMul A B).lowerLeft p + matVecMul (blockMatMul A B).lowerRight q =
        matVecMul A.lowerLeft (matVecMul B.upperLeft p + matVecMul B.upperRight q) +
          matVecMul A.lowerRight (matVecMul B.lowerLeft p + matVecMul B.lowerRight q)
    simp only [blockMatMul, add_matVecMul, matVecMul_add, ← matVecMul_mul]; abel

/-- The doubled block identity acts trivially. -/
theorem blockMatVecMul_blockIdentity (X : BlockVec d) :
    blockMatVecMul (blockIdentity d) X = X := by
  rcases X with ⟨p, q⟩
  refine Prod.ext ?_ ?_ <;>
    simp [blockIdentity, blockDiag, blockMatVecMul, matVecMul_one, zero_matVecMul]

/-- The block reflection is a right inverse of `bfA` at the matrix level. -/
theorem blockMatMul_blockReflect_blockMatrixOfCoeff_eq_id {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    blockMatMul (blockMatrixOfCoeff A) (blockReflect (blockMatrixOfCoeff A)) =
      blockIdentity d := by
  have hsdet : IsUnit (symmPart A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp
      (isUnit_symmPart_of_isEllipticMatrix hA)
  have hss : symmPart A * (symmPart A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hsdet
  have hss' : (symmPart A)⁻¹ * symmPart A = 1 := Matrix.nonsing_inv_mul _ hsdet
  have hkt : matTranspose (skewPart A) = -(skewPart A) := matTranspose_skewPart A
  refine blockMat_ext ?_ ?_ ?_ ?_
  · simp only [blockMatMul, blockReflect_upperLeft, blockReflect_lowerLeft,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h : (symmPart A + -skewPart A * (symmPart A)⁻¹ * skewPart A) * (symmPart A)⁻¹ +
        -(-skewPart A * (symmPart A)⁻¹) * -(-skewPart A * (symmPart A)⁻¹) =
        symmPart A * (symmPart A)⁻¹ := by noncomm_ring
    rw [h, hss]
  · simp only [blockMatMul, blockReflect_upperRight, blockReflect_lowerRight,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h : (symmPart A + -skewPart A * (symmPart A)⁻¹ * skewPart A) *
          -((symmPart A)⁻¹ * skewPart A) +
        -(-skewPart A * (symmPart A)⁻¹) *
          (symmPart A + -skewPart A * (symmPart A)⁻¹ * skewPart A) =
        -(symmPart A * (symmPart A)⁻¹ * skewPart A) +
          skewPart A * ((symmPart A)⁻¹ * symmPart A) := by noncomm_ring
    rw [h, hss, hss']; simp
  · simp only [blockMatMul, blockReflect_upperLeft, blockReflect_lowerLeft,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]; noncomm_ring
  · simp only [blockMatMul, blockReflect_upperRight, blockReflect_lowerRight,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h : -((symmPart A)⁻¹ * skewPart A) * -((symmPart A)⁻¹ * skewPart A) +
        (symmPart A)⁻¹ * (symmPart A + -skewPart A * (symmPart A)⁻¹ * skewPart A) =
        (symmPart A)⁻¹ * symmPart A := by noncomm_ring
    rw [h, hss']

/-- The reflection is a right inverse of `bfA` at the level of the doubled
action. -/
theorem blockMatVecMul_blockReflect_inv {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (Y : BlockVec d) :
    blockMatVecMul (blockMatrixOfCoeff A)
        (blockMatVecMul (blockReflect (blockMatrixOfCoeff A)) Y) = Y := by
  rw [← blockMatVecMul_blockMatMul,
    blockMatMul_blockReflect_blockMatrixOfCoeff_eq_id hA, blockMatVecMul_blockIdentity]

/-! ## Positive semidefiniteness and the block Fenchel inequality -/

/-- `bfA` is positive semidefinite. -/
theorem blockMatrixOfCoeff_quadratic_nonneg {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (Z : BlockVec d) :
    0 ≤ blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) := by
  have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix hA Z
  have hden : (0 : ℝ) < 1 + 2 * Lam ^ 2 := by positivity
  have hc : 0 ≤ (lam / (1 + 2 * Lam ^ 2)) * blockVecDot Z Z :=
    mul_nonneg (div_nonneg hA.1.le hden.le) (blockVecDot_nonneg Z)
  linarith

/-- **Block Fenchel/Young inequality.**  For the symmetric p.s.d. `bfA` with
inverse `blockReflect bfA`:
`2 X·Y − Y·(reflect bfA)Y ≤ X·(bfA)X`. -/
theorem block_fenchel {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X Y : BlockVec d) :
    2 * blockVecDot X Y -
        blockVecDot Y (blockMatVecMul (blockReflect (blockMatrixOfCoeff A)) Y) ≤
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) := by
  set P := blockMatrixOfCoeff A with hP
  set R := blockReflect P with hR
  have hPsymm : IsSymmetricBlockMat P := isSymmetricBlockMat_blockMatrixOfCoeff A
  set W := blockMatVecMul R Y with hWdef
  have hPW : blockMatVecMul P W = Y := blockMatVecMul_blockReflect_inv hA Y
  have hpsd :
      0 ≤ blockVecDot (X + (-1 : ℝ) • W) (blockMatVecMul P (X + (-1 : ℝ) • W)) :=
    blockMatrixOfCoeff_quadratic_nonneg hA _
  have hPZ : blockMatVecMul P (X + (-1 : ℝ) • W) = blockMatVecMul P X + (-1 : ℝ) • Y := by
    rw [blockMatVecMul_add, blockMatVecMul_smul, hPW]
  rw [hPZ] at hpsd
  simp only [blockVecDot_add_left, blockVecDot_add_right, blockVecDot_smul_left,
    blockVecDot_smul_right] at hpsd
  have hcomm : blockVecDot W (blockMatVecMul P X) = blockVecDot X Y := by
    rw [blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hPsymm, hPW]
  have hWY : blockVecDot W Y = blockVecDot Y (blockMatVecMul R Y) := by
    rw [hWdef, blockVecDot_comm]
  linarith [hpsd, hcomm, hWY]

/-! ## A8 (lower) — diagonal sandwich, lower half -/

/-- A block-diagonal matrix with scalar-multiple-of-identity blocks acts by
scaling each block. -/
theorem blockMatVecMul_blockDiag_smul_one (a b : ℝ) (p q : Vec d) :
    blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) (p, q) =
      (a • p, b • q) := by
  refine Prod.ext ?_ ?_ <;>
    simp [blockDiag, blockMatVecMul, matVecMul_smul_one, zero_matVecMul]

/-- **A8 (lower).**  `blockDiag (½ • 1) ((2Θ)⁻¹ • 1) ≤ bfA` in the block Loewner
order. -/
theorem blockDiag_blockMatLoewnerLE_blockMatrixOfCoeff_of_isThetaElliptic
    {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) :
    BlockMatLoewnerLE
      (blockDiag ((1 / 2 : ℝ) • (1 : Mat d)) ((2 * Θ)⁻¹ • (1 : Mat d)))
      (blockMatrixOfCoeff A) := by
  have hΘ : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hA.2.1
  intro X
  rcases X with ⟨p, q⟩
  -- the Fenchel test vector Y = D_lo (p,q) = (½ p, (2Θ)⁻¹ q)
  set Ylo := blockMatVecMul
      (blockDiag ((1 / 2 : ℝ) • (1 : Mat d)) ((2 * Θ)⁻¹ • (1 : Mat d))) (p, q) with hYlo
  have hYval : Ylo = ((1 / 2 : ℝ) • p, (2 * Θ)⁻¹ • q) := by
    rw [hYlo]; exact blockMatVecMul_blockDiag_smul_one _ _ p q
  -- value of X·(D_lo X)
  have hDlo :
      blockVecDot (p, q) Ylo = (1 / 2 : ℝ) * vecNormSq p + (2 * Θ)⁻¹ * vecNormSq q := by
    rw [hYlo]
    exact blockVecDot_blockMatVecMul_blockDiag_smul_one (1 / 2) ((2 * Θ)⁻¹) p q
  -- Fenchel at Y = Ylo
  have hfen := block_fenchel hA (p, q) Ylo
  -- bound the dual term Y·(reflect bfA)Y
  have hswap :
      blockVecDot Ylo (blockMatVecMul (blockReflect (blockMatrixOfCoeff A)) Ylo) =
        blockVecDot (Ylo.2, Ylo.1)
          (blockMatVecMul (blockMatrixOfCoeff A) (Ylo.2, Ylo.1)) :=
    blockVecDot_blockMatVecMul_blockReflect (blockMatrixOfCoeff A) Ylo
  have hZ : (Ylo.2, Ylo.1) = ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p) := by
    rw [hYval]
  -- A8 upper applied at the swapped vector
  have hup := blockMatrixOfCoeff_blockMatLoewnerLE_blockDiag_of_isThetaElliptic hA
      ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p)
  have hdhi := blockVecDot_blockMatVecMul_blockDiag_smul_one (2 * Θ) 2
      ((2 * Θ)⁻¹ • q) ((1 / 2 : ℝ) • p)
  rw [vecNormSq_smul, vecNormSq_smul] at hdhi
  -- simplify the diagonal upper value using Θ > 0
  have harith :
      (2 * Θ) * ((2 * Θ)⁻¹ ^ 2 * vecNormSq q) + 2 * ((1 / 2 : ℝ) ^ 2 * vecNormSq p) =
        (2 * Θ)⁻¹ * vecNormSq q + (1 / 2 : ℝ) * vecNormSq p := by
    have hne : (2 * Θ) ≠ 0 := by positivity
    field_simp
  rw [harith] at hdhi
  -- assemble
  have hYRY :
      blockVecDot Ylo (blockMatVecMul (blockReflect (blockMatrixOfCoeff A)) Ylo) ≤
        (2 * Θ)⁻¹ * vecNormSq q + (1 / 2 : ℝ) * vecNormSq p := by
    rw [hswap, hZ]
    have hup' :
        blockVecDot ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p)
            (blockMatVecMul (blockMatrixOfCoeff A) ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p)) ≤
          blockVecDot ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p)
            (blockMatVecMul
              (blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d)))
              ((2 * Θ)⁻¹ • q, (1 / 2 : ℝ) • p)) := by
      have := hup; linarith [this]
    rw [hdhi] at hup'
    exact hup'
  -- reduce the block Loewner goal and finish
  show (1 / 2 : ℝ) * blockVecDot (p, q) Ylo ≤
    (1 / 2 : ℝ) * blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q))
  rw [hDlo]
  rw [hDlo] at hfen
  linarith [hfen, hYRY]

/-! ## A9 — two-field comparison

The verified scalar action on `BlockMat d` (componentwise), and the comparison
`bfB ≤ 4Θ • bfA` for two matrices in the same `(1, Θ)` ellipticity class. -/

/-- Componentwise scalar action on doubled block matrices. -/
-- Candidate for relocation to `Homogenization/Ambient/BlockMatrix.lean`.
instance : SMul ℝ (BlockMat d) where
  smul c P :=
    { upperLeft := c • P.upperLeft
      upperRight := c • P.upperRight
      lowerLeft := c • P.lowerLeft
      lowerRight := c • P.lowerRight }

@[simp] theorem blockSMul_upperLeft (c : ℝ) (P : BlockMat d) :
    (c • P).upperLeft = c • P.upperLeft := rfl
@[simp] theorem blockSMul_upperRight (c : ℝ) (P : BlockMat d) :
    (c • P).upperRight = c • P.upperRight := rfl
@[simp] theorem blockSMul_lowerLeft (c : ℝ) (P : BlockMat d) :
    (c • P).lowerLeft = c • P.lowerLeft := rfl
@[simp] theorem blockSMul_lowerRight (c : ℝ) (P : BlockMat d) :
    (c • P).lowerRight = c • P.lowerRight := rfl

/-- The scalar action commutes with the doubled action. -/
theorem blockMatVecMul_blockSMul (c : ℝ) (P : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (c • P) X = c • blockMatVecMul P X := by
  rcases X with ⟨p, q⟩
  refine Prod.ext ?_ ?_ <;>
    simp [blockMatVecMul, smul_matVecMul, smul_add]

/-- `blockSMul` on block-diagonal scalar matrices. -/
theorem blockSMul_blockDiag_smul_one (c a b : ℝ) :
    (c • blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) =
      blockDiag ((c * a) • (1 : Mat d)) ((c * b) • (1 : Mat d)) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp [blockDiag, mul_smul]

/-- The block Loewner order is preserved by nonnegative scaling. -/
theorem blockMatLoewnerLE_smul {c : ℝ} (hc : 0 ≤ c) {P Q : BlockMat d}
    (h : BlockMatLoewnerLE P Q) : BlockMatLoewnerLE (c • P) (c • Q) := by
  intro X
  have hx := h X
  rw [blockMatVecMul_blockSMul, blockMatVecMul_blockSMul, blockVecDot_smul_right,
    blockVecDot_smul_right]
  nlinarith [hx, hc]

/-- **A9.**  For `A`, `B` in the same `(1, Θ)` ellipticity class,
`bfB ≤ (4Θ) • bfA` in the block Loewner order. -/
theorem blockMatrixOfCoeff_blockMatLoewnerLE_smul_of_isThetaElliptic
    {Θ : ℝ} {A B : Mat d} (hA : IsThetaElliptic Θ A) (hB : IsThetaElliptic Θ B) :
    BlockMatLoewnerLE (blockMatrixOfCoeff B) ((4 * Θ) • blockMatrixOfCoeff A) := by
  have hΘ : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hA.2.1
  have hne : (2 * Θ) ≠ 0 := by positivity
  -- bfB ≤ blockDiag (2Θ • 1) (2 • 1)
  have hupB := blockMatrixOfCoeff_blockMatLoewnerLE_blockDiag_of_isThetaElliptic hB
  -- blockDiag (½ • 1) ((2Θ)⁻¹ • 1) ≤ bfA
  have hloA := blockDiag_blockMatLoewnerLE_blockMatrixOfCoeff_of_isThetaElliptic hA
  -- scale the lower bound by 4Θ ≥ 0
  have hscaled := blockMatLoewnerLE_smul (c := 4 * Θ) (by positivity) hloA
  -- 4Θ • blockDiag (½ • 1) ((2Θ)⁻¹ • 1) = blockDiag (2Θ • 1) (2 • 1)
  have hdiageq :
      (4 * Θ) • blockDiag ((1 / 2 : ℝ) • (1 : Mat d)) ((2 * Θ)⁻¹ • (1 : Mat d)) =
        blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d)) := by
    rw [blockSMul_blockDiag_smul_one]
    have e1 : (4 * Θ) * (1 / 2 : ℝ) = 2 * Θ := by ring
    have e2 : (4 * Θ) * (2 * Θ)⁻¹ = (2 : ℝ) := by
      rw [show (4 : ℝ) * Θ = 2 * (2 * Θ) by ring, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [e1, e2]
  rw [hdiageq] at hscaled
  exact BlockMatLoewnerLE.trans hupB hscaled

end Homogenization
