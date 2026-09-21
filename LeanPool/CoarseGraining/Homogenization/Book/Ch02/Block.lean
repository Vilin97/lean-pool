/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Matrices
import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix

/-! # Block -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public transpose operation for doubled block matrices. -/
def blockMatTranspose {d : ℕ} (A : BlockMat d) : BlockMat d :=
  { upperLeft := matTranspose A.upperLeft
    upperRight := matTranspose A.lowerLeft
    lowerLeft := matTranspose A.upperRight
    lowerRight := matTranspose A.lowerRight }

/-- Public multiplication operation for doubled block matrices. -/
def blockMatMul {d : ℕ} (A B : BlockMat d) : BlockMat d :=
  { upperLeft := A.upperLeft * B.upperLeft + A.upperRight * B.lowerLeft
    upperRight := A.upperLeft * B.upperRight + A.upperRight * B.lowerRight
    lowerLeft := A.lowerLeft * B.upperLeft + A.lowerRight * B.lowerLeft
    lowerRight := A.lowerLeft * B.upperRight + A.lowerRight * B.lowerRight }

/-- Public block diagonal matrix. -/
def blockDiag {d : ℕ} (A B : Mat d) : BlockMat d :=
  { upperLeft := A
    upperRight := 0
    lowerLeft := 0
    lowerRight := B }

/-- Public identity matrix in doubled block form. -/
def blockIdentity (d : ℕ) : BlockMat d :=
  blockDiag 1 1

/-- Public inverse operation for doubled block matrices, routed through the
ordinary `2d × 2d` matrix inverse. -/
noncomputable def blockMatInv {d : ℕ} (A : BlockMat d) : BlockMat d :=
  ofFullBlockMat ((toFullBlockMat A)⁻¹)

/-- Public triangular block matrix `G_h`. -/
def blockG {d : ℕ} (h : Mat d) : BlockMat d :=
  { upperLeft := 1
    upperRight := 0
    lowerLeft := h
    lowerRight := 1 }

/-- Public reflection block matrix `R`. -/
def blockR (d : ℕ) : BlockMat d :=
  { upperLeft := 0
    upperRight := 1
    lowerLeft := 1
    lowerRight := 0 }

/-- Positive definiteness for public doubled block matrices, expressed through
the doubled quadratic form. -/
def BlockPosDef {d : ℕ} (A : BlockMat d) : Prop :=
  ∀ X : BlockVec d, X ≠ 0 → 0 < blockVecDot X (blockMatVecMul A X)

/-- The pointwise doubled coefficient matrix field `\mathbf A(x)` associated to
the public coefficient representative. Public theorems about this field should
use a.e. hypotheses/conclusions on `U`. -/
noncomputable def blockMatrixField {d : ℕ} {U : Domain d} (a : CoeffOn U) :
    Vec d → BlockMat d :=
  fun x =>
    let s := symmPart (a.toCoeffField x)
    let k := skewPart (a.toCoeffField x)
    let sInv := s⁻¹
    { upperLeft := s + matTranspose k * sInv * k
      upperRight := -(matTranspose k * sInv)
      lowerLeft := -(sInv * k)
      lowerRight := sInv }

/-- The explicit inverse field appearing in
`e.block.matrix.inverse.basic.definitions`. -/
noncomputable def blockMatrixInverseField {d : ℕ} {U : Domain d} (a : CoeffOn U) :
    Vec d → BlockMat d :=
  fun x =>
    let s := symmPart (a.toCoeffField x)
    let k := skewPart (a.toCoeffField x)
    let sInv := s⁻¹
    { upperLeft := sInv
      upperRight := -(sInv * k)
      lowerLeft := -(matTranspose k * sInv)
      lowerRight := s + matTranspose k * sInv * k }

/-- Pointwise doubled energy density
`\frac12 X \cdot \mathbf A(x) X`. -/
noncomputable def blockEnergyDensityAt {d : ℕ} {U : Domain d} (a : CoeffOn U)
    (X : BlockVec d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockMatrixField a x) X)

/-- The note-facing coarse block matrix assembled from the public coarse
matrices `sigma`, `sigmaStarInv`, and `kappa`. -/
noncomputable def blockMatrixOfCoarseMatrices {d : ℕ}
    (M : CoarseMatrices d) : BlockMat d :=
  { upperLeft := M.b
    upperRight := -(matTranspose M.kappa * M.sigmaStarInv)
    lowerLeft := -(M.sigmaStarInv * M.kappa)
    lowerRight := M.sigmaStarInv }

private theorem blockMatrixOfCoarseMatrices_cross_transpose {d : ℕ} (K S : Mat d)
    (hS : S.IsSymm) :
    matTranspose (-(matTranspose K * S)) = -(S * K) := by
  ext i j
  simp [matTranspose, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [hS.apply]
  ring

/-- The note-facing coarse block matrix assembled from the public coarse
matrices is symmetric as a doubled block matrix. -/
theorem isSymmetricBlockMat_blockMatrixOfCoarseMatrices {d : ℕ}
    (M : CoarseMatrices d) (hSigma : M.sigma.IsSymm)
    (hSigmaStarInv : M.sigmaStarInv.IsSymm) :
    IsSymmetricBlockMat (blockMatrixOfCoarseMatrices M) := by
  have hB : M.b.IsSymm := by
    unfold CoarseMatrices.b
    exact Matrix.IsSymm.add hSigma
      (transpose_mul_symm_mul_isSymm M.kappa M.sigmaStarInv hSigmaStarInv)
  have hCross :
      matTranspose (-(matTranspose M.kappa * M.sigmaStarInv)) =
        -(M.sigmaStarInv * M.kappa) :=
    blockMatrixOfCoarseMatrices_cross_transpose M.kappa M.sigmaStarInv hSigmaStarInv
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockMatrixOfCoarseMatrices, blockMatEntry, matTranspose] using
            (hB.apply i j).symm
      | inr j =>
          have h := congrArg (fun N : Mat d => N j i) hCross
          simpa [blockMatrixOfCoarseMatrices, blockMatEntry, matTranspose] using h
  | inr i =>
      cases β with
      | inl j =>
          have h := congrArg (fun N : Mat d => N i j) hCross
          simpa [blockMatrixOfCoarseMatrices, blockMatEntry, matTranspose] using h.symm
      | inr j =>
          simpa [blockMatrixOfCoarseMatrices, blockMatEntry, matTranspose] using
            (hSigmaStarInv.apply i j).symm

/-- The canonical public coarse block matrix `\mathbf A(U; a)`. -/
noncomputable def coarseBlockMatrix {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    BlockMat d :=
  blockMatrixOfCoarseMatrices (coarseMatrices U a)

/-- The canonical public coarse block matrix is symmetric as a doubled block
matrix. -/
theorem isSymmetricBlockMat_coarseBlockMatrix {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    IsSymmetricBlockMat (coarseBlockMatrix U a) := by
  unfold coarseBlockMatrix
  exact isSymmetricBlockMat_blockMatrixOfCoarseMatrices (coarseMatrices U a)
    (sigmaCoarse_isSymm U a) (sigmaStarInvCoarse_isSymm U a)

theorem coarseBlockMatrix_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    coarseBlockMatrix U a = coarseBlockMatrix U b := by
  simp [coarseBlockMatrix, blockMatrixOfCoarseMatrices, coarseMatrices_eq_ofAEEq h]

/-- The canonical public starred inverse block matrix
`\mathbf A_*^{-1}(U; a)`. -/
noncomputable def coarseStarredBlockMatrixInv {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : BlockMat d :=
  blockReflect (coarseBlockMatrix U a)

/-- The canonical public starred block matrix `\mathbf A_*(U; a)`.

The notes introduce `\mathbf A_*` through the positive definite matrix whose
inverse appears in the doubled response splitting. -/
noncomputable def coarseStarredBlockMatrix {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : BlockMat d :=
  blockMatInv (coarseStarredBlockMatrixInv U a)

@[simp] theorem coarseBlockMatrix_upperLeft {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseBlockMatrix U a).upperLeft = bCoarse U a :=
  rfl

@[simp] theorem coarseBlockMatrix_upperRight {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseBlockMatrix U a).upperRight =
      -(matTranspose (kappaCoarse U a) * sigmaStarInvCoarse U a) :=
  rfl

@[simp] theorem coarseBlockMatrix_lowerLeft {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseBlockMatrix U a).lowerLeft =
      -(sigmaStarInvCoarse U a * kappaCoarse U a) :=
  rfl

@[simp] theorem coarseBlockMatrix_lowerRight {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a :=
  rfl

@[simp] theorem coarseStarredBlockMatrixInv_eq_blockReflect {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    coarseStarredBlockMatrixInv U a = blockReflect (coarseBlockMatrix U a) :=
  rfl

end

end Ch02
end Book
end Homogenization
