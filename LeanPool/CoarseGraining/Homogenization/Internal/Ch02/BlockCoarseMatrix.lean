/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockCoarseMatrixDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MagicIdentities
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledMu
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticWrappers
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.Basics

/-! # Block Coarse Matrix -/

open scoped BigOperators

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem blockMat_eq_of_toFullBlockMat_eq {d : ℕ} {A B : BlockMat d}
    (h : toFullBlockMat A = toFullBlockMat B) : A = B := by
  calc
    A = ofFullBlockMat (toFullBlockMat A) := (ofFullBlockMat_toFullBlockMat A).symm
    _ = ofFullBlockMat (toFullBlockMat B) := by rw [h]
    _ = B := ofFullBlockMat_toFullBlockMat B

private theorem toFullBlockMat_blockMatMul {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (Book.Ch02.blockMatMul A B) =
      toFullBlockMat A * toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;>
    simp [Book.Ch02.blockMatMul, toFullBlockMat, Matrix.mul_apply,
      Fintype.sum_sum_type]

private theorem toFullBlockMat_blockIdentity {d : ℕ} :
    toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
  ext α β
  cases α <;> cases β <;>
    simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat,
      Matrix.one_apply]

private theorem blockMatMul_blockMatInv_right {d : ℕ} (A : BlockMat d)
    (hdet : IsUnit (toFullBlockMat A).det) :
    Book.Ch02.blockMatMul A (Book.Ch02.blockMatInv A) =
      Book.Ch02.blockIdentity d := by
  apply blockMat_eq_of_toFullBlockMat_eq
  calc
    toFullBlockMat (Book.Ch02.blockMatMul A (Book.Ch02.blockMatInv A)) =
        toFullBlockMat A * toFullBlockMat (Book.Ch02.blockMatInv A) := by
          rw [toFullBlockMat_blockMatMul]
    _ = toFullBlockMat A * (toFullBlockMat A)⁻¹ := by
          simp [Book.Ch02.blockMatInv]
    _ = 1 := Matrix.mul_nonsing_inv (toFullBlockMat A) hdet
    _ = toFullBlockMat (Book.Ch02.blockIdentity d) :=
          (toFullBlockMat_blockIdentity (d := d)).symm

private theorem blockMatMul_blockMatInv_left {d : ℕ} (A : BlockMat d)
    (hdet : IsUnit (toFullBlockMat A).det) :
    Book.Ch02.blockMatMul (Book.Ch02.blockMatInv A) A =
      Book.Ch02.blockIdentity d := by
  apply blockMat_eq_of_toFullBlockMat_eq
  calc
    toFullBlockMat (Book.Ch02.blockMatMul (Book.Ch02.blockMatInv A) A) =
        toFullBlockMat (Book.Ch02.blockMatInv A) * toFullBlockMat A := by
          rw [toFullBlockMat_blockMatMul]
    _ = (toFullBlockMat A)⁻¹ * toFullBlockMat A := by
          simp [Book.Ch02.blockMatInv]
    _ = 1 := Matrix.nonsing_inv_mul (toFullBlockMat A) hdet
    _ = toFullBlockMat (Book.Ch02.blockIdentity d) :=
          (toFullBlockMat_blockIdentity (d := d)).symm

private theorem isUnit_det_toFullBlockMat_of_blockPosDef {d : ℕ}
    {A : BlockMat d} (hA : Book.Ch02.BlockPosDef A) :
    IsUnit (toFullBlockMat A).det := by
  classical
  let M : FullBlockMat d := toFullBlockMat A
  have hker : ¬ ∃ v : FullBlockVec d, v ≠ 0 ∧ Matrix.mulVec M v = 0 := by
    rintro ⟨v, hv, hMv⟩
    let X : BlockVec d := ofFullBlockVec v
    have hX : X ≠ 0 := by
      intro hX0
      apply hv
      calc
        v = toFullBlockVec X := by simp [X]
        _ = 0 := by
          rw [hX0]
          funext α
          cases α <;> rfl
    have hquad : blockVecDot X (blockMatVecMul A X) = 0 := by
      rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X)]
      rw [toFullBlockVec_blockMatVecMul]
      simp [M, X, hMv]
    have hpos := hA X hX
    linarith
  have hdet_ne : (toFullBlockMat A).det ≠ 0 := by
    intro hdet
    rcases (Matrix.exists_mulVec_eq_zero_iff (M := M)).mpr hdet with ⟨v, hv, hMv⟩
    exact hker ⟨v, hv, by simpa [Matrix.mulVec] using hMv⟩
  exact isUnit_iff_ne_zero.mpr hdet_ne

private theorem toFullBlockMat_posDef_of_blockPosDef {d : ℕ} {A : BlockMat d}
    (hSymm : IsSymmetricBlockMat A) (hPos : Book.Ch02.BlockPosDef A) :
    (toFullBlockMat A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      isSymm_toFullBlockMat_of_isSymmetricBlockMat hSymm
  · intro v hv
    let X : BlockVec d := ofFullBlockVec v
    have hX : X ≠ 0 := by
      intro hX0
      apply hv
      calc
        v = toFullBlockVec X := by simp [X]
        _ = 0 := by
          rw [hX0]
          funext α
          cases α <;> rfl
    have h := hPos X hX
    have h' : 0 < dotProduct v (Matrix.mulVec (toFullBlockMat A) v) := by
      rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X)] at h
      rw [toFullBlockVec_blockMatVecMul] at h
      simpa [X] using h
    simpa using h'

private theorem blockMatInv_posDef_of_blockPosDef {d : ℕ} {A : BlockMat d}
    (hSymm : IsSymmetricBlockMat A) (hPos : Book.Ch02.BlockPosDef A) :
    Book.Ch02.BlockPosDef (Book.Ch02.blockMatInv A) := by
  have hFull : (toFullBlockMat A).PosDef :=
    toFullBlockMat_posDef_of_blockPosDef hSymm hPos
  intro X hX
  have hFullX : toFullBlockVec X ≠ 0 := by
    intro hzero
    apply hX
    calc
      X = ofFullBlockVec (toFullBlockVec X) := (ofFullBlockVec_toFullBlockVec X).symm
      _ = 0 := by rw [hzero]; rfl
  have h := hFull.inv.dotProduct_mulVec_pos hFullX
  rw [← dotProduct_toFullBlockVec X
    (blockMatVecMul (Book.Ch02.blockMatInv A) X)]
  rw [toFullBlockVec_blockMatVecMul]
  simpa [Book.Ch02.blockMatInv] using h

private theorem blockVec_swap_ne_zero {d : ℕ} {X : BlockVec d}
    (hX : X ≠ 0) : (X.2, X.1) ≠ 0 := by
  rcases X with ⟨p, q⟩
  intro h
  exact hX (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))

private theorem blockPosDef_blockReflect {d : ℕ} {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) :
    Book.Ch02.BlockPosDef (blockReflect A) := by
  intro X hX
  simpa using hA (X.2, X.1) (blockVec_swap_ne_zero hX)

private theorem BlockMatLoewnerLE_blockReflect {d : ℕ} {A B : BlockMat d}
    (hAB : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockReflect A) (blockReflect B) := by
  intro X
  simpa using hAB (X.2, X.1)

private theorem weightedAverage_add_const {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (f : P.Cell → ℝ) (c : ℝ) :
    P.weightedAverage (fun i => f i + c) = P.weightedAverage f + c := by
  classical
  let : Fintype P.Cell := P.instFintype
  unfold DomainPartition.weightedAverage
  calc
    ∑ i : P.Cell, P.weight i * (f i + c) =
        ∑ i : P.Cell, (P.weight i * f i + P.weight i * c) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = ∑ i : P.Cell, P.weight i * f i + ∑ i : P.Cell, P.weight i * c := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i : P.Cell, P.weight i * f i + (∑ i : P.Cell, P.weight i) * c := by
          rw [Finset.sum_mul]
    _ = ∑ i : P.Cell, P.weight i * f i + c := by
          rw [P.weight_sum_one, one_mul]

private theorem weightedAverage_const_mul {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (c : ℝ) (f : P.Cell → ℝ) :
    P.weightedAverage (fun i => c * f i) = c * P.weightedAverage f := by
  classical
  let : Fintype P.Cell := P.instFintype
  unfold DomainPartition.weightedAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

private theorem vecDot_matVecMul_weightedMatAverage {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (F : P.Cell → Mat d) (x y : Vec d) :
    vecDot x (matVecMul (P.weightedMatAverage F) y) =
      P.weightedAverage fun i => vecDot x (matVecMul (F i) y) := by
  classical
  let : Fintype P.Cell := P.instFintype
  simp [DomainPartition.weightedMatAverage, DomainPartition.weightedAverage,
    vecDot, matVecMul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  ring_nf
  let T : P.Cell → Fin d → Fin d → ℝ :=
    fun c i j => F c i j * x i * y j * P.weight c
  change (∑ i : Fin d, ∑ j : Fin d, ∑ c : P.Cell, T c i j) =
    ∑ c : P.Cell, ∑ i : Fin d, ∑ j : Fin d, T c i j
  calc
    (∑ i : Fin d, ∑ j : Fin d, ∑ c : P.Cell, T c i j)
        = ∑ i : Fin d, ∑ c : P.Cell, ∑ j : Fin d, T c i j := by
          congr with i
          rw [Finset.sum_comm]
    _ = ∑ c : P.Cell, ∑ i : Fin d, ∑ j : Fin d, T c i j := by
          rw [Finset.sum_comm]

private theorem blockVecDot_blockMatVecMul_weightedBlockAverage {d : ℕ}
    {U : Domain d} (P : DomainPartition U) (F : P.Cell → BlockMat d)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (P.weightedBlockAverage F) X) =
      P.weightedAverage fun i => blockVecDot X (blockMatVecMul (F i) X) := by
  classical
  let : Fintype P.Cell := P.instFintype
  rcases X with ⟨p, q⟩
  rw [blockMatVecMul, blockVecDot, vecDot_add_right, vecDot_add_right]
  change
    vecDot p (matVecMul (P.weightedMatAverage fun i => (F i).upperLeft) p) +
          vecDot p (matVecMul (P.weightedMatAverage fun i => (F i).upperRight) q) +
        (vecDot q (matVecMul (P.weightedMatAverage fun i => (F i).lowerLeft) p) +
          vecDot q (matVecMul (P.weightedMatAverage fun i => (F i).lowerRight) q)) =
      P.weightedAverage fun i => blockVecDot (p, q) (blockMatVecMul (F i) (p, q))
  rw [vecDot_matVecMul_weightedMatAverage P (fun i => (F i).upperLeft)]
  rw [vecDot_matVecMul_weightedMatAverage P (fun i => (F i).upperRight)]
  rw [vecDot_matVecMul_weightedMatAverage P (fun i => (F i).lowerLeft)]
  rw [vecDot_matVecMul_weightedMatAverage P (fun i => (F i).lowerRight)]
  simp [DomainPartition.weightedAverage, blockMatVecMul, blockVecDot,
    vecDot_add_right, Finset.sum_add_distrib, mul_add, add_assoc]

private theorem half_blockVecDot_blockMatVecMul_weightedBlockAverage {d : ℕ}
    {U : Domain d} (P : DomainPartition U) (F : P.Cell → BlockMat d)
    (X : BlockVec d) :
    (1 / 2 : ℝ) *
        blockVecDot X (blockMatVecMul (P.weightedBlockAverage F) X) =
      P.weightedAverage fun i =>
        (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (F i) X) := by
  rw [blockVecDot_blockMatVecMul_weightedBlockAverage P F X]
  rw [weightedAverage_const_mul]

private theorem weightedBlockAverage_blockReflect {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (F : P.Cell → BlockMat d) :
    P.weightedBlockAverage (fun i => blockReflect (F i)) =
      blockReflect (P.weightedBlockAverage F) := by
  rfl

private theorem cross_transpose {d : ℕ} (K S : Mat d) (hS : S.IsSymm) :
    matTranspose (-(matTranspose K * S)) = -(S * K) := by
  ext i j
  simp [matTranspose, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [hS.apply]
  ring

private theorem isSymmetricBlockMat_blockMatrixOfCoarseMatrices {d : ℕ}
    (M : CoarseMatrices d) (hSigma : M.sigma.IsSymm)
    (hSigmaStarInv : M.sigmaStarInv.IsSymm) :
    IsSymmetricBlockMat (Book.Ch02.blockMatrixOfCoarseMatrices M) := by
  have hB : M.b.IsSymm := by
    unfold CoarseMatrices.b
    exact hSigma.add
      (transpose_mul_symm_mul_isSymm M.kappa M.sigmaStarInv hSigmaStarInv)
  have hCross :
      matTranspose (-(matTranspose M.kappa * M.sigmaStarInv)) =
        -(M.sigmaStarInv * M.kappa) :=
    cross_transpose M.kappa M.sigmaStarInv hSigmaStarInv
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [Book.Ch02.blockMatrixOfCoarseMatrices, blockMatEntry,
            matTranspose] using (hB.apply i j).symm
      | inr j =>
          have h := congrArg (fun N : Mat d => N j i) hCross
          simpa [Book.Ch02.blockMatrixOfCoarseMatrices, blockMatEntry,
            matTranspose] using h
  | inr i =>
      cases β with
      | inl j =>
          have h := congrArg (fun N : Mat d => N i j) hCross
          simpa [Book.Ch02.blockMatrixOfCoarseMatrices, blockMatEntry,
            matTranspose] using h.symm
      | inr j =>
          simpa [Book.Ch02.blockMatrixOfCoarseMatrices, blockMatEntry,
            matTranspose] using (hSigmaStarInv.apply i j).symm

private theorem coarseBlockMatrix_isSymmetricBlockMat {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    IsSymmetricBlockMat (Book.Ch02.coarseBlockMatrix U a) := by
  unfold Book.Ch02.coarseBlockMatrix
  exact isSymmetricBlockMat_blockMatrixOfCoarseMatrices (Book.Ch02.coarseMatrices U a)
    (Book.Ch02.sigmaCoarse_isSymm U a) (Book.Ch02.sigmaStarInvCoarse_isSymm U a)

private theorem responseJ_eq_block_quadratic_zero_dim
    (U : Domain 0) (a : CoeffOn U) (p q : Vec 0) :
    responseJ U a p q =
      (1 / 2 : ℝ) *
          blockVecDot (-p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) -
        vecDot p q := by
  have hp : p = 0 := Subsingleton.elim p 0
  have hq : q = 0 := Subsingleton.elim q 0
  subst p
  subst q
  have hJ := Book.Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse U a (0 : Vec 0)
  simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul] using hJ

private theorem responseJ_eq_block_quadratic_of_isEllipticFieldOn {d : ℕ}
    [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) *
          blockVecDot (-p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) -
        vecDot p q := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, _sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
      compat hS
  have hBlockEq :
      Book.Ch02.coarseBlockMatrix U a =
        Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField :=
    book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data U a hA hS hK hSigma hdet
  have hOld :=
    magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
      compat hA hS hK hSigma p q
  calc
    responseJ U a p q = ResponseJ (U : Set (Vec d)) p q a.toCoeffField :=
      book_responseJ_eq_ResponseJ U a p q
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (-p, q)
              (blockMatVecMul
                (Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField)
                (-p, q)) -
          vecDot p q := hOld
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (-p, q)
              (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) -
          vecDot p q := by
            rw [hBlockEq]

theorem responseJ_eq_block_quadratic {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) *
          blockVecDot (-p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) -
        vecDot p q := by
  by_cases hd : d = 0
  · subst d
    exact responseJ_eq_block_quadratic_zero_dim U a p q
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hbEll :
        IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
      simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    have hb := responseJ_eq_block_quadratic_of_isEllipticFieldOn U b hbEll p q
    calc
      responseJ U a p q = responseJ U b p q := by
        rw [responseJ_eq_ofAEEq hba p q]
      _ =
          (1 / 2 : ℝ) *
              blockVecDot (-p, q)
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b) (-p, q)) -
            vecDot p q := hb
      _ =
          (1 / 2 : ℝ) *
              blockVecDot (-p, q)
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) -
            vecDot p q := by
              rw [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hba]

private theorem coarseBlockMatrix_quadratic_split_zero_dim
    (U : Domain 0) (a : CoeffOn U) (p q : Vec 0) :
    (1 / 2 : ℝ) *
        blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul (Book.Ch02.kappaCoarse U a) p)
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
              (q - matVecMul (Book.Ch02.kappaCoarse U a) p)) := by
  have hp : p = 0 := Subsingleton.elim p 0
  have hq : q = 0 := Subsingleton.elim q 0
  subst p
  subst q
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]

private theorem coarseBlockMatrix_quadratic_split_of_isEllipticFieldOn {d : ℕ}
    [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) :
    (1 / 2 : ℝ) *
        blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul (Book.Ch02.kappaCoarse U a) p)
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
              (q - matVecMul (Book.Ch02.kappaCoarse U a) p)) := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, _sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
      compat hS
  have hBlockEq :
      Book.Ch02.coarseBlockMatrix U a =
        Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField :=
    book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data U a hA hS hK hSigma hdet
  have hOld :=
    magic_identity_block_quadratic_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
      compat hA hS hK hSigma p q
  calc
    (1 / 2 : ℝ) *
        blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) *
        blockVecDot (p, q)
          (blockMatVecMul
            (Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField)
            (p, q)) := by
            rw [hBlockEq]
    _ =
        (1 / 2 : ℝ) *
            vecDot p
              (matVecMul
                (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) p) +
          (1 / 2 : ℝ) *
            vecDot
              (q - matVecMul
                (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
              (matVecMul
                (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                (q - matVecMul
                  (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
        hOld
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) +
          (1 / 2 : ℝ) *
            vecDot (q - matVecMul (Book.Ch02.kappaCoarse U a) p)
              (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
                (q - matVecMul (Book.Ch02.kappaCoarse U a) p)) := by
            rw [← book_sigmaCoarse_eq_sigmaCoarse U a,
              ← book_kappaCoarse_eq_kappaCoarse U a,
              ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]

private theorem coarseBlockMatrix_quadratic_split {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    (1 / 2 : ℝ) *
        blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul (Book.Ch02.kappaCoarse U a) p)
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
              (q - matVecMul (Book.Ch02.kappaCoarse U a) p)) := by
  by_cases hd : d = 0
  · subst d
    exact coarseBlockMatrix_quadratic_split_zero_dim U a p q
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hbEll :
        IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
      simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    have hb := coarseBlockMatrix_quadratic_split_of_isEllipticFieldOn U b hbEll p q
    simpa [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hba,
      Book.Ch02.sigmaCoarse_eq_ofAEEq hba, Book.Ch02.kappaCoarse_eq_ofAEEq hba,
      Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hba] using hb

private theorem sigmaCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (Book.Ch02.sigmaCoarse U a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using Book.Ch02.sigmaCoarse_isSymm U a
  · intro p hp
    have hStar :
        0 < vecDot p (matVecMul (Book.Ch02.sigmaStarCoarse U a) p) := by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
        (Book.Ch02.sigmaStarCoarse_posDef U a).dotProduct_mulVec_pos hp
    have hLe := (Book.Ch02.responseMagicIdentitiesTheory U a).sigmaStar_le_sigma p
    have hSigma :
        0 < vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) := by
      nlinarith
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hSigma

private theorem coarseBlockMatrix_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Book.Ch02.BlockPosDef (Book.Ch02.coarseBlockMatrix U a) := by
  intro X hX
  rcases X with ⟨p, q⟩
  let r : Vec d := q - matVecMul (Book.Ch02.kappaCoarse U a) p
  have hsplit := coarseBlockMatrix_quadratic_split U a p q
  have hp_nonneg :
      0 ≤ vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) := by
    by_cases hp : p = 0
    · simp [hp, vecDot, matVecMul]
    · exact le_of_lt <| by
        simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
          (sigmaCoarse_posDef U a).dotProduct_mulVec_pos hp
  have hr_nonneg :
      0 ≤ vecDot r (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) r) := by
    by_cases hr : r = 0
    · simp [r, hr, vecDot, matVecMul]
    · exact le_of_lt <| by
        simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
          (Book.Ch02.sigmaStarInvCoarse_posDef U a).dotProduct_mulVec_pos hr
  have hhalf_pos :
      0 < (1 / 2 : ℝ) *
        blockVecDot (p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) := by
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by
        intro hq
        exact hX (Prod.ext hp hq)
      have hr : r ≠ 0 := by
        intro hr
        apply hq
        simpa [r, hp, matVecMul_zero] using hr
      have hr_pos :
          0 < vecDot r (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) r) := by
        simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
          (Book.Ch02.sigmaStarInvCoarse_posDef U a).dotProduct_mulVec_pos hr
      nlinarith [hsplit]
    · have hp_pos :
          0 < vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) := by
        simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
          (sigmaCoarse_posDef U a).dotProduct_mulVec_pos hp
      nlinarith [hsplit, hr_nonneg]
  nlinarith

private theorem adjoint_coarse_matrices_of_isEllipticFieldOn {d : ℕ}
    [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    Book.Ch02.sigmaStarInvCoarse U a.transpose =
        Book.Ch02.sigmaStarInvCoarse U a ∧
      Book.Ch02.sigmaStarCoarse U a.transpose =
        Book.Ch02.sigmaStarCoarse U a ∧
      Book.Ch02.sigmaCoarse U a.transpose = Book.Ch02.sigmaCoarse U a ∧
      Book.Ch02.kappaCoarse U a.transpose = -Book.Ch02.kappaCoarse U a := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨_R, _sigma0, _compat, hA, _hSInv, _hS, _hK, _hSigma, _hSigmaCanonical⟩
  have hEllAdj :
      IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
        (adjointCoeffField a.toCoeffField) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEllAdj hvol with
    ⟨_RAdj, _sigmaAdj, _compatAdj, hAAdj, _hSInvAdj, _hSAdj, _hKAdj,
      _hSigmaAdj, _hSigmaCanonicalAdj⟩
  have hSInvOld :
      Homogenization.sigmaStarInvCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaStarInvCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hStarOld :
      Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaStarCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hSigmaOld :
      Homogenization.sigmaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hKappaOld :
      Homogenization.kappaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        -(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
    kappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      Book.Ch02.sigmaStarInvCoarse U a.transpose =
          Homogenization.sigmaStarInvCoarse (U : Set (Vec d))
            (adjointCoeffField a.toCoeffField) := by
            simpa [CoeffOn.transpose, adjointCoeffField] using!
              book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a.transpose
      _ = Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField :=
            hSInvOld
      _ = Book.Ch02.sigmaStarInvCoarse U a := by
            rw [book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
  · calc
      Book.Ch02.sigmaStarCoarse U a.transpose =
          Homogenization.sigmaStarCoarse (U : Set (Vec d))
            (adjointCoeffField a.toCoeffField) := by
            simpa [CoeffOn.transpose, adjointCoeffField] using!
              book_sigmaStarCoarse_eq_sigmaStarCoarse U a.transpose
      _ = Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField :=
            hStarOld
      _ = Book.Ch02.sigmaStarCoarse U a := by
            rw [book_sigmaStarCoarse_eq_sigmaStarCoarse U a]
  · calc
      Book.Ch02.sigmaCoarse U a.transpose =
          Homogenization.sigmaCoarse (U : Set (Vec d))
            (adjointCoeffField a.toCoeffField) := by
            simpa [CoeffOn.transpose, adjointCoeffField] using!
              book_sigmaCoarse_eq_sigmaCoarse U a.transpose
      _ = Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField :=
            hSigmaOld
      _ = Book.Ch02.sigmaCoarse U a := by
            rw [book_sigmaCoarse_eq_sigmaCoarse U a]
  · calc
      Book.Ch02.kappaCoarse U a.transpose =
          Homogenization.kappaCoarse (U : Set (Vec d))
            (adjointCoeffField a.toCoeffField) := by
            simpa [CoeffOn.transpose, adjointCoeffField] using!
              book_kappaCoarse_eq_kappaCoarse U a.transpose
      _ = -(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
            hKappaOld
      _ = -Book.Ch02.kappaCoarse U a := by
            rw [book_kappaCoarse_eq_kappaCoarse U a]

private theorem adjoint_coarse_matrices {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    Book.Ch02.sigmaStarInvCoarse U a.transpose =
        Book.Ch02.sigmaStarInvCoarse U a ∧
      Book.Ch02.sigmaStarCoarse U a.transpose =
        Book.Ch02.sigmaStarCoarse U a ∧
      Book.Ch02.sigmaCoarse U a.transpose = Book.Ch02.sigmaCoarse U a ∧
      Book.Ch02.kappaCoarse U a.transpose = -Book.Ch02.kappaCoarse U a := by
  by_cases hd : d = 0
  · subst d
    refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hbEll :
        IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
      simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    rcases adjoint_coarse_matrices_of_isEllipticFieldOn U b hbEll with
      ⟨hSInv, hStar, hSigma, hKappa⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        Book.Ch02.sigmaStarInvCoarse U a.transpose =
            Book.Ch02.sigmaStarInvCoarse U b.transpose := by
              rw [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hba.transpose]
        _ = Book.Ch02.sigmaStarInvCoarse U b := hSInv
        _ = Book.Ch02.sigmaStarInvCoarse U a := by
              rw [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hba]
    · calc
        Book.Ch02.sigmaStarCoarse U a.transpose =
            Book.Ch02.sigmaStarCoarse U b.transpose := by
              rw [Book.Ch02.sigmaStarCoarse_eq_ofAEEq hba.transpose]
        _ = Book.Ch02.sigmaStarCoarse U b := hStar
        _ = Book.Ch02.sigmaStarCoarse U a := by
              rw [Book.Ch02.sigmaStarCoarse_eq_ofAEEq hba]
    · calc
        Book.Ch02.sigmaCoarse U a.transpose =
            Book.Ch02.sigmaCoarse U b.transpose := by
              rw [Book.Ch02.sigmaCoarse_eq_ofAEEq hba.transpose]
        _ = Book.Ch02.sigmaCoarse U b := hSigma
        _ = Book.Ch02.sigmaCoarse U a := by
              rw [Book.Ch02.sigmaCoarse_eq_ofAEEq hba]
    · calc
        Book.Ch02.kappaCoarse U a.transpose =
            Book.Ch02.kappaCoarse U b.transpose := by
              rw [Book.Ch02.kappaCoarse_eq_ofAEEq hba.transpose]
        _ = -Book.Ch02.kappaCoarse U b := hKappa
        _ = -Book.Ch02.kappaCoarse U a := by
              rw [Book.Ch02.kappaCoarse_eq_ofAEEq hba]

private theorem coarseBlockMatrix_transpose_eq_blockMatFlipFlux {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    Book.Ch02.coarseBlockMatrix U a.transpose =
      blockMatFlipFlux (Book.Ch02.coarseBlockMatrix U a) := by
  rcases adjoint_coarse_matrices U a with ⟨hSInv, _hStar, hSigma, hKappa⟩
  apply blockMat_ext
  · ext i j
    simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
      CoarseMatrices.b, blockMatFlipFlux, hSigma, hSInv, hKappa, matTranspose,
      Matrix.mul_apply]
  · ext i j
    simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
      CoarseMatrices.b, blockMatFlipFlux, hSInv, hKappa, matTranspose,
      Matrix.mul_apply]
  · ext i j
    simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
      CoarseMatrices.b, blockMatFlipFlux, hSInv, hKappa, matTranspose,
      Matrix.mul_apply]
  · ext i j
    simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
      CoarseMatrices.b, blockMatFlipFlux, hSInv]

private theorem doubled_block_quadratic_algebra {d : ℕ} (A : BlockMat d)
    (p q r s : Vec d) :
    (1 / 2 : ℝ) *
          ((1 / 2 : ℝ) *
              blockVecDot (s - p, r - q)
                (blockMatVecMul A (s - p, r - q)) -
            vecDot (p - s) (r - q)) +
        (1 / 2 : ℝ) *
          ((1 / 2 : ℝ) *
              blockVecDot (-(s + p), r + q)
                (blockMatVecMul (blockMatFlipFlux A) (-(s + p), r + q)) -
            vecDot (s + p) (r + q)) =
      (1 / 2 : ℝ) *
          blockVecDot (p, q) (blockMatVecMul A (p, q)) +
        (1 / 2 : ℝ) *
          blockVecDot (r, s)
            (blockMatVecMul (blockReflect A) (r, s)) -
        blockVecDot (p, q) (r, s) := by
  rcases A with ⟨ul, ur, ll, lr⟩
  simp [blockMatFlipFlux, blockReflect, blockMatVecMul, blockVecDot,
    matVecMul_add, matVecMul_neg, neg_matVecMul,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right,
    sub_eq_add_neg]
  rw [vecDot_comm s q]
  ring_nf

private theorem doubled_response_splitting {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d) :
    doubledResponseJ U a P Q =
      (1 / 2 : ℝ) *
          blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) +
        (1 / 2 : ℝ) *
          blockVecDot Q
            (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) -
        blockVecDot P Q := by
  rcases P with ⟨p, q⟩
  rcases Q with ⟨r, s⟩
  have hScalar :=
    (Book.Ch02.doubledResponseTheory U a).doubled_response_by_scalar p s q r
  have hJ1 := responseJ_eq_block_quadratic U a (p - s) (r - q)
  have hJ2 := responseJ_eq_block_quadratic U a.transpose (s + p) (r + q)
  calc
    doubledResponseJ U a (p, q) (r, s) =
        (1 / 2 : ℝ) * responseJ U a (p - s) (r - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (s + p) (r + q) := hScalar
    _ =
        (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) *
                blockVecDot (s - p, r - q)
                  (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (s - p, r - q)) -
              vecDot (p - s) (r - q)) +
          (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) *
                blockVecDot (-(s + p), r + q)
                  (blockMatVecMul (blockMatFlipFlux (Book.Ch02.coarseBlockMatrix U a))
                    (-(s + p), r + q)) -
              vecDot (s + p) (r + q)) := by
            rw [hJ1, hJ2, coarseBlockMatrix_transpose_eq_blockMatFlipFlux]
            simp [sub_eq_add_neg, add_comm]
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (p, q)
              (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) +
          (1 / 2 : ℝ) *
            blockVecDot (r, s)
              (blockMatVecMul (blockReflect (Book.Ch02.coarseBlockMatrix U a)) (r, s)) -
          blockVecDot (p, q) (r, s) :=
            doubled_block_quadratic_algebra (Book.Ch02.coarseBlockMatrix U a) p q r s
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (p, q)
              (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) +
          (1 / 2 : ℝ) *
            blockVecDot (r, s)
              (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) (r, s)) -
          blockVecDot (p, q) (r, s) := by
            rfl

private theorem block_matrix_subadditive {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i)),
      (∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i)) →
      BlockMatLoewnerLE (Book.Ch02.coarseBlockMatrix U a)
        (P.weightedBlockAverage fun i => Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i)) := by
  intro P aCell hCell X
  classical
  let : Fintype P.Cell := P.instFintype
  rcases X with ⟨p, q⟩
  have hSub :=
    (Book.Ch02.responseSubadditivityAndScalingTheory U a).responseJ_subadditive
      P aCell hCell (-p) q
  have hParent := responseJ_eq_block_quadratic U a (-p) q
  have hParent' :
      responseJ U a (-p) q =
        (1 / 2 : ℝ) *
            blockVecDot (p, q)
              (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) +
          vecDot p q := by
    rw [hParent]
    rw [vecDot_neg_left]
    simp [neg_neg]
  have hCells :
      ∀ i : P.Cell,
        responseJ (P.cell i) (aCell i) (-p) q =
          (1 / 2 : ℝ) *
              blockVecDot (p, q)
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i))
                  (p, q)) +
            vecDot p q := by
    intro i
    have h := responseJ_eq_block_quadratic (P.cell i) (aCell i) (-p) q
    rw [h]
    rw [vecDot_neg_left]
    simp [neg_neg]
  have hSub' :
      (1 / 2 : ℝ) *
            blockVecDot (p, q)
              (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) +
          vecDot p q ≤
        P.weightedAverage
          (fun i : P.Cell =>
            (1 / 2 : ℝ) *
                blockVecDot (p, q)
                  (blockMatVecMul
                    (Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i)) (p, q)) +
              vecDot p q) := by
    simpa [hParent', hCells] using hSub
  have hAvgConst :=
    weightedAverage_add_const P
      (fun i : P.Cell =>
        (1 / 2 : ℝ) *
          blockVecDot (p, q)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i)) (p, q)))
      (vecDot p q)
  have hClean :
      (1 / 2 : ℝ) *
          blockVecDot (p, q)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q)) ≤
        P.weightedAverage
          (fun i : P.Cell =>
            (1 / 2 : ℝ) *
              blockVecDot (p, q)
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i))
                  (p, q))) := by
    nlinarith [hSub', hAvgConst]
  calc
    (1 / 2 : ℝ) *
        blockVecDot (p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q))
      ≤ P.weightedAverage
          (fun i : P.Cell =>
            (1 / 2 : ℝ) *
              blockVecDot (p, q)
                (blockMatVecMul (Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i))
                  (p, q))) := hClean
    _ =
        (1 / 2 : ℝ) *
          blockVecDot (p, q)
            (blockMatVecMul
              (P.weightedBlockAverage
                fun i => Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i)) (p, q)) := by
          rw [← half_blockVecDot_blockMatVecMul_weightedBlockAverage]

private theorem starred_inverse_subadditive {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i)),
      (∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i)) →
      BlockMatLoewnerLE (Book.Ch02.coarseStarredBlockMatrixInv U a)
        (P.weightedBlockAverage fun i =>
          Book.Ch02.coarseStarredBlockMatrixInv (P.cell i) (aCell i)) := by
  intro P aCell hCell
  have hBlock := block_matrix_subadditive U a P aCell hCell
  have hReflect := BlockMatLoewnerLE_blockReflect hBlock
  rw [← weightedBlockAverage_blockReflect P
    (fun i => Book.Ch02.coarseBlockMatrix (P.cell i) (aCell i))] at hReflect
  simpa [Book.Ch02.coarseStarredBlockMatrixInv] using hReflect

theorem blockCoarseMatrixTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Book.Ch02.BlockCoarseMatrixTheory U a := by
  let hBlockPos : Book.Ch02.BlockPosDef (Book.Ch02.coarseBlockMatrix U a) :=
    coarseBlockMatrix_posDef U a
  let hStarInvPos : Book.Ch02.BlockPosDef
      (Book.Ch02.coarseStarredBlockMatrixInv U a) := by
    simpa [Book.Ch02.coarseStarredBlockMatrixInv] using
      blockPosDef_blockReflect hBlockPos
  let hStarInvSymm : IsSymmetricBlockMat
      (Book.Ch02.coarseStarredBlockMatrixInv U a) := by
    simpa [Book.Ch02.coarseStarredBlockMatrixInv] using
      isSymmetricBlockMat_blockReflect (coarseBlockMatrix_isSymmetricBlockMat U a)
  let hStarDet : IsUnit (toFullBlockMat
      (Book.Ch02.coarseStarredBlockMatrixInv U a)).det :=
    isUnit_det_toFullBlockMat_of_blockPosDef hStarInvPos
  rcases adjoint_coarse_matrices U a with ⟨_hSInvAdj, hStarAdj, hSigmaAdj, hKappaAdj⟩
  refine
    { doubled_response_splitting := ?_
      block_matrix_formula := ?_
      starred_inverse_formula := ?_
      block_matrix_posDef := hBlockPos
      starred_matrix_posDef := ?_
      starred_inverse_posDef := hStarInvPos
      starred_left_inverse := ?_
      starred_right_inverse := ?_
      block_matrix_subadditive := block_matrix_subadditive U a
      starred_inverse_subadditive := starred_inverse_subadditive U a
      adjoint_sigma := hSigmaAdj
      adjoint_sigmaStar := hStarAdj
      adjoint_kappa := hKappaAdj }
  · intro P Q
    exact doubled_response_splitting U a P Q
  · rfl
  · rfl
  · simpa [Book.Ch02.coarseStarredBlockMatrix] using
      blockMatInv_posDef_of_blockPosDef hStarInvSymm hStarInvPos
  · simpa [Book.Ch02.coarseStarredBlockMatrix] using
      blockMatMul_blockMatInv_left (Book.Ch02.coarseStarredBlockMatrixInv U a) hStarDet
  · simpa [Book.Ch02.coarseStarredBlockMatrix] using
      blockMatMul_blockMatInv_right (Book.Ch02.coarseStarredBlockMatrixInv U a) hStarDet

end BookCh02

end

end Ch02
end Internal
end Homogenization
