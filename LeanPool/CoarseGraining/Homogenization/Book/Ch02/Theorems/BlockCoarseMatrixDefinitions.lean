/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponseDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScalingDefinitions

/-! # Block Coarse Matrix Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for `l.block.coarse.matrices.basic.definitions`.

This is the block-matrix surface that connects the doubled formalism back to
the scalar coarse matrices without exposing legacy coarse-data witnesses. The
canonical public theorem proving this package is `blockCoarseMatrixTheory` in
`BlockCoarseMatrix.lean`. -/
structure BlockCoarseMatrixTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Prop where
  doubled_response_splitting :
    ∀ P Q : BlockVec d,
      doubledResponseJ U a P Q =
        (1 / 2 : ℝ) *
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) +
          (1 / 2 : ℝ) *
            blockVecDot Q (blockMatVecMul (coarseStarredBlockMatrixInv U a) Q) -
          blockVecDot P Q
  block_matrix_formula :
    coarseBlockMatrix U a = blockMatrixOfCoarseMatrices (coarseMatrices U a)
  starred_inverse_formula :
    coarseStarredBlockMatrixInv U a = blockReflect (coarseBlockMatrix U a)
  block_matrix_posDef :
    BlockPosDef (coarseBlockMatrix U a)
  starred_matrix_posDef :
    BlockPosDef (coarseStarredBlockMatrix U a)
  starred_inverse_posDef :
    BlockPosDef (coarseStarredBlockMatrixInv U a)
  starred_left_inverse :
    blockMatMul (coarseStarredBlockMatrix U a) (coarseStarredBlockMatrixInv U a) =
      blockIdentity d
  starred_right_inverse :
    blockMatMul (coarseStarredBlockMatrixInv U a) (coarseStarredBlockMatrix U a) =
      blockIdentity d
  block_matrix_subadditive :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i)),
      (∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i)) →
      BlockMatLoewnerLE (coarseBlockMatrix U a)
        (P.weightedBlockAverage fun i => coarseBlockMatrix (P.cell i) (aCell i))
  starred_inverse_subadditive :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i)),
      (∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i)) →
      BlockMatLoewnerLE (coarseStarredBlockMatrixInv U a)
        (P.weightedBlockAverage fun i =>
          coarseStarredBlockMatrixInv (P.cell i) (aCell i))
  adjoint_sigma :
    sigmaCoarse U a.transpose = sigmaCoarse U a
  adjoint_sigmaStar :
    sigmaStarCoarse U a.transpose = sigmaStarCoarse U a
  adjoint_kappa :
    kappaCoarse U a.transpose = -kappaCoarse U a

end

end Ch02
end Book
end Homogenization
