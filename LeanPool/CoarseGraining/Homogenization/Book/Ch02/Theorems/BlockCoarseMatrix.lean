/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.BlockCoarseMatrix

/-! # Block Coarse Matrix -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 coarse block matrix theorem
`l.block.coarse.matrices.basic.definitions`. -/
theorem blockCoarseMatrixTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    BlockCoarseMatrixTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.blockCoarseMatrixTheory U a

end

end Ch02
end Book
end Homogenization
