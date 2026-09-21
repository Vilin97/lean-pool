/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixPositivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs

/-! # Matrix Positivity -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- The pure-flux coarse matrix `sigmaStarInv(U; a)` is positive definite. -/
theorem sigmaStarInvCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (sigmaStarInvCoarse U a).PosDef :=
  Homogenization.Internal.Ch02.BookCh02.sigmaStarInvCoarse_posDef U a

/-- The derived coarse matrix `sigmaStar(U; a)` is positive definite. -/
theorem sigmaStarCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (sigmaStarCoarse U a).PosDef :=
  Homogenization.Internal.Ch02.BookCh02.sigmaStarCoarse_posDef U a

/-- The canonical pure-flux matrix is invertible. -/
theorem isUnit_det_sigmaStarInvCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    IsUnit (sigmaStarInvCoarse U a).det :=
  Homogenization.Internal.Ch02.BookCh02.isUnit_det_sigmaStarInvCoarse U a

/-- The canonical `sigmaStar` matrix is invertible. -/
theorem isUnit_det_sigmaStarCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    IsUnit (sigmaStarCoarse U a).det :=
  Homogenization.Internal.Ch02.BookCh02.isUnit_det_sigmaStarCoarse U a

/-- The response functional is nonnegative. -/
theorem responseJ_nonneg {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) :
    0 ≤ responseJ U a p q :=
  Homogenization.Internal.Ch02.BookCh02.responseJ_nonneg U a p q

/-- Strict positivity of the pure-flux response away from `q = 0`. -/
theorem responseJ_zero_right_pos {d : ℕ} (U : Domain d) (a : CoeffOn U)
    {q : Vec d} (hq : q ≠ 0) :
    0 < responseJ U a 0 q := by
  have hformula :=
    responseJ_zero_q_eq_sigmaStarInvCoarse U a q
  have hquad :
      0 < vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (sigmaStarInvCoarse_posDef U a).dotProduct_mulVec_pos hq
  rw [hformula]
  nlinarith

end

end Ch02
end Book
end Homogenization
