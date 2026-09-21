/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction

/-! # Matrix Positivity -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem sigmaStarInvCoarse_posDef_zero_dim (U : Domain 0)
    (a : CoeffOn U) :
    (Book.Ch02.sigmaStarInvCoarse U a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (Book.Ch02.sigmaStarInvCoarse_isSymm U a)
  · intro q hq
    exact False.elim (hq (Subsingleton.elim q 0))

theorem sigmaStarInvCoarse_posDef_of_isEllipticFieldOn {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    (Book.Ch02.sigmaStarInvCoarse U a).PosDef := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, _sigma0, compat, _hA, _hSInv, _hS, _hK, _hSigma, _hSigmaCanonical⟩
  have hPos :
      (Homogenization.sigmaStarInvCoarse
        (U : Set (Vec d)) a.toCoeffField).PosDef :=
    Homogenization.sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R U.isDomain hEll hvol compat
  simpa [book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a] using hPos

theorem sigmaStarInvCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (Book.Ch02.sigmaStarInvCoarse U a).PosDef := by
  by_cases hd : d = 0
  · subst d
    exact sigmaStarInvCoarse_posDef_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hb :
        (Book.Ch02.sigmaStarInvCoarse U b).PosDef :=
      sigmaStarInvCoarse_posDef_of_isEllipticFieldOn U b
        (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    simpa [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hba] using hb

theorem sigmaStarCoarse_posDef {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    (Book.Ch02.sigmaStarCoarse U a).PosDef := by
  unfold Book.Ch02.sigmaStarCoarse
  exact (sigmaStarInvCoarse_posDef U a).inv

theorem isUnit_det_sigmaStarInvCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    IsUnit (Book.Ch02.sigmaStarInvCoarse U a).det :=
  (Matrix.isUnit_iff_isUnit_det (A := Book.Ch02.sigmaStarInvCoarse U a)).mp
    (sigmaStarInvCoarse_posDef U a).isUnit

theorem isUnit_det_sigmaStarCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    IsUnit (Book.Ch02.sigmaStarCoarse U a).det :=
  (Matrix.isUnit_iff_isUnit_det (A := Book.Ch02.sigmaStarCoarse U a)).mp
    (sigmaStarCoarse_posDef U a).isUnit

theorem responseJ_nonneg {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) :
    0 ≤ responseJ U a p q := by
  rw [book_responseJ_eq_ResponseJ U a p q]
  exact Homogenization.responseJ_nonneg (U : Set (Vec d)) p q a.toCoeffField

end BookCh02

end

end Ch02
end Internal
end Homogenization
