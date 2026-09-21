/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction

/-! # Magic Identities Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for `l.magic.identities.basic.definitions`.

The canonical public theorem proving this package is
`responseMagicIdentitiesTheory` in `MagicIdentities.lean`. -/
structure ResponseMagicIdentitiesTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Prop where
  completed_square :
    ∀ p q : Vec d,
      responseJ U a p q =
        (1 / 2 : ℝ) *
          vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) *
          vecDot
            (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p))
  adjoint_quadratic :
    ∀ p q : Vec d,
      responseJ U a.transpose p q =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q
  response_adjoint_sum :
    ∀ p q h : Vec d,
      responseJ U a p (q - h) + responseJ U a.transpose p (q + h) =
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a) p)) +
        vecDot (h - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (h - matVecMul (kappaCoarse U a) p))
  diagonal_magic :
    ∀ e : Vec d,
      responseJ U a e (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) e) +
          responseJ U a.transpose e
            (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) e) =
        vecDot e (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) e)
  sigmaStar_le_sigma :
    MatLoewnerLE (sigmaStarCoarse U a) (sigmaCoarse U a)
  kappa_symm_le_defect :
    MatLoewnerLE
      (kappaCoarse U a + matTranspose (kappaCoarse U a))
      (sigmaCoarse U a - sigmaStarCoarse U a)
  neg_kappa_symm_le_defect :
    MatLoewnerLE
      (-(kappaCoarse U a + matTranspose (kappaCoarse U a)))
      (sigmaCoarse U a - sigmaStarCoarse U a)

namespace ResponseMagicIdentitiesTheory

/-- The magic identities depend only on the public coefficient representative
up to a.e. equality on the domain. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hTheory : ResponseMagicIdentitiesTheory U a) :
    ResponseMagicIdentitiesTheory U b where
  completed_square := by
    intro p q
    simpa [responseJ_eq_ofAEEq h p q, sigmaCoarse_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h, kappaCoarse_eq_ofAEEq h,
      sigmaStarInvCoarse_eq_ofAEEq h] using hTheory.completed_square p q
  adjoint_quadratic := by
    intro p q
    simpa [responseJ_eq_ofAEEq h.transpose p q, sigmaCoarse_eq_ofAEEq h,
      kappaCoarse_eq_ofAEEq h, sigmaStarInvCoarse_eq_ofAEEq h] using
      hTheory.adjoint_quadratic p q
  response_adjoint_sum := by
    intro p q k
    simpa [responseJ_eq_ofAEEq h p (q - k),
      responseJ_eq_ofAEEq h.transpose p (q + k), sigmaCoarse_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h, kappaCoarse_eq_ofAEEq h,
      sigmaStarInvCoarse_eq_ofAEEq h] using
      hTheory.response_adjoint_sum p q k
  diagonal_magic := by
    intro e
    simpa [responseJ_eq_ofAEEq h e
        (matVecMul (sigmaStarCoarse U b - kappaCoarse U b) e),
      responseJ_eq_ofAEEq h.transpose e
        (matVecMul (sigmaStarCoarse U b + kappaCoarse U b) e),
      sigmaCoarse_eq_ofAEEq h, sigmaStarCoarse_eq_ofAEEq h,
      kappaCoarse_eq_ofAEEq h] using hTheory.diagonal_magic e
  sigmaStar_le_sigma := by
    simpa [sigmaStarCoarse_eq_ofAEEq h, sigmaCoarse_eq_ofAEEq h] using
      hTheory.sigmaStar_le_sigma
  kappa_symm_le_defect := by
    simpa [sigmaCoarse_eq_ofAEEq h, sigmaStarCoarse_eq_ofAEEq h,
      kappaCoarse_eq_ofAEEq h] using hTheory.kappa_symm_le_defect
  neg_kappa_symm_le_defect := by
    simpa [sigmaCoarse_eq_ofAEEq h, sigmaStarCoarse_eq_ofAEEq h,
      kappaCoarse_eq_ofAEEq h] using hTheory.neg_kappa_symm_le_defect

/-- A.e.-equivalent coefficient representatives satisfy the same magic
identity package. -/
theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseMagicIdentitiesTheory U a ↔ ResponseMagicIdentitiesTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseMagicIdentitiesTheory

end

end Ch02
end Book
end Homogenization
