/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MagicIdentitiesDefinitions
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.Basics

/-! # Magic Identities -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem matLoewnerLE_zero_dim {A B : Mat 0} :
    MatLoewnerLE A B := by
  intro p
  have hp : p = 0 := Subsingleton.elim p 0
  subst p
  simp [vecDot, matVecMul]

private theorem responseJ_zero_zero_of_canonical_identities
    (U : Domain 0) (a : CoeffOn U) :
    responseJ U a 0 0 = 0 := by
  have hM : CanonicalResponseMatrixIdentities U a :=
    canonicalResponseMatrixIdentities U a
  have h := hM.sigmaStarInv_response (0 : Vec 0)
  simpa [vecDot, matVecMul] using h

private theorem responseMagicIdentitiesTheory_zero_dim
    (U : Domain 0) (a : CoeffOn U) :
    ResponseMagicIdentitiesTheory U a := by
  have hJ : responseJ U a (0 : Vec 0) (0 : Vec 0) = 0 :=
    responseJ_zero_zero_of_canonical_identities U a
  have hJAdj : responseJ U a.transpose (0 : Vec 0) (0 : Vec 0) = 0 :=
    responseJ_zero_zero_of_canonical_identities U a.transpose
  refine
    { completed_square := ?_
      adjoint_quadratic := ?_
      response_adjoint_sum := ?_
      diagonal_magic := ?_
      sigmaStar_le_sigma := matLoewnerLE_zero_dim
      kappa_symm_le_defect := matLoewnerLE_zero_dim
      neg_kappa_symm_le_defect := matLoewnerLE_zero_dim }
  · intro p q
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    simpa [vecDot, matVecMul, hJ]
  · intro p q
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    simpa [vecDot, matVecMul, hJAdj]
  · intro p q h
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    have hh : h = 0 := Subsingleton.elim h 0
    subst p
    subst q
    subst h
    have hJa : responseJ U a (0 : Vec 0) ((0 : Vec 0) - 0) = 0 := by
      simpa using hJ
    have hJb : responseJ U a.transpose (0 : Vec 0) ((0 : Vec 0) + 0) = 0 := by
      simpa using hJAdj
    rw [hJa, hJb]
    simp [vecDot, matVecMul]
  · intro e
    have he : e = 0 := Subsingleton.elim e 0
    subst e
    have hJa :
        responseJ U a (0 : Vec 0)
          (matVecMul (Book.Ch02.sigmaStarCoarse U a - Book.Ch02.kappaCoarse U a)
            (0 : Vec 0)) = 0 := by
      simpa [matVecMul] using! hJ
    have hJb :
        responseJ U a.transpose (0 : Vec 0)
          (matVecMul (Book.Ch02.sigmaStarCoarse U a + Book.Ch02.kappaCoarse U a)
            (0 : Vec 0)) = 0 := by
      simpa [matVecMul] using! hJAdj
    rw [hJa, hJb]
    simp [vecDot, matVecMul]

private theorem responseMagicIdentitiesTheory_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseMagicIdentitiesTheory U a := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨_R, _sigma0, _compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hEllAdj :
      IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
        (adjointCoeffField a.toCoeffField) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEllAdj hvol with
    ⟨_RAdj, _sigmaAdj, _compatAdj, hAAdj, _hSInvAdj, hSAdj0, hKAdj0,
      hSigmaAdj0, _hSigmaCanonicalAdj⟩
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det := by
    exact
      isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) _R U.isDomain hEll hvol
        _compat hS
  have hStarAdjEq :
      Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaStarCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hKappaAdjEq :
      Homogenization.kappaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        -(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
    kappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hSigmaAdjEq :
      Homogenization.sigmaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hdetAdj : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d))
        (adjointCoeffField a.toCoeffField)).det := by
    simpa [hStarAdjEq] using hdet
  have hSigmaCanon :
      IsSigmaCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using hSigma
  have hSAdj :
      IsSigmaStarCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [hStarAdjEq] using hSAdj0
  have hKAdj :
      IsKappaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (-(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) := by
    simpa [hStarAdjEq, hKappaAdjEq] using hKAdj0
  have hSigmaAdjCanon0 :
      IsSigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField))
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField))
        (Homogenization.kappaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)) := by
    simpa [sigmaCoarse_eq_of_isSigmaCoarse hSAdj0 hKAdj0 hSigmaAdj0 hdetAdj]
      using hSigmaAdj0
  have hSigmaAdj :
      IsSigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (-(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) := by
    simpa [hSigmaAdjEq, hStarAdjEq, hKappaAdjEq] using hSigmaAdjCanon0
  refine
    { completed_square := ?_
      adjoint_quadratic := ?_
      response_adjoint_sum := ?_
      diagonal_magic := ?_
      sigmaStar_le_sigma := ?_
      kappa_symm_le_defect := ?_
      neg_kappa_symm_le_defect := ?_ }
  · intro p q
    calc
      responseJ U a p q =
          ResponseJ (U : Set (Vec d)) p q a.toCoeffField :=
        book_responseJ_eq_ResponseJ U a p q
      _ =
          (1 / 2 : ℝ) *
            vecDot p
              (matVecMul
                (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                  Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p) +
            (1 / 2 : ℝ) *
              vecDot p
                (matVecMul
                  (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField +
                    matTranspose
                      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) p) +
            (1 / 2 : ℝ) *
              vecDot
                (q -
                  matVecMul
                    (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField -
                      Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
                (matVecMul
                  (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                  (q -
                    matVecMul
                      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField -
                        Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
        magic_identity_responseJ_shifted_square_canonical_of_isSigmaCoarse
          (U := (U : Set (Vec d))) (a := a.toCoeffField) hS hK hSigmaCanon hdet p q
      _ =
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
          (1 / 2 : ℝ) *
            vecDot p
              (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
          (1 / 2 : ℝ) *
            vecDot
              (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p)
              (matVecMul (sigmaStarInvCoarse U a)
                (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p)) := by
        rw [← book_sigmaCoarse_eq_sigmaCoarse U a,
          ← book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a,
          ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
  · intro p q
    calc
      responseJ U a.transpose p q =
          ResponseJ (U : Set (Vec d)) p q (adjointCoeffField a.toCoeffField) := by
        rw [book_responseJ_eq_ResponseJ U a.transpose p q]
        rfl
      _ =
          (1 / 2 : ℝ) *
              vecDot p
                (matVecMul
                  (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) p) -
            vecDot p q +
            (1 / 2 : ℝ) *
              vecDot
                (q -
                  matVecMul
                    (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
                (matVecMul
                  (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹
                  (q -
                    matVecMul
                      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
        magic_identity_responseJ_adjoint_completed_square_of_isSigmaCoarse
          (U := (U : Set (Vec d))) (a := a.toCoeffField)
          hSAdj hKAdj hSigmaAdj hdet p q
      _ =
          (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
          (1 / 2 : ℝ) *
            vecDot (q - matVecMul (kappaCoarse U a) p)
              (matVecMul (sigmaStarInvCoarse U a)
                (q - matVecMul (kappaCoarse U a) p)) -
          vecDot p q := by
        rw [← sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
          ← book_sigmaCoarse_eq_sigmaCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a,
          ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
        ring
  · intro p q h
    calc
      responseJ U a p (q - h) + responseJ U a.transpose p (q + h) =
          ResponseJ (U : Set (Vec d)) p (q - h) a.toCoeffField +
            ResponseJ (U : Set (Vec d)) p (q + h)
              (adjointCoeffField a.toCoeffField) := by
        rw [book_responseJ_eq_ResponseJ U a p (q - h),
          book_responseJ_eq_ResponseJ U a.transpose p (q + h)]
        rfl
      _ =
          vecDot p
              (matVecMul
                (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                  Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p) +
            vecDot
              (q -
                matVecMul
                  (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p)
              (matVecMul
                (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                (q -
                  matVecMul
                    (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p)) +
            vecDot
              (h -
                matVecMul
                  (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
              (matVecMul
                (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                (h -
                  matVecMul
                    (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
        magic_identity_responseJ_adjoint_sum_canonical_of_isSigmaCoarse
          (U := (U : Set (Vec d))) (a := a.toCoeffField)
          hS hK hSigmaCanon hSAdj hKAdj hSigmaAdj hdet p q h
      _ =
          vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
          vecDot (q - matVecMul (sigmaStarCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q - matVecMul (sigmaStarCoarse U a) p)) +
          vecDot (h - matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (h - matVecMul (kappaCoarse U a) p)) := by
        rw [← book_sigmaCoarse_eq_sigmaCoarse U a,
          ← book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a,
          ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
  · intro e
    calc
      responseJ U a e
          (matVecMul (Book.Ch02.sigmaStarCoarse U a - Book.Ch02.kappaCoarse U a) e) +
          responseJ U a.transpose e
            (matVecMul (Book.Ch02.sigmaStarCoarse U a + Book.Ch02.kappaCoarse U a) e) =
          ResponseJ (U : Set (Vec d)) e
              (matVecMul
                (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField -
                  Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) e)
              a.toCoeffField +
            ResponseJ (U : Set (Vec d)) e
              (matVecMul
                (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField +
                  Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) e)
              (adjointCoeffField a.toCoeffField) := by
        rw [book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
          book_kappaCoarse_eq_kappaCoarse U a,
          book_responseJ_eq_ResponseJ U a e
            (matVecMul
              (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField -
                Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) e),
          book_responseJ_eq_ResponseJ U a.transpose e
            (matVecMul
              (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField +
                Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) e)]
        rfl
      _ =
          vecDot e
            (matVecMul
              (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) e) :=
        magic_identity_responseJ_adjoint_diagonal_canonical_of_isSigmaCoarse
          (U := (U : Set (Vec d))) (a := a.toCoeffField)
          hS hK hSigmaCanon hSAdj hKAdj hSigmaAdj hdet e
      _ =
          vecDot e (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) e) := by
        rw [← book_sigmaCoarse_eq_sigmaCoarse U a,
          ← book_sigmaStarCoarse_eq_sigmaStarCoarse U a]
  · intro p
    change
      (1 / 2 : ℝ) *
          vecDot p (matVecMul (Book.Ch02.sigmaStarCoarse U a) p) ≤
        (1 / 2 : ℝ) *
          vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p)
    rw [book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
      book_sigmaCoarse_eq_sigmaCoarse U a]
    have h :=
      sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse
        (U := (U : Set (Vec d))) (a := a.toCoeffField)
        hS hK hSigmaCanon hSAdj hKAdj hSigmaAdj hdet p
    nlinarith
  · intro p
    change
      (1 / 2 : ℝ) *
          vecDot p
            (matVecMul
              (Book.Ch02.kappaCoarse U a + matTranspose (Book.Ch02.kappaCoarse U a)) p) ≤
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (Book.Ch02.sigmaCoarse U a - Book.Ch02.sigmaStarCoarse U a) p)
    rw [book_kappaCoarse_eq_kappaCoarse U a,
      book_sigmaCoarse_eq_sigmaCoarse U a,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a]
    have h :=
      kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse
        (U := (U : Set (Vec d))) (a := a.toCoeffField)
        hS hK hSigmaCanon hSAdj hKAdj hSigmaAdj hdet p
    nlinarith
  · intro p
    change
      (1 / 2 : ℝ) *
          vecDot p
            (matVecMul
              (-(Book.Ch02.kappaCoarse U a + matTranspose (Book.Ch02.kappaCoarse U a))) p) ≤
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (Book.Ch02.sigmaCoarse U a - Book.Ch02.sigmaStarCoarse U a) p)
    rw [book_kappaCoarse_eq_kappaCoarse U a,
      book_sigmaCoarse_eq_sigmaCoarse U a,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a]
    simp only [neg_matVecMul, vecDot_neg_right]
    have h :=
      neg_kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse
        (U := (U : Set (Vec d))) (a := a.toCoeffField)
        hS hK hSigmaCanon hdet p
    nlinarith

private theorem responseMagicIdentitiesTheory_of_neZero
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U) :
    ResponseMagicIdentitiesTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hb : ResponseMagicIdentitiesTheory U b :=
    responseMagicIdentitiesTheory_of_isEllipticFieldOn U b
      (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseMagicIdentitiesTheory.ofAEEq hba hb

theorem responseMagicIdentitiesTheory
    {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseMagicIdentitiesTheory U a := by
  by_cases hd : d = 0
  · subst d
    exact responseMagicIdentitiesTheory_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    exact responseMagicIdentitiesTheory_of_neZero U a

end BookCh02

end

end Ch02
end Internal
end Homogenization
