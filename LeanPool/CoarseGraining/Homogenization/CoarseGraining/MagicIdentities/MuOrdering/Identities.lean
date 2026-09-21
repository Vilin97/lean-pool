/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.Matrix.Order
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.StarredSubadditivity

/-! # Identities -/

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- magic identities and sigmaStar <= sigma

The magic-identity theorems (block_quadratic, mu_sub_vecDot,
responseJ_add_mu_sub_vecDot and their shifted-square / canonical /
deterministic variants), sigmaStarCoarse <= sigmaCoarse on origin cubes,
and the kappa_add_transpose / sigmaStar <= sigma / sigmaStarCoarse <=
sigmaCoarse general orderings under isSigmaCoarse + mu_ge_vecDot or
IsEllipticFieldOn.
-/

theorem magic_identity_block_quadratic_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix
      ⟨deterministicCoarseBlockMatrix U a, hA⟩
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hShift :
      (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    simpa using magic_half_vecDot_sub_of_isSymm hSInvSymm q (matVecMul kappa p)
  have hCorr :
      vecDot (matVecMul kappa p) (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot p
          (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    symm
    exact vecDot_matVecMul_transpose p
      (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) kappa
  calc
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa) (p, q)) := by
      rw [coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet]
    _ =
      (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) +
        vecDot q (matVecMul (-(sigmaStar⁻¹ * kappa)) p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
      have hBlock0 :
          (1 / 2 : ℝ) * blockVecDot (p, q)
              (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
            (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) +
              vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
              (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) :=
        magic_half_blockVecDot_pos_left_of_isSymmetricBlockMat hAc.1 p q
      rw [coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet] at hBlock0
      have hBlock :
          (1 / 2 : ℝ) * blockVecDot (p, q)
              (blockMatVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa) (p, q)) =
            (1 / 2 : ℝ) * vecDot q
                (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerRight q) +
              vecDot q (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerLeft p) +
              (1 / 2 : ℝ) * vecDot p
                (matVecMul (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperLeft p) :=
        hBlock0
      simpa [blockMatrixOfDeterministicData] using hBlock
    _ = (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
      simp [sub_eq_add_neg, matVecMul_mul, neg_matVecMul, vecDot_neg_right]
    _ = (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
      rw [hShift, hCorr]
      unfold bCoarse
      rw [add_matVecMul, vecDot_add_right, matVecMul_mul, matVecMul_mul]
      ring_nf
      simp [Matrix.mul_assoc]

theorem magic_identity_block_quadratic_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_block_quadratic_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_block_quadratic_deterministicCoarseBlockMatrix_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (deterministicCoarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
  rw [← coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]
  exact magic_identity_block_quadratic_of_isSigmaCoarse
    U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_sub_vecDot_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
  calc
    Mu U (p, q) a - vecDot p q =
        (1 / 2 : ℝ) * blockVecDot (p, q)
          (blockMatVecMul (deterministicCoarseBlockMatrix U a) (p, q)) - vecDot p q := by
      rw [hA.2 (p, q)]
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
      rw [magic_identity_block_quadratic_deterministicCoarseBlockMatrix_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q]

theorem magic_identity_mu_sub_vecDot_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q := by
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix
      ⟨deterministicCoarseBlockMatrix U a, hA⟩
  calc
    Mu U (p, q) a - vecDot p q =
        (1 / 2 : ℝ) * blockVecDot (p, q)
          (blockMatVecMul (coarseBlockMatrix U a) (p, q)) - vecDot p q := by
      rw [hAc.2 (p, q)]
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
          vecDot p q := by
      rw [magic_identity_block_quadratic_canonical_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q]

theorem magic_identity_mu_sub_vecDot_shifted_square_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  calc
    Mu U (p, q) a - vecDot p q =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
      exact magic_identity_mu_sub_vecDot_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
      ring
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (magic_adjoint_shifted_square_eq_completed_square
          (sigma := sigma) (sigmaStar := sigmaStar) (kappa := kappa) hSInvSymm hdet p q)

theorem magic_identity_mu_sub_vecDot_shifted_square_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_mu_sub_vecDot_shifted_square_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_responseJ_add_mu_sub_vecDot_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q h : Vec d) :
    ResponseJ U p (q - h) a + (Mu U (p, q + h) a - vecDot p (q + h)) =
      vecDot p (matVecMul (sigma - sigmaStar) p) +
        vecDot (q - matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul sigmaStar p)) +
        vecDot (h - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (h - matVecMul kappa p)) := by
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hResp :=
    magic_identity_responseJ_shifted_square_of_isSigmaCoarse
      U a hS hK hSigma hdet p (q - h)
  have hMu :=
    magic_identity_mu_sub_vecDot_shifted_square_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p (q + h)
  have hSquare :
      (1 / 2 : ℝ) * vecDot ((q - matVecMul sigmaStar p) - (h - matVecMul kappa p))
          (matVecMul sigmaStar⁻¹
            ((q - matVecMul sigmaStar p) - (h - matVecMul kappa p))) +
        (1 / 2 : ℝ) * vecDot ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))
          (matVecMul sigmaStar⁻¹
            ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))) =
      vecDot (q - matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul sigmaStar p)) +
        vecDot (h - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (h - matVecMul kappa p)) := by
    simpa using magic_half_vecDot_sub_add_of_isSymm hSInvSymm
      (q - matVecMul sigmaStar p) (h - matVecMul kappa p)
  have hSub :
      q - h - matVecMul (sigmaStar - kappa) p =
        (q - matVecMul sigmaStar p) - (h - matVecMul kappa p) := by
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, add_assoc, add_left_comm, add_comm]
  have hAdd :
      q + h - matVecMul (sigmaStar + kappa) p =
        (q - matVecMul sigmaStar p) + (h - matVecMul kappa p) := by
    simp [sub_eq_add_neg, add_matVecMul, add_assoc, add_left_comm, add_comm]
  have hResp' :
      ResponseJ U p (q - h) a =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot ((q - matVecMul sigmaStar p) - (h - matVecMul kappa p))
            (matVecMul sigmaStar⁻¹
              ((q - matVecMul sigmaStar p) - (h - matVecMul kappa p))) := by
    simpa [hSub] using hResp
  have hMu' :
      Mu U (p, q + h) a - vecDot p (q + h) =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))
            (matVecMul sigmaStar⁻¹
              ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))) := by
    simpa [hAdd] using hMu
  linarith [hResp', hMu', hSquare]

theorem magic_identity_responseJ_add_mu_sub_vecDot_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q h : Vec d) :
    ResponseJ U p (q - h) a + (Mu U (p, q + h) a - vecDot p (q + h)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (sigmaStarCoarse U a) p)) +
        vecDot (h - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (h - matVecMul (kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_add_mu_sub_vecDot_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q h

theorem magic_identity_responseJ_add_mu_sub_vecDot_diagonal_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStar - kappa) p) a +
        (Mu U (p, matVecMul (sigmaStar + kappa) p) a -
          vecDot p (matVecMul (sigmaStar + kappa) p)) =
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  simpa [sub_eq_add_neg, add_matVecMul, neg_matVecMul, matVecMul_neg,
    vecDot_zero_left, vecDot_zero_right, matVecMul_zero, add_assoc] using
    magic_identity_responseJ_add_mu_sub_vecDot_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p (matVecMul sigmaStar p) (matVecMul kappa p)

theorem magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a +
        (Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
          vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_add_mu_sub_vecDot_diagonal_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p

theorem sigmaStarCoarse_le_sigmaCoarse_openCubeSet_originCube_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (openCubeSet (originCube d n)))
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu (openCubeSet (originCube d n)) P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse (openCubeSet (originCube d n)) a) p) ≤
      vecDot p (matVecMul (sigmaCoarse (openCubeSet (originCube d n)) a) p) := by
  have hdiag :=
    magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isSigmaCoarse
      (U := openCubeSet (originCube d n)) a hA hS hK hSigma hdet p
  have hResp :
      0 ≤ ResponseJ (openCubeSet (originCube d n)) p
        (matVecMul
          (sigmaStarCoarse (openCubeSet (originCube d n)) a -
            kappaCoarse (openCubeSet (originCube d n)) a) p) a :=
    responseJ_nonneg (openCubeSet (originCube d n)) p
      (matVecMul
        (sigmaStarCoarse (openCubeSet (originCube d n)) a -
          kappaCoarse (openCubeSet (originCube d n)) a) p) a
  have hMuGe :=
    R.mu_ge_vecDot_openCubeSet_originCube system hEll pairingIntegrable mu_eq_muCandidate
      (p, matVecMul
        (sigmaStarCoarse (openCubeSet (originCube d n)) a +
          kappaCoarse (openCubeSet (originCube d n)) a) p)
  have hMu :
      0 ≤ Mu (openCubeSet (originCube d n))
            (p, matVecMul
              (sigmaStarCoarse (openCubeSet (originCube d n)) a +
                kappaCoarse (openCubeSet (originCube d n)) a) p) a -
          vecDot p
            (matVecMul
              (sigmaStarCoarse (openCubeSet (originCube d n)) a +
                kappaCoarse (openCubeSet (originCube d n)) a) p) := by
    linarith
  have hDef :
      vecDot p
          (matVecMul
            (sigmaCoarse (openCubeSet (originCube d n)) a -
              sigmaStarCoarse (openCubeSet (originCube d n)) a) p) =
        vecDot p (matVecMul (sigmaCoarse (openCubeSet (originCube d n)) a) p) -
          vecDot p (matVecMul (sigmaStarCoarse (openCubeSet (originCube d n)) a) p) := by
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_neg_right]
  linarith

theorem sigmaStarCoarse_le_sigmaCoarse_cubeSet_originCube_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (cubeSet (originCube d n)))
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu (cubeSet (originCube d n)) P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (cubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (cubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse (cubeSet (originCube d n)) a) p) ≤
      vecDot p (matVecMul (sigmaCoarse (cubeSet (originCube d n)) a) p) := by
  have hdiag :=
    magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isSigmaCoarse
      (U := cubeSet (originCube d n)) a hA hS hK hSigma hdet p
  have hResp :
      0 ≤ ResponseJ (cubeSet (originCube d n)) p
        (matVecMul
          (sigmaStarCoarse (cubeSet (originCube d n)) a -
            kappaCoarse (cubeSet (originCube d n)) a) p) a :=
    responseJ_nonneg (cubeSet (originCube d n)) p
      (matVecMul
        (sigmaStarCoarse (cubeSet (originCube d n)) a -
          kappaCoarse (cubeSet (originCube d n)) a) p) a
  have hMuGe :=
    R.mu_ge_vecDot_cubeSet_originCube system hEll pairingIntegrable mu_eq_muCandidate
      (p, matVecMul
        (sigmaStarCoarse (cubeSet (originCube d n)) a +
          kappaCoarse (cubeSet (originCube d n)) a) p)
  have hMu :
      0 ≤ Mu (cubeSet (originCube d n))
            (p, matVecMul
              (sigmaStarCoarse (cubeSet (originCube d n)) a +
                kappaCoarse (cubeSet (originCube d n)) a) p) a -
          vecDot p
            (matVecMul
              (sigmaStarCoarse (cubeSet (originCube d n)) a +
                kappaCoarse (cubeSet (originCube d n)) a) p) := by
    linarith
  have hDef :
      vecDot p
          (matVecMul
            (sigmaCoarse (cubeSet (originCube d n)) a -
              sigmaStarCoarse (cubeSet (originCube d n)) a) p) =
        vecDot p (matVecMul (sigmaCoarse (cubeSet (originCube d n)) a) p) -
          vecDot p (matVecMul (sigmaStarCoarse (cubeSet (originCube d n)) a) p) := by
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_neg_right]
  linarith

theorem magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    Mu U (p, matVecMul (sigmaStar + kappa) p) a -
        vecDot p (matVecMul (sigmaStar + kappa) p) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) := by
  simpa [sub_eq_add_neg, add_matVecMul, neg_matVecMul, matVecMul_neg,
    vecDot_zero_left, vecDot_zero_right, matVecMul_zero, add_assoc] using
    magic_identity_mu_sub_vecDot_shifted_square_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p (matVecMul (sigmaStar + kappa) p)

theorem magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
        vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p

theorem kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse_of_mu_ge_vecDot {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a)
    (p : Vec d) :
    vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  have hMuGeP := hMuGe (p, matVecMul (sigmaStar + kappa) p)
  have hMu :
      0 ≤ Mu U (p, matVecMul (sigmaStar + kappa) p) a -
          vecDot p (matVecMul (sigmaStar + kappa) p) := by
    linarith
  have hSpecial :=
    magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p
  linarith

theorem kappa_add_transpose_le_sigma_sub_sigmaStar_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact R.mu_ge_vecDot_of_isEllipticFieldOn hU hEll hvol compat P
  exact kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a)
    (p : Vec d) :
    vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse_of_mu_ge_vecDot
      U a hA hS hK hSigma hdet hMuGe p

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact R.mu_ge_vecDot_of_isEllipticFieldOn hU hEll hvol compat P
  exact kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

theorem sigmaStar_le_sigma_of_isSigmaCoarse_of_mu_ge_vecDot {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a)
    (p : Vec d) :
    vecDot p (matVecMul sigmaStar p) ≤ vecDot p (matVecMul sigma p) := by
  have hdiag :=
    magic_identity_responseJ_add_mu_sub_vecDot_diagonal_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p
  have hResp :
      0 ≤ ResponseJ U p (matVecMul (sigmaStar - kappa) p) a :=
    responseJ_nonneg U p (matVecMul (sigmaStar - kappa) p) a
  have hMuGeP := hMuGe (p, matVecMul (sigmaStar + kappa) p)
  have hMu :
      0 ≤ Mu U (p, matVecMul (sigmaStar + kappa) p) a -
          vecDot p (matVecMul (sigmaStar + kappa) p) := by
    linarith
  have hDef :
      vecDot p (matVecMul (sigma - sigmaStar) p) =
        vecDot p (matVecMul sigma p) - vecDot p (matVecMul sigmaStar p) := by
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_neg_right]
  linarith

theorem sigmaStar_le_sigma_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul sigmaStar p) ≤ vecDot p (matVecMul sigma p) := by
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact R.mu_ge_vecDot_of_isEllipticFieldOn hU hEll hvol compat P
  exact sigmaStar_le_sigma_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

theorem sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    sigmaStar_le_sigma_of_isSigmaCoarse_of_mu_ge_vecDot
      U a hA hS hK hSigma hdet hMuGe p

theorem sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact R.mu_ge_vecDot_of_isEllipticFieldOn hU hEll hvol compat P
  exact sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

end

end Homogenization
