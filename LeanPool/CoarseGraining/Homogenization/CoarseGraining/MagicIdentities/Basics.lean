/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Subadditivity
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! # Basics -/

namespace Homogenization

noncomputable section

/-!
Foundational completed-square identities and ordering consequences.
-/

theorem magic_vecDot_matVecMul_comm_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    vecDot ξ (matVecMul A η) = vecDot η (matVecMul A ξ) := by
  calc
    vecDot ξ (matVecMul A η) = vecDot ξ (matVecMul (matTranspose A) η) := by
      rw [show matTranspose A = A by simpa [matTranspose] using hA.eq]
    _ = vecDot (matVecMul A ξ) η := by
      rw [vecDot_matVecMul_transpose]
    _ = vecDot η (matVecMul A ξ) := by
      rw [vecDot_comm]

theorem magic_half_vecDot_add_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    (1 / 2 : ℝ) * vecDot (ξ + η) (matVecMul A (ξ + η)) =
      (1 / 2 : ℝ) * vecDot ξ (matVecMul A ξ) +
        vecDot ξ (matVecMul A η) +
        (1 / 2 : ℝ) * vecDot η (matVecMul A η) := by
  have hcomm := magic_vecDot_matVecMul_comm_of_isSymm hA ξ η
  simp [matVecMul_add, vecDot_add_left, vecDot_add_right, hcomm]
  ring

theorem magic_half_vecDot_sub_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    (1 / 2 : ℝ) * vecDot (ξ - η) (matVecMul A (ξ - η)) =
      (1 / 2 : ℝ) * vecDot ξ (matVecMul A ξ) -
        vecDot ξ (matVecMul A η) +
        (1 / 2 : ℝ) * vecDot η (matVecMul A η) := by
  simpa [sub_eq_add_neg, matVecMul_neg, vecDot_neg_left, vecDot_neg_right] using
    magic_half_vecDot_add_of_isSymm hA ξ (-η)

theorem magic_adjoint_shifted_square_eq_completed_square {d : ℕ}
    {sigma sigmaStar kappa : Mat d} (hSInvSymm : (sigmaStar⁻¹).IsSymm)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
      (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
        (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
  have hSub :
      (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    simpa using magic_half_vecDot_sub_of_isSymm hSInvSymm q (matVecMul kappa p)
  have hShift :
      (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar + kappa) p)
            (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)) := by
    simpa using
      magic_half_vecDot_sub_of_isSymm hSInvSymm q (matVecMul (sigmaStar + kappa) p)
  have hInvMul : matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p) = p := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul sigmaStar hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hInvShift :
      matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p) =
        p + matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
    calc
      matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)
          = matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p) +
            matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
              rw [add_matVecMul, matVecMul_add]
      _ = p + matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
              rw [hInvMul]
  have hCross :
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)) =
        vecDot p q + vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    rw [hInvShift]
    simp [vecDot_add_right, vecDot_comm]
  have hKsym :
      (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) =
        vecDot p (matVecMul kappa p) := by
    have ht :
        vecDot p (matVecMul (matTranspose kappa) p) =
          vecDot p (matVecMul kappa p) := by
      calc
        vecDot p (matVecMul (matTranspose kappa) p) =
            vecDot (matVecMul kappa p) p := by
              rw [vecDot_matVecMul_transpose]
        _ = vecDot p (matVecMul kappa p) := by
              rw [vecDot_comm]
    rw [add_matVecMul, vecDot_add_right, ht]
    ring
  have hKpair :
      vecDot p (matVecMul (kappa + matTranspose kappa) p) =
        2 * vecDot p (matVecMul kappa p) := by
    linarith [hKsym]
  have hTailSigma :
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) =
        vecDot p (matVecMul sigmaStar p) := by
    rw [hInvMul, vecDot_comm]
  have hTailCross :
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot p (matVecMul kappa p) := by
    calc
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
            vecDot (matVecMul kappa p)
              (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) := by
                rw [magic_vecDot_matVecMul_comm_of_isSymm hSInvSymm
                  (matVecMul sigmaStar p) (matVecMul kappa p)]
      _ = vecDot (matVecMul kappa p) p := by
            rw [hInvMul]
      _ = vecDot p (matVecMul kappa p) := by
            rw [vecDot_comm]
  have hTailCorr :
      vecDot (matVecMul kappa p) (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot p
          (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    symm
    exact vecDot_matVecMul_transpose p
      (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) kappa
  have hTail :
      (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)) =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigmaStar p) +
          vecDot p (matVecMul kappa p) +
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    calc
      (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar + kappa) p)) =
        (1 / 2 : ℝ) * vecDot (matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) +
          vecDot (matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
              simpa [add_matVecMul] using
                magic_half_vecDot_add_of_isSymm hSInvSymm
                  (matVecMul sigmaStar p) (matVecMul kappa p)
      _ = (1 / 2 : ℝ) * vecDot p (matVecMul sigmaStar p) +
            vecDot p (matVecMul kappa p) +
            (1 / 2 : ℝ) * vecDot p
              (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
              rw [hTailSigma, hTailCross, hTailCorr]
  have hMagic :
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
    rw [hSub, hShift, hCross, hTail, ← hTailCorr, hKpair]
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_neg_right]
    ring_nf
  exact hMagic.symm

theorem magic_half_vecDot_sub_add_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    (1 / 2 : ℝ) * vecDot (ξ - η) (matVecMul A (ξ - η)) +
        (1 / 2 : ℝ) * vecDot (ξ + η) (matVecMul A (ξ + η)) =
      vecDot ξ (matVecMul A ξ) +
        vecDot η (matVecMul A η) := by
  have hsub := magic_half_vecDot_sub_of_isSymm hA ξ η
  have hadd := magic_half_vecDot_add_of_isSymm hA ξ η
  linarith

theorem magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat {d : ℕ}
    {B : BlockMat d} (hB : IsSymmetricBlockMat B) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul B (-p, q)) =
      (1 / 2 : ℝ) * vecDot q (matVecMul B.lowerRight q) -
        vecDot q (matVecMul B.lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul B.upperLeft p) := by
  have hur :
      matTranspose B.upperRight = B.lowerLeft := by
    ext i j
    simpa [matTranspose, blockMatEntry] using (hB (Sum.inr i) (Sum.inl j)).symm
  have hcross :
      vecDot p (matVecMul B.upperRight q) =
        vecDot q (matVecMul B.lowerLeft p) := by
    calc
      vecDot p (matVecMul B.upperRight q) =
          vecDot (matVecMul B.upperRight q) p := by
            rw [vecDot_comm]
      _ = vecDot q (matVecMul (matTranspose B.upperRight) p) := by
            symm
            exact vecDot_matVecMul_transpose q p B.upperRight
      _ = vecDot q (matVecMul B.lowerLeft p) := by
            rw [hur]
  simp [blockVecDot, blockMatVecMul, matVecMul_neg,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcross]
  ring

theorem magic_half_blockVecDot_pos_left_of_isSymmetricBlockMat {d : ℕ}
    {B : BlockMat d} (hB : IsSymmetricBlockMat B) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q) (blockMatVecMul B (p, q)) =
      (1 / 2 : ℝ) * vecDot q (matVecMul B.lowerRight q) +
        vecDot q (matVecMul B.lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul B.upperLeft p) := by
  simpa [matVecMul_neg, vecDot_neg_left, vecDot_neg_right] using
    magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hB (-p) q

theorem magic_identity_sigmaCorrectedResponse_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    sigmaCorrectedResponse U a p = (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) := by
  exact (isSigmaCanonicalCoarse_of_isSigmaCoarse hS hK hSigma hdet).2 p

theorem magic_identity_responseJ_completed_square_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      sigmaCorrectedResponse U a p - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p)) := by
  have hResp :=
    basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p q
  have hZero :=
    basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p
  have hSymm : (sigmaStarInvCoarse U a).IsSymm := by
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
    exact (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hShift :
      (1 / 2 : ℝ) * vecDot (q + matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) +
          vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) := by
    simpa using
      magic_half_vecDot_add_of_isSymm hSymm q (matVecMul (kappaCoarse U a) p)
  have hCorr :
      vecDot (matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) =
        vecDot p
          (matVecMul (matTranspose (kappaCoarse U a))
            (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p))) := by
    symm
    exact vecDot_matVecMul_transpose p
      (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p))
      (kappaCoarse U a)
  have hResp' :
      ResponseJ U p q a =
        ResponseJ U p 0 a - vecDot p q +
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) +
          vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) := by
    linarith
  calc
    ResponseJ U p q a =
        ResponseJ U p 0 a - vecDot p q +
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) +
          vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) := hResp'
    _ = sigmaCorrectedResponse U a p - vecDot p q +
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) +
          vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) +
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (matTranspose (kappaCoarse U a))
              (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p))) := by
      rw [sigmaCorrectedResponse]
      ring
    _ = sigmaCorrectedResponse U a p - vecDot p q +
          (1 / 2 : ℝ) * vecDot (q + matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p)) := by
      rw [hShift, hCorr]
      ring

theorem magic_identity_responseJ_completed_square_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    magic_identity_sigmaCorrectedResponse_of_isSigmaCoarse U a hS hK hSigma hdet p] using
    magic_identity_responseJ_completed_square_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p q

theorem magic_identity_responseJ_shifted_square_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar - kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar - kappa) p)) := by
  have hResp :=
    magic_identity_responseJ_completed_square_of_isSigmaCoarse
      U a hS hK hSigma hdet p q
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  have hAdd :
      (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) +
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    simpa using magic_half_vecDot_add_of_isSymm hSInvSymm q (matVecMul kappa p)
  have hShift :
      (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar - kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar - kappa) p)) =
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot q (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar - kappa) p)
            (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)) := by
    simpa using
      magic_half_vecDot_sub_of_isSymm hSInvSymm q (matVecMul (sigmaStar - kappa) p)
  have hInvMul : matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p) = p := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul sigmaStar hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hNegK : matVecMul (-kappa) p = -matVecMul kappa p := by
    rw [neg_matVecMul]
  have hInvShift :
      matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p) =
        p - matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
    calc
      matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)
          = matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p) -
            matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
              rw [sub_eq_add_neg, add_matVecMul, hNegK]
              rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
      _ = p - matVecMul sigmaStar⁻¹ (matVecMul kappa p) := by
              simpa [sub_eq_add_neg] using congrArg (fun v => v - matVecMul sigmaStar⁻¹ (matVecMul kappa p)) hInvMul
  have hCross :
      vecDot q (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)) =
        vecDot p q - vecDot q (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
    rw [hInvShift]
    simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, vecDot_comm]
  have hKsym :
      (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) =
        vecDot p (matVecMul kappa p) := by
    have ht :
        vecDot p (matVecMul (matTranspose kappa) p) =
          vecDot p (matVecMul kappa p) := by
      calc
        vecDot p (matVecMul (matTranspose kappa) p) =
            vecDot (matVecMul kappa p) p := by
              rw [vecDot_matVecMul_transpose]
        _ = vecDot p (matVecMul kappa p) := by
              rw [vecDot_comm]
    rw [add_matVecMul, vecDot_add_right, ht]
    ring
  have hTailSigma :
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) =
        vecDot p (matVecMul sigmaStar p) := by
    rw [hInvMul, vecDot_comm]
  have hTailCross :
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot p (matVecMul kappa p) := by
    calc
      vecDot (matVecMul sigmaStar p)
          (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
            vecDot (matVecMul kappa p)
              (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) := by
                rw [magic_vecDot_matVecMul_comm_of_isSymm hSInvSymm
                  (matVecMul sigmaStar p) (matVecMul kappa p)]
      _ = vecDot (matVecMul kappa p) p := by
            rw [hInvMul]
      _ = vecDot p (matVecMul kappa p) := by
            rw [vecDot_comm]
  have hTailCorr :
      vecDot (matVecMul kappa p) (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) =
        vecDot p
          (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    symm
    exact vecDot_matVecMul_transpose p
      (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) kappa
  have hTail :
      (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar - kappa) p)
          (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)) =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigmaStar p) -
          vecDot p (matVecMul kappa p) +
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
    calc
      (1 / 2 : ℝ) * vecDot (matVecMul (sigmaStar - kappa) p)
          (matVecMul sigmaStar⁻¹ (matVecMul (sigmaStar - kappa) p)) =
        (1 / 2 : ℝ) * vecDot (matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (matVecMul sigmaStar p)) -
          vecDot (matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) +
          (1 / 2 : ℝ) * vecDot (matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (matVecMul kappa p)) := by
              simpa [sub_eq_add_neg, add_matVecMul, hNegK] using
                magic_half_vecDot_sub_of_isSymm hSInvSymm
                  (matVecMul sigmaStar p) (matVecMul kappa p)
      _ = (1 / 2 : ℝ) * vecDot p (matVecMul sigmaStar p) -
            vecDot p (matVecMul kappa p) +
            (1 / 2 : ℝ) * vecDot p
              (matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (matVecMul kappa p))) := by
              rw [hTailSigma, hTailCross, hTailCorr]
  have hMagic :
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar - kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar - kappa) p)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) := by
    have hNegSigma :
        vecDot p (matVecMul (-sigmaStar) p) = -vecDot p (matVecMul sigmaStar p) := by
      rw [neg_matVecMul, vecDot_neg_right]
    rw [hAdd, hShift, hCross, hKsym, hTail, ← hTailCorr]
    rw [sub_eq_add_neg, add_matVecMul, vecDot_add_right, hNegSigma]
    ring_nf
  calc
    ResponseJ U p q a =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
          (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) := hResp
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar - kappa) p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar - kappa) p)) := by
      symm
      exact hMagic

theorem magic_identity_responseJ_shifted_square_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_shifted_square_of_isSigmaCoarse
      U a hS hK hSigma hdet p q

theorem magic_identity_responseJ_adjoint_completed_square_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hK : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigma : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q (adjointCoeffField a) =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
  simpa [sub_eq_add_neg, neg_matVecMul] using
    magic_identity_responseJ_completed_square_of_isSigmaCoarse
      U (adjointCoeffField a) hS hK hSigma hdet p q

theorem magic_identity_responseJ_adjoint_shifted_square_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hK : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigma : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q (adjointCoeffField a) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  calc
    ResponseJ U p q (adjointCoeffField a) =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
      exact magic_identity_responseJ_adjoint_completed_square_of_isSigmaCoarse
        U a hS hK hSigma hdet p q
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (magic_adjoint_shifted_square_eq_completed_square
          (sigma := sigma) (sigmaStar := sigmaStar) (kappa := kappa) hSInvSymm hdet p q)

theorem magic_identity_responseJ_adjoint_sum_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p q h : Vec d) :
    ResponseJ U p (q - h) a + ResponseJ U p (q + h) (adjointCoeffField a) =
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
  have hAdj :=
    magic_identity_responseJ_adjoint_shifted_square_of_isSigmaCoarse
      U a hSAdj hKAdj hSigmaAdj hdet p (q + h)
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
  have hAdj' :
      ResponseJ U p (q + h) (adjointCoeffField a) =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))
            (matVecMul sigmaStar⁻¹
              ((q - matVecMul sigmaStar p) + (h - matVecMul kappa p))) := by
    simpa [hAdd] using hAdj
  linarith [hResp', hAdj', hSquare]

theorem magic_identity_responseJ_adjoint_sum_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p q h : Vec d) :
    ResponseJ U p (q - h) a + ResponseJ U p (q + h) (adjointCoeffField a) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (sigmaStarCoarse U a) p)) +
        vecDot (h - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (h - matVecMul (kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_adjoint_sum_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p q h

theorem magic_identity_responseJ_adjoint_diagonal_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStar - kappa) p) a +
        ResponseJ U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a) =
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  simpa [sub_eq_add_neg, add_matVecMul, neg_matVecMul, matVecMul_neg,
    vecDot_zero_left, vecDot_zero_right, matVecMul_zero, add_assoc] using
    magic_identity_responseJ_adjoint_sum_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p (matVecMul sigmaStar p)
      (matVecMul kappa p)

theorem magic_identity_responseJ_adjoint_diagonal_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p
        (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a +
        ResponseJ U p
          (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
            (adjointCoeffField a) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_adjoint_diagonal_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p

theorem magic_identity_responseJ_sigmaStar_sub_kappa_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStar - kappa) p) a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) := by
  simpa [sub_eq_add_neg, add_matVecMul, neg_matVecMul, matVecMul_neg,
    vecDot_zero_left, vecDot_zero_right, matVecMul_zero, add_assoc] using
    magic_identity_responseJ_shifted_square_of_isSigmaCoarse
      U a hS hK hSigma hdet p (matVecMul (sigmaStar - kappa) p)

theorem magic_identity_responseJ_sigmaStar_sub_kappa_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_responseJ_sigmaStar_sub_kappa_of_isSigmaCoarse
      U a hS hK hSigma hdet p

theorem magic_identity_responseJ_adjoint_sigmaStar_add_kappa_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) := by
  simpa [sub_eq_add_neg, add_matVecMul, neg_matVecMul, matVecMul_neg,
    vecDot_zero_left, vecDot_zero_right, matVecMul_zero, add_assoc] using
    magic_identity_responseJ_adjoint_shifted_square_of_isSigmaCoarse
      U a hSAdj hKAdj hSigmaAdj hdet p (matVecMul (sigmaStar + kappa) p)

theorem sigmaStar_le_sigma_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul sigmaStar p) ≤ vecDot p (matVecMul sigma p) := by
  have hdiag :=
    magic_identity_responseJ_adjoint_diagonal_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p
  have hResp :
      0 ≤ ResponseJ U p (matVecMul (sigmaStar - kappa) p) a :=
    responseJ_nonneg U p (matVecMul (sigmaStar - kappa) p) a
  have hAdj :
      0 ≤ ResponseJ U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a) :=
    responseJ_nonneg U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a)
  have hDef :
      vecDot p (matVecMul (sigma - sigmaStar) p) =
        vecDot p (matVecMul sigma p) - vecDot p (matVecMul sigmaStar p) := by
    simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_neg_right]
  linarith

theorem sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    sigmaStar_le_sigma_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p

theorem kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  have hResp :
      0 ≤ ResponseJ U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a) :=
    responseJ_nonneg U p (matVecMul (sigmaStar + kappa) p) (adjointCoeffField a)
  have hSpecial :=
    magic_identity_responseJ_adjoint_sigmaStar_add_kappa_of_isSigmaCoarse
      U a hSAdj hKAdj hSigmaAdj hdet p
  linarith

theorem neg_kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    -vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  have hResp :
      0 ≤ ResponseJ U p (matVecMul (sigmaStar - kappa) p) a :=
    responseJ_nonneg U p (matVecMul (sigmaStar - kappa) p) a
  have hSpecial :=
    magic_identity_responseJ_sigmaStar_sub_kappa_of_isSigmaCoarse
      U a hS hK hSigma hdet p
  linarith

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse
      U a hSAdj hKAdj hSigmaAdj hdet p

theorem neg_kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    -vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    neg_kappa_add_transpose_le_sigma_sub_sigmaStar_of_isSigmaCoarse
      U a hS hK hSigma hdet p

theorem basic_cg_identities_coarse_graining_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |volumeAverage U
        (fun x => vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) := by
  have hlin :=
    basic_cg_identities_linear_response_of_isResponseMaximizer
      U a hEll p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) hInt u hmax w
  have hJspecial :=
    magic_identity_responseJ_sigmaStar_sub_kappa_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p
  have hkappa :=
    kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse
      U a hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p
  have hbound :
      ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a ≤
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
    linarith
  have hsqrt :
      Real.sqrt (2 * ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a) ≤
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hmul :
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
          Real.sqrt
            (2 * ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a) ≤
        Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
          Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) := by
    exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  exact le_trans hlin hmul

theorem basic_cg_identities_coarse_graining_canonical_of_isSigmaCoarse_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |volumeAverage U
        (fun x => vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) :=
  basic_cg_identities_coarse_graining_canonical_of_isSigmaCoarse
    U a hEll hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u hmax w

theorem basic_cg_identities_coarse_graining_average_pairing_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |vecDot p
        (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a))
          (fun i => volumeAverage U (fun x => w.toH1.grad x i))) -
      vecDot p
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) := by
  let avgGrad : Vec d := fun i => volumeAverage U (fun x => w.toH1.grad x i)
  let avgFlux : Vec d := fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)
  have hcg :=
    basic_cg_identities_coarse_graining_canonical_of_isSigmaCoarse
      U a hEll hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p hInt u hmax w
  have hpair :=
    basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
      U a p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) hInt w
  have hStarSymm : (sigmaStarCoarse U a).IsSymm := by
    have hInvSymm : (sigmaStar⁻¹).IsSymm :=
      (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
    unfold sigmaStarCoarse
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
    exact isSymm_nonsingInv hInvSymm
  have hStarEq : matTranspose (sigmaStarCoarse U a) = sigmaStarCoarse U a := by
    simpa [matTranspose] using hStarSymm.eq
  have hgradEq :
      vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) avgGrad =
        vecDot p
          (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a)) avgGrad) := by
    unfold avgGrad aStarCoarse
    calc
      vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) avgGrad =
          vecDot p (matVecMul (matTranspose (sigmaStarCoarse U a - kappaCoarse U a)) avgGrad) := by
            rw [vecDot_matVecMul_transpose]
      _ = vecDot p
            (matVecMul (matTranspose (sigmaStarCoarse U a) - matTranspose (kappaCoarse U a)) avgGrad) := by
            simp [matTranspose, Matrix.transpose_sub]
      _ = vecDot p
            (matVecMul (sigmaStarCoarse U a - matTranspose (kappaCoarse U a)) avgGrad) := by
            rw [hStarEq]
      _ = vecDot p
            (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a)) avgGrad) := by
            rfl
  have hrewrite :
      volumeAverage U
          (fun x => vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
      vecDot p
          (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a)) avgGrad) -
        vecDot p avgFlux := by
    calc
      volumeAverage U
          (fun x => vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
          vecDot (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) avgGrad -
            vecDot p avgFlux := by
              simpa [avgGrad, avgFlux] using hpair
      _ = vecDot p
            (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a)) avgGrad) -
          vecDot p avgFlux := by
            rw [hgradEq]
  rw [hrewrite] at hcg
  simpa [avgGrad, avgFlux] using hcg

theorem
    basic_cg_identities_coarse_graining_average_pairing_canonical_of_isSigmaCoarse_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |vecDot p
        (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a))
          (fun i => volumeAverage U (fun x => w.toH1.grad x i))) -
      vecDot p
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) :=
  basic_cg_identities_coarse_graining_average_pairing_canonical_of_isSigmaCoarse
    U a hEll hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u hmax w

theorem basic_cg_identities_coarse_graining_average_difference_canonical_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) (hInt : ResponseLinearIntegrabilityData U a)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |vecDot p
        (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a))
          (fun i => volumeAverage U (fun x => w.toH1.grad x i)) -
          (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) := by
  simpa [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right] using
    basic_cg_identities_coarse_graining_average_pairing_canonical_of_isSigmaCoarse
      U a hEll hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p hInt u hmax w

theorem
    basic_cg_identities_coarse_graining_average_difference_canonical_of_isSigmaCoarse_of_isEllipticFieldOn
    {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d)
    (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p
      (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a u)
    (w : AHarmonicFunction a U) :
    |vecDot p
        (matVecMul (aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a))
          (fun i => volumeAverage U (fun x => w.toH1.grad x i)) -
          (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) :=
  basic_cg_identities_coarse_graining_average_difference_canonical_of_isSigmaCoarse
    U a hEll hS hK hSigma hSAdj hKAdj hSigmaAdj hdet p
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u hmax w


end

end Homogenization
