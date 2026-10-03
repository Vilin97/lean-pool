/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.CoarseMatrices

/-! # Response -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Symmetric response identities

This file records the response-level consequences of the vanishing coupling
matrix in the symmetric case.
-/

private theorem zero_matVecMul {d : ℕ} (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

theorem kappa_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix_of_isKappaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    kappa = 0 := by
  have hkCoarse : kappaCoarse U a = 0 :=
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  have hkEq : kappaCoarse U a = kappa :=
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet
  rw [← hkEq]
  exact hkCoarse

theorem responseJ_eq_add_p_zero_zero_q_sub_dot_of_isKappaCoarse_of_kappa_eq_zero
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hk : kappa = 0) (p q : Vec d) :
    ResponseJ U p q a =
      ResponseJ U p 0 a + ResponseJ U 0 q a - vecDot p q := by
  have h := hK p q
  rw [hk] at h
  simp [zero_matVecMul, matVecMul_zero, vecDot_zero_right] at h
  linarith

theorem responseJ_eq_add_p_zero_zero_q_sub_dot_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      ResponseJ U p 0 a + ResponseJ U 0 q a - vecDot p q :=
  responseJ_eq_add_p_zero_zero_q_sub_dot_of_isKappaCoarse_of_kappa_eq_zero hK
    (kappa_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix_of_isKappaCoarse
      ha hA hS hK hdet)
    p q

theorem responseJ_p_zero_eq_half_vecDot_sigma_of_isSigmaCoarse_of_kappa_eq_zero
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hk : kappa = 0) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) := by
  have h := hSigma.2 p
  rw [hk] at h
  simp [matTranspose, zero_matVecMul, matVecMul_zero, vecDot_zero_right] at h
  linarith

theorem responseJ_p_zero_eq_half_vecDot_sigma_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) :=
  responseJ_p_zero_eq_half_vecDot_sigma_of_isSigmaCoarse_of_kappa_eq_zero hSigma
    (kappa_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix_of_isKappaCoarse
      ha hA hS hK hdet)
    p

theorem responseJ_p_zero_eq_half_vecDot_sigmaCoarse_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet]
  exact responseJ_p_zero_eq_half_vecDot_sigma_of_isSymmetricCoeffField
    ha hA hS hK hSigma hdet p

theorem responseJ_zero_q_eq_half_vecDot_sigmaStar_inv_of_isSigmaStarCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (q : Vec d) :
    ResponseJ U 0 q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) :=
  hS.2 q

theorem responseJ_zero_q_eq_half_vecDot_sigmaStarInvCoarse_of_isSigmaStarCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (q : Vec d) :
    ResponseJ U 0 q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
  rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  exact hS.2 q

theorem responseJ_eq_half_vecDot_sigma_add_half_vecDot_sigmaStar_inv_sub_dot_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
        vecDot p q := by
  calc
    ResponseJ U p q a =
        ResponseJ U p 0 a + ResponseJ U 0 q a - vecDot p q :=
      responseJ_eq_add_p_zero_zero_q_sub_dot_of_isSymmetricCoeffField
        ha hA hS hK hdet p q
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot q (matVecMul sigmaStar⁻¹ q) -
          vecDot p q := by
      rw [responseJ_p_zero_eq_half_vecDot_sigma_of_isSymmetricCoeffField
        ha hA hS hK hSigma hdet p, hS.2 q]

theorem responseJ_eq_half_vecDot_sigmaCoarse_add_half_vecDot_sigmaStarInvCoarse_sub_dot_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) -
        vecDot p q := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  exact
    responseJ_eq_half_vecDot_sigma_add_half_vecDot_sigmaStar_inv_sub_dot_of_isSymmetricCoeffField
      ha hA hS hK hSigma hdet p q

end

end Homogenization
