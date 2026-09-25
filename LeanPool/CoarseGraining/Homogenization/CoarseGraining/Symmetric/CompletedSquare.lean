/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.Basics
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Response

/-! # Completed Square -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Completed squares for symmetric coefficient fields

This file specializes the nonsymmetric magic identities to the symmetric case,
where `kappa` vanishes and the completed square is centered at
`q = sigmaStar * p`.
-/

private theorem zero_matVecMul {d : ℕ} (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

theorem responseJ_completedSquare_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul sigmaStar p)) := by
  have hk : kappa = 0 :=
    kappa_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix_of_isKappaCoarse
      ha hA hS hK hdet
  calc
    ResponseJ U p q a =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar - kappa) p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar - kappa) p)) := by
      exact magic_identity_responseJ_shifted_square_of_isSigmaCoarse
        U a hS hK hSigma hdet p q
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
          (1 / 2 : ℝ) *
            vecDot (q - matVecMul sigmaStar p)
              (matVecMul sigmaStar⁻¹ (q - matVecMul sigmaStar p)) := by
      rw [hk]
      simp [matTranspose, zero_matVecMul, vecDot_zero_right]

theorem responseJ_sigmaStar_mul_eq_half_gap_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul sigmaStar p) a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) := by
  rw [responseJ_completedSquare_of_isSymmetricCoeffField
    ha hA hS hK hSigma hdet p (matVecMul sigmaStar p)]
  simp [vecDot_zero_left, matVecMul_zero]

theorem responseJ_sigmaStarCoarse_mul_eq_half_gap_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a) p) a =
      (1 / 2 : ℝ) *
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet]
  exact responseJ_sigmaStar_mul_eq_half_gap_of_isSymmetricCoeffField
    ha hA hS hK hSigma hdet p

end

end Homogenization
