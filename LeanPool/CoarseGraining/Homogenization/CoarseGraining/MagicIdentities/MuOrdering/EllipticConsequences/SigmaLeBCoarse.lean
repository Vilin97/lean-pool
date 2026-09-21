/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaCoarsePosDef

/-! # Sigma Le BCoarse -/

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- sigma ≤ bCoarse and Loewner orderings

`kappaTranspose_sigmaStarInvCoarse_kappa_posSemidef`, the abstract
`sigma_le_bCoarse_of_isSigmaStarCoarse` Loewner ordering, and the canonical
`sigmaCoarse ≤ bCoarse` bridges via `IsSigmaCoarse`, `IsEllipticFieldOn` plus
`HodgeConverseCriterion`, and `IsOpenBoundedConvexDomain`.
-/

theorem kappaTranspose_sigmaStarInvCoarse_kappa_posSemidef {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) :
    ((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a).PosSemidef := by
  have hSigmaStarInv :
      (sigmaStarInvCoarse U a).PosSemidef :=
    sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse_local (U := U) (a := a) hS
  simpa [matTranspose] using
    hSigmaStarInv.conjTranspose_mul_mul_same (kappaCoarse U a)

theorem sigma_le_bCoarse_of_isSigmaStarCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) :
    MatLoewnerLE sigma (bCoarse sigma sigmaStar kappa) := by
  have hSigmaStarInv :
      sigmaStar⁻¹.PosSemidef := by
    simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using
      sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse_local (U := U) (a := a) hS
  have hCorr :
      ((matTranspose kappa) * sigmaStar⁻¹ * kappa).PosSemidef := by
    simpa [matTranspose] using hSigmaStarInv.conjTranspose_mul_mul_same kappa
  intro p
  have hCorrNonneg :
      0 ≤ vecDot p (matVecMul (((matTranspose kappa) * sigmaStar⁻¹ * kappa)) p) := by
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hCorr.dotProduct_mulVec_nonneg p
  have hExpand :
      (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (((matTranspose kappa) * sigmaStar⁻¹ * kappa)) p) := by
    calc
      (1 / 2 : ℝ) * vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p)
          =
        (1 / 2 : ℝ) *
          (vecDot p (matVecMul sigma p) +
            vecDot p (matVecMul (((matTranspose kappa) * sigmaStar⁻¹ * kappa)) p)) := by
              simp [bCoarse, add_matVecMul, vecDot_add_right]
      _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (((matTranspose kappa) * sigmaStar⁻¹ * kappa)) p) := by
              ring
  rw [hExpand]
  nlinarith

theorem sigmaCoarse_le_bCoarse_of_isSigmaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    MatLoewnerLE (sigmaCoarse U a)
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using
    sigma_le_bCoarse_of_isSigmaStarCoarse
      (U := U) (a := a) (sigma := sigma) (sigmaStar := sigmaStar) (kappa := kappa) hS

theorem sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE (sigmaCoarse U a)
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact sigmaCoarse_le_bCoarse_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hdet

theorem sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE (sigmaCoarse U a)
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) := by
  exact
    sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hS hK hSigma

end

end Homogenization
