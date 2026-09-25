/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarPosDef

/-! # Sigma Star Le Sigma -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- sigmaStarCoarse ≤ sigmaCoarse bridges

The three elliptic-bridge wrappers establishing `sigmaStarCoarse U a ≤
sigmaCoarse U a` from `IsEllipticFieldOn` plus a domain regularity hypothesis
(`HodgeConverseCriterion`, `IsOpenBoundedConvexDomain`, or
`IsSobolevRegularDomain`).
-/

theorem sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact
      IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := U) (P := P) (a := a) hU hEll hvol.ne'
  exact sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

theorem sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
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
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  exact
    sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma p

theorem sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a) p) := by
  have hMuGe : ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu U P a := by
    intro P
    exact
      IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := U) (P := P) (a := a) hU hEll hvol
  exact sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := U) (a := a) hA hS hK hSigma hdet hMuGe p

end

end Homogenization
