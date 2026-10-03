/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarInvAveraged

/-! # BCoarse Canonical -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- bCoarse canonical positive-definiteness and `IsUnit`

The three `bCoarse_canonical_posDef_of_…` wrappers (Sobolev-regular,
`HodgeConverseCriterion`, `IsOpenBoundedConvexDomain`) and the matching
`isUnit_det_bCoarse_canonical_…` wrappers obtained from the positive-definite
plus determinant correspondence.
-/

theorem bCoarse_canonical_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).PosDef := by
  have hSigmaPos :
      (sigmaCoarse U a).PosDef :=
    sigmaCoarse_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := U) (a := a) hU hEll hvol hA hS hK hSigma hdet
  have hCorrPos :
      ((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a).PosSemidef :=
    kappaTranspose_sigmaStarInvCoarse_kappa_posSemidef (U := U) (a := a) hS
  simpa [bCoarse, sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet] using
    hSigmaPos.add_posSemidef hCorrPos

theorem bCoarse_canonical_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).PosDef := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    bCoarse_canonical_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := U) (a := a) hU hEll hvol.ne' hA hS hK hSigma hdet

theorem bCoarse_canonical_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).PosDef := by
  exact
    bCoarse_canonical_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma

theorem isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    IsUnit
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).det := by
  exact
    (Matrix.isUnit_iff_isUnit_det
      (A := bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))).mp
      ((bCoarse_canonical_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := U) (a := a) hU hEll hvol hA hS hK hSigma hdet).isUnit)

theorem isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    IsUnit
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).det := by
  exact
    (Matrix.isUnit_iff_isUnit_det
      (A := bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))).mp
      ((bCoarse_canonical_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
        (U := U) (a := a) R hU hEll hHodge hvol compat hA hS hK hSigma).isUnit)

theorem isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    IsUnit
      (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).det := by
  exact
    isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma

end

end Homogenization
