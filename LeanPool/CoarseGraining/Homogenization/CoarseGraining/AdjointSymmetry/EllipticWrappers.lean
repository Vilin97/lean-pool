/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences

/-! # Elliptic Wrappers -/

namespace Homogenization

noncomputable section

/-!
# Adjoint symmetry -- elliptic no-`hdet` wrappers

This file packages the witness-data adjoint-symmetry theorems under
recovery-plus-ellipticity hypotheses, so downstream users do not need to
thread `IsUnit sigmaStar.det` by hand.
-/

private theorem hdet_of_recovery_hodge
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) :
    IsUnit sigmaStar.det :=
  isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hU hEll hHodge hvol compat hS

theorem sigmaStarCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact sigmaStarCoarse_adjointCoeffField_eq_of_isSigmaStarData
    (U := U) (a := a) hS hSAdj hdet

theorem sigmaStarCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a :=
  sigmaStarCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hSAdj

theorem kappaCoarse_adjointCoeffField_eq_neg_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa)) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact kappaCoarse_adjointCoeffField_eq_neg_of_isKappaData
    (U := U) (a := a) hS hK hSAdj hKAdj hdet

theorem kappaCoarse_adjointCoeffField_eq_neg_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa)) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) :=
  kappaCoarse_adjointCoeffField_eq_neg_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSAdj hKAdj

theorem sigmaCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa)) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact sigmaCoarse_adjointCoeffField_eq_of_isSigmaData
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem sigmaCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa)) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a :=
  sigmaCoarse_adjointCoeffField_eq_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSigma hSAdj hKAdj hSigmaAdj

end

end Homogenization
