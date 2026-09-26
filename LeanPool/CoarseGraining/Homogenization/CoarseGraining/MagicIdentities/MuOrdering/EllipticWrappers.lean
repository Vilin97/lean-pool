/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences

/-! # Elliptic Wrappers -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- elliptic no-`hdet` wrappers for core magic identities

This file packages the most-used `ResponseJ` and block-quadratic magic
identities, `Mu - p · q` formulas, and canonical ordering consequences under
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

theorem basic_cg_identities_responseJ_zero_formula_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p

theorem basic_cg_identities_responseJ_zero_formula_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) :=
  basic_cg_identities_responseJ_zero_formula_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSigma p

theorem basic_cg_identities_responseJ_formula_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) - vecDot p q +
        vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p q

theorem basic_cg_identities_responseJ_formula_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) - vecDot p q +
        vecDot q (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) :=
  basic_cg_identities_responseJ_formula_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSigma p q

theorem magic_identity_responseJ_completed_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      sigmaCorrectedResponse U a p - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_responseJ_completed_square_canonical_of_isSigmaCoarse
      U a hS hK hSigma hdet p q

theorem magic_identity_responseJ_completed_square_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      sigmaCorrectedResponse U a p - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p)) :=
  magic_identity_responseJ_completed_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSigma p q

theorem magic_identity_responseJ_completed_square_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_responseJ_completed_square_of_isSigmaCoarse
      U a hS hK hSigma hdet p q

theorem magic_identity_responseJ_completed_square_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
        (1 / 2 : ℝ) * vecDot (q + matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q + matVecMul kappa p)) :=
  magic_identity_responseJ_completed_square_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS hK hSigma p q

theorem basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) :=
  basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
      vecDot p q := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
      vecDot p q :=
  magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_block_quadratic_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_block_quadratic_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_block_quadratic_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (p, q)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) :=
  magic_identity_block_quadratic_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_sub_vecDot_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q :=
  magic_identity_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_mu_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_sub_vecDot_shifted_square_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q : Vec d) :
    Mu U (p, q) a - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) :=
  magic_identity_mu_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_responseJ_add_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q h : Vec d) :
    ResponseJ U p (q - h) a + (Mu U (p, q + h) a - vecDot p (q + h)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (sigmaStarCoarse U a) p)) +
        vecDot (h - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (h - matVecMul (kappaCoarse U a) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_responseJ_add_mu_sub_vecDot_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q h

theorem magic_identity_responseJ_add_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p q h : Vec d) :
    ResponseJ U p (q - h) a + (Mu U (p, q + h) a - vecDot p (q + h)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (sigmaStarCoarse U a) p)) +
        vecDot (h - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (h - matVecMul (kappaCoarse U a) p)) :=
  magic_identity_responseJ_add_mu_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q h

theorem magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a +
        (Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
          vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p

theorem magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a - kappaCoarse U a) p) a +
        (Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
          vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) =
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) :=
  magic_identity_responseJ_add_mu_sub_vecDot_diagonal_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p

theorem magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
        vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p

theorem magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (p : Vec d) :
    Mu U (p, matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) a -
        vecDot p (matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p) =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) :=
  magic_identity_mu_sub_vecDot_sigmaStar_add_kappa_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isEllipticFieldOn
      (U := U) (a := a) R hU hEll hvol compat hA hS hK hSigma hdet p

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    vecDot p (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) ≤
      vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) :=
  kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p

theorem kappa_add_transpose_le_sigma_sub_sigmaStar_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    kappa_add_transpose_le_sigma_sub_sigmaStar_of_isEllipticFieldOn
      (U := U) (a := a) R hU hEll hvol compat hA hS hK hSigma hdet p

theorem kappa_add_transpose_le_sigma_sub_sigmaStar_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    vecDot p (matVecMul (kappa + matTranspose kappa) p) ≤
      vecDot p (matVecMul (sigma - sigmaStar) p) :=
  kappa_add_transpose_le_sigma_sub_sigmaStar_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p

theorem sigmaStar_le_sigma_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    vecDot p (matVecMul sigmaStar p) ≤ vecDot p (matVecMul sigma p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    sigmaStar_le_sigma_of_isEllipticFieldOn
      (U := U) (a := a) R hU hEll hvol compat hA hS hK hSigma hdet p

theorem sigmaStar_le_sigma_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    vecDot p (matVecMul sigmaStar p) ≤ vecDot p (matVecMul sigma p) :=
  sigmaStar_le_sigma_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q :=
  magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) :=
  magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q :=
  magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

theorem
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    hdet_of_recovery_hodge (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_canonical_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

theorem
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) :=
  magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_canonical_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hA hS hK hSigma p q

end

end Homogenization
