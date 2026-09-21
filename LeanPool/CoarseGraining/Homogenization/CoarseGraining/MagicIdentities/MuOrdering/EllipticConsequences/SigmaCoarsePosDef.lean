/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarLeSigma

/-! # Sigma Coarse Pos Def -/

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- sigmaCoarse positive-definiteness bridges

The three elliptic-bridge wrappers establishing `(sigmaCoarse U a).PosDef` from
`IsEllipticFieldOn` plus a domain regularity hypothesis
(`IsSobolevRegularDomain`, `HodgeConverseCriterion`, or
`IsOpenBoundedConvexDomain`).
-/

theorem sigmaCoarse_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
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
    (sigmaCoarse U a).PosDef := by
  have hSigmaStarPos :
      (sigmaStarCoarse U a).PosDef :=
    sigmaStarCoarse_posDef_of_isSigmaStarCoarse (U := U) (a := a) hS hdet
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (sigmaCoarse_isSymm_of_isSigmaCoarse (U := U) (a := a) hS hK hSigma hdet)
  · intro p hp
    have hStarPos :
        0 < vecDot p (matVecMul (sigmaStarCoarse U a) p) := by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
        hSigmaStarPos.dotProduct_mulVec_pos hp
    have hle :=
      sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := U) (a := a) hU hEll hvol hA hS hK hSigma hdet p
    have hle' :
        vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
          vecDot p (matVecMul (sigmaCoarse U a) p) := hle
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using lt_of_lt_of_le hStarPos hle'

theorem sigmaCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
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
    (sigmaCoarse U a).PosDef := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    sigmaCoarse_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := U) (a := a) hU hEll hvol.ne' hA hS hK hSigma hdet

theorem sigmaCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
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
    (sigmaCoarse U a).PosDef := by
  exact
    sigmaCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma

end

end Homogenization
