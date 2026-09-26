/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.BCoarseCanonical

/-! # Origin Cube -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- origin-cube specializations

Origin-cube `openCubeSet` and `cubeSet` specializations of the
`sigmaStarCoarse_le_sigmaCoarse`, `sigmaCoarse_le_bCoarse`, and
`kappaCoarse_add_transpose ≤ sigmaCoarse - sigmaStarCoarse` orderings.
-/

theorem sigmaStarCoarse_le_sigmaCoarse_openCubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_openCubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse (openCubeSet (originCube d n)) a) p) ≤
      vecDot p (matVecMul (sigmaCoarse (openCubeSet (originCube d n)) a) p) := by
  have hvol : 0 < (MeasureTheory.volume (openCubeSet (originCube d n))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d n)
  have hdet : IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isSobolevRegularDomain
      hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (U := openCubeSet (originCube d n))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d n)))
      hvol compat hS
  have hMuGe :
      ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
    intro P
    exact
      PotentialSolenoidalL2RecoveryData.mu_ge_vecDot_openCubeSet_originCubeOfIsEllipticFieldOn
        (R := R) hEll compat P
  exact sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := openCubeSet (originCube d n)) (a := a) hA hS hK hSigma hdet hMuGe p

theorem sigmaStarCoarse_le_sigmaCoarse_cubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (cubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_cubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (cubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (cubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse (cubeSet (originCube d n)) a) p) ≤
      vecDot p (matVecMul (sigmaCoarse (cubeSet (originCube d n)) a) p) := by
  have hdet : IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := cubeSet (originCube d n)) (a := a) R
      (isSobolevRegularDomain_cubeSet_originCube_recovery (d := d) n)
      hEll
      (hodgeConverseCriterion_cubeSet_originCube (d := d) (n := n))
      (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n)
      compat hS
  have hMuGe :
      ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu (cubeSet (originCube d n)) P a := by
    intro P
    exact
      PotentialSolenoidalL2RecoveryData.mu_ge_vecDot_cubeSet_originCubeOfIsEllipticFieldOn
        (R := R) hEll compat P
  exact sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
    (U := cubeSet (originCube d n)) (a := a) hA hS hK hSigma hdet hMuGe p

theorem sigmaCoarse_le_bCoarse_openCubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_openCubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (sigmaCoarse (openCubeSet (originCube d n)) a)
      (bCoarse
        (sigmaCoarse (openCubeSet (originCube d n)) a)
        (sigmaStarCoarse (openCubeSet (originCube d n)) a)
        (kappaCoarse (openCubeSet (originCube d n)) a)) := by
  exact
    sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (by
        rw [volume_openCubeSet_toReal]
        exact cubeVolume_pos (originCube d n))
      compat hS hK hSigma

theorem sigmaCoarse_le_bCoarse_cubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (cubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_cubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (sigmaCoarse (cubeSet (originCube d n)) a)
      (bCoarse
        (sigmaCoarse (cubeSet (originCube d n)) a)
        (sigmaStarCoarse (cubeSet (originCube d n)) a)
        (kappaCoarse (cubeSet (originCube d n)) a)) := by
  exact
    sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := cubeSet (originCube d n)) (a := a) R
      (isSobolevRegularDomain_cubeSet_originCube_recovery (d := d) n)
      hEll
      (hodgeConverseCriterion_cubeSet_originCube (d := d) (n := n))
      (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n)
      compat hS hK hSigma

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_openCubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_openCubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p
        (matVecMul
          (kappaCoarse (openCubeSet (originCube d n)) a +
            matTranspose (kappaCoarse (openCubeSet (originCube d n)) a)) p) ≤
      vecDot p
        (matVecMul
          (sigmaCoarse (openCubeSet (originCube d n)) a -
            sigmaStarCoarse (openCubeSet (originCube d n)) a) p) := by
  have hvol : 0 < (MeasureTheory.volume (openCubeSet (originCube d n))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d n)
  have hdet : IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isSobolevRegularDomain
      hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (U := openCubeSet (originCube d n))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d n)))
      hvol compat hS
  have hMuGe :
      ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
    intro P
    exact
      PotentialSolenoidalL2RecoveryData.mu_ge_vecDot_openCubeSet_originCubeOfIsEllipticFieldOn
        (R := R) hEll compat P
  exact
    kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
      (U := openCubeSet (originCube d n)) (a := a) hA hS hK hSigma hdet hMuGe p

theorem kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_cubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ} (a : CoeffField d) {lam Lam : ℝ}
    (R : PotentialSolenoidalL2RecoveryData (cubeSet (originCube d n)))
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll (by
          rw [volume_cubeSet_toReal]
          exact cubeVolume_pos (originCube d n)))
    )
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (cubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (cubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (cubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (cubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (cubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p
        (matVecMul
          (kappaCoarse (cubeSet (originCube d n)) a +
            matTranspose (kappaCoarse (cubeSet (originCube d n)) a)) p) ≤
      vecDot p
        (matVecMul
          (sigmaCoarse (cubeSet (originCube d n)) a -
            sigmaStarCoarse (cubeSet (originCube d n)) a) p) := by
  have hdet : IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := cubeSet (originCube d n)) (a := a) R
      (isSobolevRegularDomain_cubeSet_originCube_recovery (d := d) n)
      hEll
      (hodgeConverseCriterion_cubeSet_originCube (d := d) (n := n))
      (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n)
      compat hS
  have hMuGe :
      ∀ P : BlockVec d, vecDot P.1 P.2 ≤ Mu (cubeSet (originCube d n)) P a := by
    intro P
    exact
      PotentialSolenoidalL2RecoveryData.mu_ge_vecDot_cubeSet_originCubeOfIsEllipticFieldOn
        (R := R) hEll compat P
  exact
    kappaCoarse_add_transpose_le_sigmaCoarse_sub_sigmaStarCoarse_of_isSigmaCoarse_of_mu_ge_vecDot
      (U := cubeSet (originCube d n)) (a := a) hA hS hK hSigma hdet hMuGe p

end

end Homogenization
