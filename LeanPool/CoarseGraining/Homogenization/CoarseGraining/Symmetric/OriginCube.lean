/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Bracketing
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.CompletedSquare

/-! # Origin Cube -/

namespace Homogenization

noncomputable section

/-!
# Symmetric formulas on triadic open cubes

This file repackages the symmetric coarse-graining identities on triadic open
cubes, using the translated origin-cube recovery data which supplies the
deterministic coarse data hypotheses.
-/

/--
If the coefficient field is symmetric, then the canonical coarse coupling
matrix `kappaCoarse` vanishes on any triadic open cube once translated
origin-cube elliptic recovery data is available.
-/
theorem kappaCoarse_eq_zero_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hRec :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (ha : IsSymmetricCoeffField a) :
    kappaCoarse (openCubeSet Q) a = 0 := by
  exact
    kappaCoarse_eq_zero_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData_of_adjointCoeffField_eq
      Q R hRec (adjointCoeffField_eq_self_of_isSymmetricCoeffField ha)

/--
On a triadic open cube with translated origin-cube recovery data, a symmetric
coefficient field splits the two response variables:
`ResponseJ p q = 1/2 p * sigmaCoarse * p
  + 1/2 q * sigmaStarInvCoarse * q - p·q`.
-/
theorem responseJ_eq_half_vecDot_sigmaCoarse_add_half_vecDot_sigmaStarInvCoarse_sub_dot_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hRec :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (ha : IsSymmetricCoeffField a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse (openCubeSet Q) a) p) +
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) -
        vecDot p q := by
  rcases
      openCubeDeterministicCoarseData_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
        Q R hRec with
    ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    responseJ_eq_half_vecDot_sigmaCoarse_add_half_vecDot_sigmaStarInvCoarse_sub_dot_of_isSymmetricCoeffField
      ha hA hS hK hSigma hdet p q

/--
At the canonical symmetric coupling `q = sigmaStarCoarse p`, the response is
one half of the gap between the two canonical coarse matrices.
-/
theorem responseJ_sigmaStarCoarse_mul_eq_half_gap_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hRec :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (ha : IsSymmetricCoeffField a) (p : Vec d) :
    ResponseJ (openCubeSet Q) p
        (matVecMul (sigmaStarCoarse (openCubeSet Q) a) p) a =
      (1 / 2 : ℝ) *
        vecDot p (matVecMul
          (sigmaCoarse (openCubeSet Q) a - sigmaStarCoarse (openCubeSet Q) a) p) := by
  rcases
      openCubeDeterministicCoarseData_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
        Q R hRec with
    ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    responseJ_sigmaStarCoarse_mul_eq_half_gap_of_isSymmetricCoeffField
      ha hA hS hK hSigma hdet p

/--
Centered origin-cube symmetric harmonic-mean lower bound:
`(average_Q a^{-1})^{-1} ≤ sigmaStarCoarse(Q; a)`.
-/
theorem harmonicMeanCoeffField_le_sigmaStarCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (ha : IsSymmetricCoeffField a) :
    MatLoewnerLE
      ((volumeAverageMat (openCubeSet (originCube d n))
        (fun x : Vec d => (a x)⁻¹))⁻¹)
      (sigmaStarCoarse (openCubeSet (originCube d n)) a) := by
  have h :=
    harmonicMeanSymmPart_le_sigmaStarCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      R hData
  rw [averagedSymmPartInv_eq_volumeAverageMat_inv_of_isSymmetricCoeffField ha] at h
  exact h

/--
Centered origin-cube symmetric middle ordering:
`sigmaStarCoarse(Q; a) ≤ sigmaCoarse(Q; a)`.
-/
theorem sigmaStarCoarse_le_sigmaCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (_ha : IsSymmetricCoeffField a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (sigmaStarCoarse (openCubeSet (originCube d n)) a)
      (sigmaCoarse (openCubeSet (originCube d n)) a) := by
  intro p
  have hbase :
      vecDot p (matVecMul
          (sigmaStarCoarse (openCubeSet (originCube d n)) a) p) ≤
        vecDot p (matVecMul
          (sigmaCoarse (openCubeSet (originCube d n)) a) p) :=
    sigmaStarCoarse_le_sigmaCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      R hData hA hS hK hSigma p
  nlinarith

/--
Centered origin-cube symmetric arithmetic-mean upper bound:
`sigmaCoarse(Q; a) ≤ average_Q a`.
-/
theorem sigmaCoarse_le_volumeAverageMat_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_isSymmetricCoeffField
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (ha : IsSymmetricCoeffField a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (sigmaCoarse (openCubeSet (originCube d n)) a)
      (volumeAverageMat (openCubeSet (originCube d n)) a) := by
  have h :=
    bCoarse_le_averagedSymmPartPlusCorrection_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      R hData hA hS hK hSigma
  rw [bCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA,
    averagedSymmPartPlusCorrection_eq_volumeAverageMat_of_isSymmetricCoeffField ha] at h
  exact h

end

end Homogenization
