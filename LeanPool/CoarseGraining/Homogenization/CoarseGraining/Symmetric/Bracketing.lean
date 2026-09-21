/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarLeSigma
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.HarmonicMean
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.UpperLeftAverage
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.CoarseMatrices

/-! # Bracketing -/

namespace Homogenization

noncomputable section

/-!
# Dirichlet--Neumann bracketing for symmetric coefficient fields

This file records the symmetric specializations of the deterministic
harmonic-mean and arithmetic-mean bounds for the canonical coarse matrices.
-/

/-- For symmetric coefficient fields, the averaged inverse symmetric part is
the average of the pointwise inverse coefficient matrices. -/
theorem averagedSymmPartInv_eq_volumeAverageMat_inv_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a) :
    averagedSymmPartInv U a = volumeAverageMat U (fun x : Vec d => (a x)⁻¹) := by
  ext i j
  simp [averagedSymmPartInv, volumeAverageMat,
    symmPart_eq_self_of_isSymmetricCoeffField ha]

/-- For symmetric coefficient fields, the upper-left averaged correction is
just the arithmetic average of the coefficient field. -/
theorem averagedSymmPartPlusCorrection_eq_volumeAverageMat_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a) :
    averagedSymmPartPlusCorrection U a = volumeAverageMat U a := by
  ext i j
  simp [averagedSymmPartPlusCorrection, volumeAverageMat,
    symmPart_eq_self_of_isSymmetricCoeffField ha,
    skewPart_eq_zero_of_isSymmetricCoeffField ha]

/--
Symmetric harmonic-mean lower bound:
`(average_U a^{-1})^{-1} ≤ sigmaStarCoarse(U; a)`.
-/
theorem harmonicMeanCoeffField_le_sigmaStarCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MatLoewnerLE
      ((volumeAverageMat U (fun x : Vec d => (a x)⁻¹))⁻¹)
      (sigmaStarCoarse U a) := by
  have h :=
    harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat
  rw [averagedSymmPartInv_eq_volumeAverageMat_inv_of_isSymmetricCoeffField ha] at h
  exact h

/--
The middle Dirichlet--Neumann ordering `sigmaStarCoarse(U; a) ≤
sigmaCoarse(U; a)`, repackaged on the symmetric theorem surface.
-/
theorem sigmaStarCoarse_le_sigmaCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (_ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE (sigmaStarCoarse U a) (sigmaCoarse U a) := by
  intro p
  have hbase :
      vecDot p (matVecMul (sigmaStarCoarse U a) p) ≤
        vecDot p (matVecMul (sigmaCoarse U a) p) :=
    sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat hA hS hK hSigma p
  nlinarith

/--
Symmetric arithmetic-mean upper bound:
`sigmaCoarse(U; a) ≤ average_U a`.
-/
theorem sigmaCoarse_le_volumeAverageMat_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    MatLoewnerLE (sigmaCoarse U a) (volumeAverageMat U a) := by
  have h :=
    bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat hA hS hK hSigma
  rw [bCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA,
    averagedSymmPartPlusCorrection_eq_volumeAverageMat_of_isSymmetricCoeffField ha] at h
  exact h

end

end Homogenization
