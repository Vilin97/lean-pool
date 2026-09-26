/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Basic

/-! # Coarse Matrices -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Symmetric coefficient fields and coarse matrices

This file specializes the deterministic coarse-matrix API to pointwise
symmetric coefficient fields. The main structural consequence is that the
canonical coupling matrix `kappaCoarse` vanishes.
-/

@[simp] theorem bCoarse_zero_right {d : ℕ} (sigma sigmaStar : Mat d) :
    bCoarse sigma sigmaStar (0 : Mat d) = sigma := by
  simp [bCoarse]

@[simp] theorem aCoarse_zero_right {d : ℕ} (sigma : Mat d) :
    aCoarse sigma (0 : Mat d) = sigma := by
  simp [aCoarse, matTranspose]

@[simp] theorem aStarCoarse_zero_right {d : ℕ} (sigmaStar : Mat d) :
    aStarCoarse sigmaStar (0 : Mat d) = sigmaStar := by
  simp [aStarCoarse, matTranspose]

theorem sigmaStarInvKappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    sigmaStarInvKappaCoarse U a = 0 :=
  sigmaStarInvKappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
    (U := U) (a := a) hA
    (adjointCoeffField_eq_self_of_isSymmetricCoeffField ha)

theorem kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    kappaCoarse U a = 0 :=
  kappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
    (U := U) (a := a) hA
    (adjointCoeffField_eq_self_of_isSymmetricCoeffField ha)

theorem coarseBlockMatrix_lowerLeft_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).lowerLeft = 0 := by
  rw [coarseBlockMatrix_lowerLeft_eq_of_isCoarseBlockMatrix hA,
    sigmaStarInvKappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp

theorem coarseBlockMatrix_upperRight_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).upperRight = 0 := by
  rw [coarseBlockMatrix_upperRight_eq_of_isCoarseBlockMatrix hA,
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp [matTranspose]

theorem coarseBlockMatrix_upperLeft_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).upperLeft = sigmaCoarse U a := by
  rw [coarseBlockMatrix_upperLeft_eq_of_isCoarseBlockMatrix hA,
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp

theorem coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (_ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a :=
  coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA

theorem bCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a) =
      sigmaCoarse U a := by
  rw [kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp

theorem aCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    aCoarse (sigmaCoarse U a) (kappaCoarse U a) = sigmaCoarse U a := by
  rw [kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp

theorem aStarCoarse_canonical_eq_sigmaStarCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    aStarCoarse (sigmaStarCoarse U a) (kappaCoarse U a) = sigmaStarCoarse U a := by
  rw [kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA]
  simp

end

end Homogenization
