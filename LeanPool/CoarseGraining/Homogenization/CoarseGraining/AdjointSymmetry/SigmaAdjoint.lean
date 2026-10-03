/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint

/-! # Sigma Adjoint -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Adjoint symmetry -- sigma / kappa / deterministic coarse block adjoint

sigmaStarCoarse / sigmaStarInvKappaCoarse / kappaCoarse / sigmaCoarse /
deterministicCoarseBlockMatrix / sigmaStarInvCoarse / sigmaStarInvKappaCoarse
equalities under adjointCoeffField, from isSigma / isKappa / isCoarseBlockMatrix
hypotheses and their witness-data variants.
-/

/-- Note-facing transpose compatibility for `\sigma_*(U; a)` from primal and
adjoint `\sigma_*` witness data. -/
theorem sigmaStarCoarse_adjointCoeffField_eq_of_isSigmaStarData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a :=
  sigmaStarCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
    (U := U) (a := a) hS hSAdj hdet

theorem sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa)) :
    sigmaStarInvKappaCoarse U (adjointCoeffField a) = -(sigmaStarInvKappaCoarse U a) := by
  rw [sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hKAdj,
    sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]
  simp

/-- Note-facing transpose compatibility for `\sigma_*^{-1}(U; a)\kappa(U; a)`
from primal and adjoint `\kappa` witness data. -/
theorem sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isKappaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa)) :
    sigmaStarInvKappaCoarse U (adjointCoeffField a) = -(sigmaStarInvKappaCoarse U a) :=
  sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
    (U := U) (a := a) hK hKAdj

theorem kappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) := by
  rw [eq_kappaCoarse_of_isKappaCoarse hSAdj hKAdj hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet]

/-- Note-facing transpose compatibility for `\kappa(U; a)` from primal and
adjoint `\sigma_*`/`\kappa` witness data. -/
theorem kappaCoarse_adjointCoeffField_eq_neg_of_isKappaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) :=
  kappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
    (U := U) (a := a) hS hK hSAdj hKAdj hdet

theorem sigmaCoarse_adjointCoeffField_eq_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hSAdj hKAdj hSigmaAdj hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet]

/-- Note-facing transpose compatibility for `\sigma(U; a)` from primal and
adjoint deterministic coarse-data witnesses. -/
theorem sigmaCoarse_adjointCoeffField_eq_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a :=
  sigmaCoarse_adjointCoeffField_eq_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    deterministicCoarseBlockMatrix U (adjointCoeffField a) =
      blockMatFlipFlux (deterministicCoarseBlockMatrix U a) := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  · ext i j
    simp [deterministicCoarseBlockMatrix, blockMatFlipFlux,
      sigmaCoarse_adjointCoeffField_eq_of_isSigmaCoarse
        (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet,
      kappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
        (U := U) (a := a) hS hK hSAdj hKAdj hdet,
      sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
        (U := U) (a := a) hS hSAdj,
      Matrix.transpose_neg, matTranspose, Matrix.mul_assoc]
  · ext i j
    simp [deterministicCoarseBlockMatrix, blockMatFlipFlux,
      kappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
        (U := U) (a := a) hS hK hSAdj hKAdj hdet,
      sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
        (U := U) (a := a) hS hSAdj,
      Matrix.transpose_neg, matTranspose, Matrix.mul_assoc]
  · ext i j
    simp [deterministicCoarseBlockMatrix, blockMatFlipFlux,
      sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isKappaCoarse
        (U := U) (a := a) hK hKAdj]
  · ext i j
    simp [deterministicCoarseBlockMatrix, blockMatFlipFlux,
      sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
        (U := U) (a := a) hS hSAdj]

/-- Note-facing transpose compatibility for the deterministic coarse block
matrix built from primal and adjoint scalar coarse-data witnesses. -/
theorem deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    deterministicCoarseBlockMatrix U (adjointCoeffField a) =
      blockMatFlipFlux (deterministicCoarseBlockMatrix U a) :=
  deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_eq_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (deterministicCoarseBlockMatrix U a).upperLeft := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperLeft
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
        (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet)

/-- Note-facing transpose compatibility for the upper-left block of the
deterministic coarse block matrix from primal and adjoint scalar coarse-data
witnesses. -/
theorem deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_eq_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (deterministicCoarseBlockMatrix U a).upperLeft :=
  deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_eq_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_eq_neg_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((deterministicCoarseBlockMatrix U a).upperRight) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperRight
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
        (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet)

/-- Note-facing transpose compatibility for the upper-right block of the
deterministic coarse block matrix from primal and adjoint scalar coarse-data
witnesses. -/
theorem deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_eq_neg_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((deterministicCoarseBlockMatrix U a).upperRight) :=
  deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_eq_neg_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_eq_neg_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((deterministicCoarseBlockMatrix U a).lowerLeft) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerLeft
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
        (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet)

/-- Note-facing transpose compatibility for the lower-left block of the
deterministic coarse block matrix from primal and adjoint scalar coarse-data
witnesses. -/
theorem deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_eq_neg_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((deterministicCoarseBlockMatrix U a).lowerLeft) :=
  deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_eq_neg_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_eq_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (deterministicCoarseBlockMatrix U a).lowerRight := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerRight
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isSigmaCoarse
        (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet)

/-- Note-facing transpose compatibility for the lower-right block of the
deterministic coarse block matrix from primal and adjoint scalar coarse-data
witnesses. -/
theorem deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_eq_of_isSigmaData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (deterministicCoarseBlockMatrix U a).lowerRight :=
  deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_eq_of_isSigmaCoarse
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    deterministicCoarseBlockMatrix U (adjointCoeffField a) =
      blockMatFlipFlux (deterministicCoarseBlockMatrix U a) := by
  calc
    deterministicCoarseBlockMatrix U (adjointCoeffField a) =
        coarseBlockMatrix U (adjointCoeffField a) := by
          symm
          exact coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hAadj
    _ = blockMatFlipFlux (coarseBlockMatrix U a) := by
      exact coarseBlockMatrix_adjointCoeffField_of_exists
        (U := U) (a := a) ⟨deterministicCoarseBlockMatrix U a, hA⟩
    _ = blockMatFlipFlux (deterministicCoarseBlockMatrix U a) := by
      rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]

/-- Note-facing transpose compatibility for the deterministic coarse block
matrix built from the canonical coarse data. -/
theorem deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    deterministicCoarseBlockMatrix U (adjointCoeffField a) =
      blockMatFlipFlux (deterministicCoarseBlockMatrix U a) :=
  deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

theorem deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (deterministicCoarseBlockMatrix U a).upperLeft := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperLeft
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj)

/-- Note-facing transpose compatibility for the upper-left block of the
deterministic coarse block matrix. -/
theorem deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_eq {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (deterministicCoarseBlockMatrix U a).upperLeft :=
  deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

theorem deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((deterministicCoarseBlockMatrix U a).upperRight) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperRight
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj)

/-- Note-facing transpose compatibility for the upper-right block of the
deterministic coarse block matrix. -/
theorem deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_eq_neg {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((deterministicCoarseBlockMatrix U a).upperRight) :=
  deterministicCoarseBlockMatrix_upperRight_adjointCoeffField_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

theorem deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((deterministicCoarseBlockMatrix U a).lowerLeft) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerLeft
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj)

/-- Note-facing transpose compatibility for the lower-left block of the
deterministic coarse block matrix. -/
theorem deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_eq_neg {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((deterministicCoarseBlockMatrix U a).lowerLeft) :=
  deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

theorem deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (deterministicCoarseBlockMatrix U a).lowerRight := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerRight
      (deterministicCoarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj)

/-- Note-facing transpose compatibility for the lower-right block of the
deterministic coarse block matrix. -/
theorem deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_eq {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    (deterministicCoarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (deterministicCoarseBlockMatrix U a).lowerRight :=
  deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

theorem sigmaStarInvCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    sigmaStarInvCoarse U (adjointCoeffField a) = sigmaStarInvCoarse U a := by
  simpa using
    deterministicCoarseBlockMatrix_lowerRight_adjointCoeffField_of_isCoarseBlockMatrix
      (U := U) (a := a) hA hAadj

/-- Note-facing transpose compatibility for `\sigma_*^{-1}(U; a)`. -/
theorem sigmaStarInvCoarse_adjointCoeffField_eq {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar) :
    sigmaStarInvCoarse U (adjointCoeffField a) = sigmaStarInvCoarse U a :=
  sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarData
    (U := U) (a := a) hS hSAdj

theorem sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    sigmaStarInvKappaCoarse U (adjointCoeffField a) = -(sigmaStarInvKappaCoarse U a) := by
  have hlower :
      -(sigmaStarInvKappaCoarse U (adjointCoeffField a)) =
        sigmaStarInvKappaCoarse U a := by
    simpa using
      deterministicCoarseBlockMatrix_lowerLeft_adjointCoeffField_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj
  have hneg := congrArg Neg.neg hlower
  simpa using hneg

/-- Note-facing transpose compatibility for `\sigma_*^{-1}(U; a)\kappa(U; a)`. -/
theorem sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    sigmaStarInvKappaCoarse U (adjointCoeffField a) = -(sigmaStarInvKappaCoarse U a) :=
  sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAadj

/-- If the coefficient field is self-adjoint, then the canonical
`\sigma_*^{-1}(U; a)\kappa(U; a)` vanishes once the deterministic coarse block
matrix is identified as coarse. -/
theorem sigmaStarInvKappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAdj : adjointCoeffField a = a) :
    sigmaStarInvKappaCoarse U a = 0 := by
  have hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a)) := by
    simpa [hAdj] using hA
  have hneg :
      sigmaStarInvKappaCoarse U a = -(sigmaStarInvKappaCoarse U a) := by
    simpa [hAdj] using
      sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj
  ext i j
  have hij : sigmaStarInvKappaCoarse U a i j = -(sigmaStarInvKappaCoarse U a i j) := by
    exact congrFun (congrFun hneg i) j
  simpa using (CharZero.eq_neg_self_iff.mp hij)

theorem sigmaStarCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a := by
  unfold sigmaStarCoarse
  simpa using
    congrArg Inv.inv
      (sigmaStarInvCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj)

/-- Note-facing transpose compatibility for `\sigma_*(U; a)`. -/
theorem sigmaStarCoarse_adjointCoeffField_eq {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a :=
  sigmaStarCoarse_adjointCoeffField_eq_of_isSigmaStarData
    (U := U) (a := a) hS hSAdj hdet

theorem kappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) := by
  unfold kappaCoarse
  rw [sigmaStarCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix (U := U) (a := a) hA hAadj,
    sigmaStarInvKappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
      (U := U) (a := a) hA hAadj]
  simp [mul_neg]

/-- Note-facing transpose compatibility for `\kappa(U; a)`. -/
theorem kappaCoarse_adjointCoeffField_eq_neg {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    kappaCoarse U (adjointCoeffField a) = -(kappaCoarse U a) :=
  kappaCoarse_adjointCoeffField_eq_neg_of_isKappaData
    (U := U) (a := a) hS hK hSAdj hKAdj hdet

/-- If the coefficient field is self-adjoint, then the canonical
`\kappa(U; a)` vanishes once the deterministic coarse block matrix is
identified as coarse. -/
theorem kappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAdj : adjointCoeffField a = a) :
    kappaCoarse U a = 0 := by
  unfold kappaCoarse
  simp [sigmaStarInvKappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
    (U := U) (a := a) hA hAdj]

theorem sigmaCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hAadj : IsCoarseBlockMatrix U (adjointCoeffField a)
      (deterministicCoarseBlockMatrix U (adjointCoeffField a))) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a := by
  have hupper :
      sigmaCoarse U (adjointCoeffField a) +
          (matTranspose (kappaCoarse U (adjointCoeffField a))) *
              sigmaStarInvCoarse U (adjointCoeffField a) *
              kappaCoarse U (adjointCoeffField a) =
        sigmaCoarse U a +
          (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a := by
    simpa using
      deterministicCoarseBlockMatrix_upperLeft_adjointCoeffField_of_isCoarseBlockMatrix
        (U := U) (a := a) hA hAadj
  rw [kappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix (U := U) (a := a) hA hAadj,
    sigmaStarInvCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix (U := U) (a := a) hA hAadj] at hupper
  simp [Matrix.transpose_neg, matTranspose, Matrix.mul_assoc] at hupper
  exact hupper

/-- Note-facing transpose compatibility for `\sigma(U; a)`. -/
theorem sigmaCoarse_adjointCoeffField_eq {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    sigmaCoarse U (adjointCoeffField a) = sigmaCoarse U a :=
  sigmaCoarse_adjointCoeffField_eq_of_isSigmaData
    (U := U) (a := a) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet


end

end Homogenization
