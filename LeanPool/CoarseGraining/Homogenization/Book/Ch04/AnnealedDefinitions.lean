/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Basic

/-! # Annealed Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Annealed coarse definitions

This file owns the Chapter 4 definitions of annealed coarse matrices and
response observables.  Scalarization witnesses and route data live in
`Homogenization.Book.Ch04.Internal.ScalarizationWitnesses`.
-/

open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The annealed doubled coarse-grained matrix `\overline{\mathbf A}(U)`,
obtained by averaging each deterministic coarse matrix entry. -/
noncomputable def annealedBlockMatrix {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : BlockMat d :=
  { upperLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P
    upperRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P
    lowerLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P
    lowerRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P }

/-- The annealed starred block matrix
`\overline{\mathbf A}_{*,n}^{-1}`. -/
noncomputable def annealedStarredBlockMatrixInv {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) : BlockMat d :=
  blockReflect (annealedBlockMatrix P U)

/-- The annealed inverse-star matrix `\overline\sigma_*^{-1}(U)`. -/
noncomputable def annealedSigmaStarInv {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).lowerRight

/-- The annealed starred matrix `\overline\sigma_*(U)`. -/
noncomputable def annealedSigmaStar {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedSigmaStarInv P U)⁻¹

/-- The annealed mixed block
`E[\sigma_*^{-1}(U; a)\kappa(U; a)]`. -/
noncomputable def annealedSigmaStarInvKappaMean {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) : Mat d :=
  -((annealedBlockMatrix P U).lowerLeft)

/-- The annealed coupling matrix `\overline\kappa(U)`. -/
noncomputable def annealedKappa {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedSigmaStar P U * annealedSigmaStarInvKappaMean P U

/-- The annealed upper-left block `\overline b(U)`. -/
noncomputable def annealedB {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).upperLeft

/-- The annealed conductivity matrix
`\overline\sigma = \overline b - \overline\kappa^t
\overline\sigma_*^{-1}\overline\kappa`. -/
noncomputable def annealedSigma {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedB P U
    - matTranspose (annealedKappa P U) * annealedSigmaStarInv P U * annealedKappa P U

@[simp] theorem annealedBlockMatrix_upperLeft_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    (annealedBlockMatrix P U).upperLeft i j =
      ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P :=
  rfl

@[simp] theorem annealedBlockMatrix_upperRight_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    (annealedBlockMatrix P U).upperRight i j =
      ∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P :=
  rfl

@[simp] theorem annealedBlockMatrix_lowerLeft_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    (annealedBlockMatrix P U).lowerLeft i j =
      ∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P :=
  rfl

@[simp] theorem annealedBlockMatrix_lowerRight_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    (annealedBlockMatrix P U).lowerRight i j =
      ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P :=
  rfl

@[simp] theorem annealedSigmaStarInv_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    annealedSigmaStarInv P U i j =
      ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P :=
  rfl

@[simp] theorem annealedSigmaStarInvKappaMean_apply {d : ℕ}
    (P : RestrictionCoeffLaw d) (U : Set (Vec d)) (i j : Fin d) :
    annealedSigmaStarInvKappaMean P U i j =
      -(∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P) := by
  simp [annealedSigmaStarInvKappaMean]

@[simp] theorem annealedB_apply {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) (i j : Fin d) :
    annealedB P U i j =
      ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P :=
  rfl

/-- Annealed block matrix on the origin cube at scale `n`. -/
noncomputable def annealedBlockMatrixAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : BlockMat d :=
  annealedBlockMatrix P (cubeSet (originCube d n))

/-- Annealed starred block matrix on the origin cube at scale `n`. -/
noncomputable def annealedStarredBlockMatrixInvAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : BlockMat d :=
  annealedStarredBlockMatrixInv P (cubeSet (originCube d n))

/-- Annealed inverse-star matrix on the origin cube at scale `n`. -/
noncomputable def annealedSigmaStarInvAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigmaStarInv P (cubeSet (originCube d n))

/-- Annealed starred matrix on the origin cube at scale `n`. -/
noncomputable def annealedSigmaStarAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigmaStar P (cubeSet (originCube d n))

/-- Annealed mixed block on the origin cube at scale `n`. -/
noncomputable def annealedSigmaStarInvKappaMeanAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigmaStarInvKappaMean P (cubeSet (originCube d n))

/-- Annealed coupling matrix on the origin cube at scale `n`. -/
noncomputable def annealedKappaAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedKappa P (cubeSet (originCube d n))

/-- Annealed upper-left block on the origin cube at scale `n`. -/
noncomputable def annealedBAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedB P (cubeSet (originCube d n))

/-- Annealed conductivity matrix on the origin cube at scale `n`. -/
noncomputable def annealedSigmaAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigma P (cubeSet (originCube d n))

/-- Response functional on the origin cube at scale `n`. -/
noncomputable def responseJAtScale {d : ℕ}
    (n : ℤ) (p q : Vec d) (a : CoeffField d) : ℝ :=
  ResponseJ (cubeSet (originCube d n)) p q a

/-- Response functional on an arbitrary triadic cube. -/
noncomputable def responseJOnCube {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) : ℝ :=
  ResponseJ (cubeSet Q) p q a

/-- Annealed response functional on the origin cube at scale `n`. -/
noncomputable def annealedResponseJAtScale {d : ℕ}
    (P : RestrictionCoeffLaw d) (n : ℤ) (p q : Vec d) : ℝ :=
  ∫ a, responseJAtScale n p q a.toFun ∂P

/-- Full unfolded coarse block observable on a deterministic triadic cube. -/
noncomputable def coarseFullBlockMatrixAtCube {d : ℕ}
    (Q : TriadicCube d) : RegCoeffField d → FullBlockMat d :=
  fun a => coarseFullBlockMatrixObservable (cubeSet Q) a.toFun

end

end Ch04
end Book
end Homogenization
