/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions

/-! # Block Matrix Properties -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
Phase-1 structural bookkeeping for the canonical coarse block matrices.

This file implements the first deterministic slice from
internal planning notes.
It focuses on the algebraic bookkeeping around the Chapter-2 note label
`l.block.coarse.matrices.basic.definitions`:

- expose the blocks of `coarseBlockMatrix U a`;
- record the reflection identity defining `coarseStarredBlockMatrixInv U a`;
- package the canonical deterministic block candidates built from
  `sigmaStarInvCoarse`, `sigmaStarInvKappaCoarse`, `kappaCoarse`, and
  `sigmaCoarse`;
- relate those canonical candidates to arbitrary deterministic witness data
  once the defining hypotheses are available.

This file deliberately avoids the heavier variational proofs reserved for later
deterministic modules.
-/

/-- Phase-1 bookkeeping for the upper-left block of the canonical coarse
matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperLeft_apply {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) :
    (coarseBlockMatrix U a).upperLeft i j =
      if i = j then
        2 * Mu U (Pi.single i 1, 0) a
      else
        Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a
          - Mu U (Pi.single i 1, 0) a
          - Mu U (Pi.single j 1, 0) a := by
  by_cases h : i = j
  · subst j
    show
      (if (Sum.inl i : BlockCoord d) = Sum.inl i then
          2 * Mu U (blockBasis (Sum.inl i)) a
        else
          Mu U (blockBasis (Sum.inl i) + blockBasis (Sum.inl i)) a
            - Mu U (blockBasis (Sum.inl i)) a
            - Mu U (blockBasis (Sum.inl i)) a) =
        if i = i then
          2 * Mu U (Pi.single i 1, 0) a
        else
          Mu U ((Pi.single i 1, 0) + (Pi.single i 1, 0)) a
            - Mu U (Pi.single i 1, 0) a
            - Mu U (Pi.single i 1, 0) a
    simp [blockBasis]
  · have hsum : (Sum.inl i : BlockCoord d) ≠ Sum.inl j := by
      simpa using h
    show
      (if (Sum.inl i : BlockCoord d) = Sum.inl j then
          2 * Mu U (blockBasis (Sum.inl i)) a
        else
          Mu U (blockBasis (Sum.inl i) + blockBasis (Sum.inl j)) a
            - Mu U (blockBasis (Sum.inl i)) a
            - Mu U (blockBasis (Sum.inl j)) a) =
        if i = j then
          2 * Mu U (Pi.single i 1, 0) a
        else
          Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a
            - Mu U (Pi.single i 1, 0) a
            - Mu U (Pi.single j 1, 0) a
    simp [blockBasis, h, hsum]

/-- Phase-1 bookkeeping for the upper-right block of the canonical coarse
matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperRight_apply {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) :
    (coarseBlockMatrix U a).upperRight i j =
      Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a
        - Mu U (Pi.single i 1, 0) a
        - Mu U (0, Pi.single j 1) a := by
  rfl

/-- Phase-1 bookkeeping for the lower-left block of the canonical coarse
matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerLeft_apply {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) :
    (coarseBlockMatrix U a).lowerLeft i j =
      Mu U ((0, Pi.single i 1) + (Pi.single j 1, 0)) a
        - Mu U (0, Pi.single i 1) a
        - Mu U (Pi.single j 1, 0) a := by
  rfl

/-- Phase-1 bookkeeping for the lower-right block of the canonical coarse
matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerRight_apply {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i j : Fin d) :
    (coarseBlockMatrix U a).lowerRight i j =
      if i = j then
        2 * Mu U (0, Pi.single i 1) a
      else
        Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a
          - Mu U (0, Pi.single i 1) a
          - Mu U (0, Pi.single j 1) a := by
  by_cases h : i = j
  · subst j
    show
      (if (Sum.inr i : BlockCoord d) = Sum.inr i then
          2 * Mu U (blockBasis (Sum.inr i)) a
        else
          Mu U (blockBasis (Sum.inr i) + blockBasis (Sum.inr i)) a
            - Mu U (blockBasis (Sum.inr i)) a
            - Mu U (blockBasis (Sum.inr i)) a) =
        if i = i then
          2 * Mu U (0, Pi.single i 1) a
        else
          Mu U ((0, Pi.single i 1) + (0, Pi.single i 1)) a
            - Mu U (0, Pi.single i 1) a
            - Mu U (0, Pi.single i 1) a
    simp [blockBasis]
  · have hsum : (Sum.inr i : BlockCoord d) ≠ Sum.inr j := by
      simpa using h
    show
      (if (Sum.inr i : BlockCoord d) = Sum.inr j then
          2 * Mu U (blockBasis (Sum.inr i)) a
        else
          Mu U (blockBasis (Sum.inr i) + blockBasis (Sum.inr j)) a
            - Mu U (blockBasis (Sum.inr i)) a
            - Mu U (blockBasis (Sum.inr j)) a) =
        if i = j then
          2 * Mu U (0, Pi.single i 1) a
        else
          Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a
            - Mu U (0, Pi.single i 1) a
            - Mu U (0, Pi.single j 1) a
    simp [blockBasis, h, hsum]

/-- Phase-1 bookkeeping for the diagonal entries of the upper-left block of the
canonical coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperLeft_apply_diag {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (i : Fin d) :
    (coarseBlockMatrix U a).upperLeft i i = 2 * Mu U (Pi.single i 1, 0) a := by
  simpa using coarseBlockMatrix_upperLeft_apply U a i i

/-- Phase-1 bookkeeping for the off-diagonal entries of the upper-left block of
the canonical coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperLeft_apply_offDiag {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {i j : Fin d} (hij : i ≠ j) :
    (coarseBlockMatrix U a).upperLeft i j =
      Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a
        - Mu U (Pi.single i 1, 0) a
        - Mu U (Pi.single j 1, 0) a := by
  simpa [hij] using coarseBlockMatrix_upperLeft_apply U a i j

/-- Phase-1 bookkeeping for the diagonal entries of the lower-right block of
the canonical coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerRight_apply_diag {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (i : Fin d) :
    (coarseBlockMatrix U a).lowerRight i i = 2 * Mu U (0, Pi.single i 1) a := by
  simpa using coarseBlockMatrix_lowerRight_apply U a i i

/-- Phase-1 bookkeeping for the off-diagonal entries of the lower-right block
of the canonical coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerRight_apply_offDiag {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {i j : Fin d} (hij : i ≠ j) :
    (coarseBlockMatrix U a).lowerRight i j =
      Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a
        - Mu U (0, Pi.single i 1) a
        - Mu U (0, Pi.single j 1) a := by
  simpa [hij] using coarseBlockMatrix_lowerRight_apply U a i j

@[simp] theorem coarseStarredBlockMatrixInv_eq_blockReflect {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    coarseStarredBlockMatrixInv U a = blockReflect (coarseBlockMatrix U a) :=
  rfl

/-!
Deterministic bookkeeping lemmas for the canonical coarse matrices.

This theorem layer packages the note-facing block matrices built from the
current canonical deterministic quantities and records the equalities they
satisfy once the relevant witness hypotheses are available.
-/

/-- The note-faithful coarse block matrix attached to deterministic data
`(sigma, sigmaStar, kappa)`. -/
noncomputable def blockMatrixOfDeterministicData {d : ℕ}
    (sigma sigmaStar kappa : Mat d) : BlockMat d :=
  { upperLeft := bCoarse sigma sigmaStar kappa
    upperRight := -((matTranspose kappa) * sigmaStar⁻¹)
    lowerLeft := -(sigmaStar⁻¹ * kappa)
    lowerRight := sigmaStar⁻¹ }

@[simp] theorem blockMatrixOfDeterministicData_upperLeft {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperLeft =
      bCoarse sigma sigmaStar kappa :=
  rfl

@[simp] theorem blockMatrixOfDeterministicData_upperRight {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperRight =
      -((matTranspose kappa) * sigmaStar⁻¹) :=
  rfl

@[simp] theorem blockMatrixOfDeterministicData_lowerLeft {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerLeft =
      -(sigmaStar⁻¹ * kappa) :=
  rfl

@[simp] theorem blockMatrixOfDeterministicData_lowerRight {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerRight =
      sigmaStar⁻¹ :=
  rfl

theorem blockMatrixOfDeterministicData_upperLeft_smul {d : ℕ}
    {sigma sigmaStar kappa : Mat d} (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (blockMatrixOfDeterministicData (lam • sigma) (lam • sigmaStar) (lam • kappa)).upperLeft =
      lam • (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperLeft := by
  simp [blockMatrixOfDeterministicData, bCoarse_smul hdet hlam]

theorem blockMatrixOfDeterministicData_upperRight_smul {d : ℕ}
    {sigma sigmaStar kappa : Mat d} (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (blockMatrixOfDeterministicData (lam • sigma) (lam • sigmaStar) (lam • kappa)).upperRight =
      (blockMatrixOfDeterministicData sigma sigmaStar kappa).upperRight := by
  rw [blockMatrixOfDeterministicData_upperRight, blockMatrixOfDeterministicData_upperRight]
  congr 1
  have htranspose : matTranspose (lam • kappa) = lam • matTranspose kappa := by
    simp [matTranspose]
  rw [htranspose, nonsing_inv_smul lam hlam.ne' hdet]
  simp [smul_smul, inv_mul_cancel₀ hlam.ne']

theorem blockMatrixOfDeterministicData_lowerLeft_smul {d : ℕ}
    {sigma sigmaStar kappa : Mat d} (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (blockMatrixOfDeterministicData (lam • sigma) (lam • sigmaStar) (lam • kappa)).lowerLeft =
      (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerLeft := by
  rw [blockMatrixOfDeterministicData_lowerLeft, blockMatrixOfDeterministicData_lowerLeft]
  congr 1
  rw [nonsing_inv_smul lam hlam.ne' hdet, smul_mul_assoc]
  simp [smul_smul, inv_mul_cancel₀ hlam.ne']

theorem blockMatrixOfDeterministicData_lowerRight_smul {d : ℕ}
    {sigma sigmaStar kappa : Mat d} (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (blockMatrixOfDeterministicData (lam • sigma) (lam • sigmaStar) (lam • kappa)).lowerRight =
      lam⁻¹ • (blockMatrixOfDeterministicData sigma sigmaStar kappa).lowerRight := by
  simp [blockMatrixOfDeterministicData, nonsing_inv_smul lam hlam.ne' hdet]

/-- The reflected note-faithful starred inverse block matrix attached to
deterministic data `(sigma, sigmaStar, kappa)`. -/
noncomputable def starredBlockMatrixInvOfDeterministicData {d : ℕ}
    (sigma sigmaStar kappa : Mat d) : BlockMat d :=
  blockReflect (blockMatrixOfDeterministicData sigma sigmaStar kappa)

@[simp] theorem starredBlockMatrixInvOfDeterministicData_eq_blockReflect {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa =
      blockReflect (blockMatrixOfDeterministicData sigma sigmaStar kappa) :=
  rfl

@[simp] theorem starredBlockMatrixInvOfDeterministicData_upperLeft {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa).upperLeft =
      sigmaStar⁻¹ :=
  rfl

@[simp] theorem starredBlockMatrixInvOfDeterministicData_upperRight {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa).upperRight =
      -(sigmaStar⁻¹ * kappa) :=
  rfl

@[simp] theorem starredBlockMatrixInvOfDeterministicData_lowerLeft {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa).lowerLeft =
      -((matTranspose kappa) * sigmaStar⁻¹) :=
  rfl

@[simp] theorem starredBlockMatrixInvOfDeterministicData_lowerRight {d : ℕ}
    (sigma sigmaStar kappa : Mat d) :
    (starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa).lowerRight =
      bCoarse sigma sigmaStar kappa :=
  rfl

/-- The coarse block candidate built from the canonical deterministic coarse
pieces already defined in `Definitions.lean`. -/
noncomputable def deterministicCoarseBlockMatrix {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) : BlockMat d :=
  { upperLeft := sigmaCoarse U a
      + (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a
    upperRight := -((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a)
    lowerLeft := -(sigmaStarInvKappaCoarse U a)
    lowerRight := sigmaStarInvCoarse U a }

@[simp] theorem deterministicCoarseBlockMatrix_upperLeft {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicCoarseBlockMatrix U a).upperLeft =
      sigmaCoarse U a
        + (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a :=
  rfl

@[simp] theorem deterministicCoarseBlockMatrix_upperRight {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicCoarseBlockMatrix U a).upperRight =
      -((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a) :=
  rfl

@[simp] theorem deterministicCoarseBlockMatrix_lowerLeft {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicCoarseBlockMatrix U a).lowerLeft =
      -(sigmaStarInvKappaCoarse U a) :=
  rfl

@[simp] theorem deterministicCoarseBlockMatrix_lowerRight {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicCoarseBlockMatrix U a).lowerRight =
      sigmaStarInvCoarse U a :=
  rfl

/-- The reflected starred inverse block candidate built from the canonical
deterministic coarse pieces. -/
noncomputable def deterministicStarredBlockMatrixInv {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) : BlockMat d :=
  blockReflect (deterministicCoarseBlockMatrix U a)

@[simp] theorem deterministicStarredBlockMatrixInv_eq_blockReflect {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    deterministicStarredBlockMatrixInv U a =
      blockReflect (deterministicCoarseBlockMatrix U a) :=
  rfl

@[simp] theorem deterministicStarredBlockMatrixInv_upperLeft {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicStarredBlockMatrixInv U a).upperLeft = sigmaStarInvCoarse U a :=
  rfl

@[simp] theorem deterministicStarredBlockMatrixInv_upperRight {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicStarredBlockMatrixInv U a).upperRight =
      -(sigmaStarInvKappaCoarse U a) :=
  rfl

@[simp] theorem deterministicStarredBlockMatrixInv_lowerLeft {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicStarredBlockMatrixInv U a).lowerLeft =
      -((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a) :=
  rfl

@[simp] theorem deterministicStarredBlockMatrixInv_lowerRight {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) :
    (deterministicStarredBlockMatrixInv U a).lowerRight =
      sigmaCoarse U a
        + (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a :=
  rfl

theorem deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    deterministicCoarseBlockMatrix U a =
      blockMatrixOfDeterministicData sigma sigmaStar kappa := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  · simp [deterministicCoarseBlockMatrix, blockMatrixOfDeterministicData, bCoarse,
      sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
      eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
      sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  · simp [deterministicCoarseBlockMatrix, blockMatrixOfDeterministicData,
      eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
      sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  · simp [deterministicCoarseBlockMatrix, blockMatrixOfDeterministicData,
      sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]
  · simp [deterministicCoarseBlockMatrix, blockMatrixOfDeterministicData,
      sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]

theorem deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    deterministicCoarseBlockMatrix U a =
      blockMatrixOfDeterministicData sigma sigmaStar kappa :=
  deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
    hS hK hSigma hdet

theorem deterministicStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    deterministicStarredBlockMatrixInv U a =
      starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa := by
  rw [deterministicStarredBlockMatrixInv, starredBlockMatrixInvOfDeterministicData,
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]

theorem deterministicStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    deterministicStarredBlockMatrixInv U a =
      starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa :=
  deterministicStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isSigmaCoarse
    hS hK hSigma hdet

theorem coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    coarseBlockMatrix U a = deterministicCoarseBlockMatrix U a := by
  symm
  exact eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA

theorem coarseBlockMatrix_eq_deterministicCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    coarseBlockMatrix U a = deterministicCoarseBlockMatrix U a :=
  coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA

theorem coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    coarseBlockMatrix U a = blockMatrixOfDeterministicData sigma sigmaStar kappa := by
  rw [coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA,
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]

/-- Canonical upper-left block formula for `\mathbf A(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseBlockMatrix_upperLeft_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).upperLeft =
      sigmaCoarse U a
        + (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a := by
  simpa using
    congrArg BlockMat.upperLeft
      (coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA)

/-- Canonical upper-right block formula for `\mathbf A(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseBlockMatrix_upperRight_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).upperRight =
      -((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a) := by
  simpa using
    congrArg BlockMat.upperRight
      (coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA)

/-- Canonical lower-left block formula for `\mathbf A(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseBlockMatrix_lowerLeft_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).lowerLeft = -(sigmaStarInvKappaCoarse U a) := by
  simpa using
    congrArg BlockMat.lowerLeft
      (coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA)

/-- Canonical lower-right block formula for `\mathbf A(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a := by
  simpa using
    congrArg BlockMat.lowerRight
      (coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA)

/-- Public upper-left block formula for the coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseBlockMatrix U a).upperLeft = bCoarse sigma sigmaStar kappa := by
  simpa using
    congrArg BlockMat.upperLeft
      (coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public upper-right block formula for the coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_upperRight_eq_neg_transpose_kappa_mul_sigmaStar_inv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseBlockMatrix U a).upperRight = -((matTranspose kappa) * sigmaStar⁻¹) := by
  simpa using
    congrArg BlockMat.upperRight
      (coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public lower-left block formula for the coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerLeft_eq_neg_sigmaStar_inv_mul_kappa_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseBlockMatrix U a).lowerLeft = -(sigmaStar⁻¹ * kappa) := by
  simpa using
    congrArg BlockMat.lowerLeft
      (coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public lower-right block formula for the coarse matrix `\mathbf A(U; a)`. -/
theorem coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseBlockMatrix U a).lowerRight = sigmaStar⁻¹ := by
  simpa using
    congrArg BlockMat.lowerRight
      (coarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public formula for the first component of `\mathbf A(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseBlockMatrix_fst_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (blockMatVecMul (coarseBlockMatrix U a) (p, q)).1 =
      matVecMul sigma p -
        matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
  calc
    (blockMatVecMul (coarseBlockMatrix U a) (p, q)).1 =
        matVecMul (bCoarse sigma sigmaStar kappa) p +
          matVecMul (-((matTranspose kappa) * sigmaStar⁻¹)) q := by
      rw [blockMatVecMul_fst]
      rw [coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hA hS hK hSigma hdet,
        coarseBlockMatrix_upperRight_eq_neg_transpose_kappa_mul_sigmaStar_inv_of_isCoarseBlockMatrix
          hA hS hK hSigma hdet]
    _ = matVecMul sigma p -
          matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
      unfold bCoarse
      rw [add_matVecMul]
      ext i
      simp [sub_eq_add_neg, matVecMul_add, matVecMul_mul, neg_matVecMul,
        matVecMul_neg, Matrix.mul_assoc]
      ring

/-- Public formula for the second component of `\mathbf A(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseBlockMatrix_snd_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (blockMatVecMul (coarseBlockMatrix U a) (p, q)).2 =
      matVecMul sigmaStar⁻¹ (q - matVecMul kappa p) := by
  rw [blockMatVecMul_snd]
  rw [coarseBlockMatrix_lowerLeft_eq_neg_sigmaStar_inv_mul_kappa_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet,
    coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet]
  ext i
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_mul, neg_matVecMul, matVecMul_neg]
  ring

/-- Public formula for `\mathbf A(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseBlockMatrix_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    blockMatVecMul (coarseBlockMatrix U a) (p, q) =
      (matVecMul sigma p -
          matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)),
        matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
  ext i
  · simpa using congrFun
      (blockMatVecMul_coarseBlockMatrix_fst_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet p q) i
  · simpa using congrFun
      (blockMatVecMul_coarseBlockMatrix_snd_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet p q) i

theorem coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    coarseStarredBlockMatrixInv U a = deterministicStarredBlockMatrixInv U a := by
  rw [coarseStarredBlockMatrixInv, deterministicStarredBlockMatrixInv,
    coarseBlockMatrix_eq_deterministicCoarseBlockMatrix_of_isCoarseBlockMatrix hA]

theorem coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    coarseStarredBlockMatrixInv U a = deterministicStarredBlockMatrixInv U a :=
  coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA

theorem coarseStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    coarseStarredBlockMatrixInv U a =
      starredBlockMatrixInvOfDeterministicData sigma sigmaStar kappa := by
  rw [coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA,
    deterministicStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]

/-- If the pure-flux slice of `\mu` matches the pure-flux slice of
`\mathcal J`, then the lower-right block of the canonical coarse block matrix
realizes the canonical `\sigma_*^{-1}(U; a)` data. -/
theorem isSigmaStarInvCoarse_coarseBlockMatrix_lowerRight_of_mu_zero_right_eq_responseJ_zero
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a) :
    IsSigmaStarInvCoarse U a (coarseBlockMatrix U a).lowerRight := by
  have hA : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  refine ⟨?_, ?_⟩
  · ext i j
    simpa [Matrix.transpose, blockMatEntry] using (hA.1 (Sum.inr i) (Sum.inr j)).symm
  · intro q
    calc
      ResponseJ U 0 q a = Mu U (0, q) a := (hMuResp q).symm
      _ = (1 / 2 : ℝ) * blockVecDot (0, q) (blockMatVecMul (coarseBlockMatrix U a) (0, q)) := by
            simpa using hA.2 (0, q)
      _ = (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) := by
            simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]

/-- If the pure-flux slice of `\mu` matches the pure-flux slice of
`\mathcal J`, then the lower-right block of the canonical coarse block matrix
is the canonical `\sigma_*^{-1}(U; a)`. -/
theorem coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a) :
    (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a :=
  eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse
    (isSigmaStarInvCoarse_coarseBlockMatrix_lowerRight_of_mu_zero_right_eq_responseJ_zero
      (U := U) (a := a) hex hMuResp)

/-- If the pure-flux slice of `\mu` matches the pure-flux slice of
`\mathcal J`, then the upper-left block of `\mathbf A_*^{-1}(U; a)` is the
canonical `\sigma_*^{-1}(U; a)`. -/
theorem coarseStarredBlockMatrixInv_upperLeft_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a) :
    (coarseStarredBlockMatrixInv U a).upperLeft = sigmaStarInvCoarse U a := by
  rw [coarseStarredBlockMatrixInv_eq_blockReflect]
  simpa using
    coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
      (U := U) (a := a) hex hMuResp

/-- Canonical upper-left block formula for `\mathbf A_*^{-1}(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseStarredBlockMatrixInv_upperLeft_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseStarredBlockMatrixInv U a).upperLeft = sigmaStarInvCoarse U a := by
  simpa using
    congrArg BlockMat.upperLeft
      (coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA)

/-- Canonical upper-right block formula for `\mathbf A_*^{-1}(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseStarredBlockMatrixInv_upperRight_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseStarredBlockMatrixInv U a).upperRight = -(sigmaStarInvKappaCoarse U a) := by
  simpa using
    congrArg BlockMat.upperRight
      (coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA)

/-- Canonical lower-left block formula for `\mathbf A_*^{-1}(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseStarredBlockMatrixInv_lowerLeft_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseStarredBlockMatrixInv U a).lowerLeft =
      -((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a) := by
  simpa using
    congrArg BlockMat.lowerLeft
      (coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA)

/-- Canonical lower-right block formula for `\mathbf A_*^{-1}(U; a)` once the
deterministic coarse candidate is identified as coarse. -/
theorem coarseStarredBlockMatrixInv_lowerRight_eq_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a)) :
    (coarseStarredBlockMatrixInv U a).lowerRight =
      sigmaCoarse U a
        + (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a := by
  simpa using
    congrArg BlockMat.lowerRight
      (coarseStarredBlockMatrixInv_eq_deterministicStarredBlockMatrixInv_of_isCoarseBlockMatrix hA)

/-- Public upper-left block formula for the reflected coarse matrix
`\mathbf A_*^{-1}(U; a)`. -/
theorem coarseStarredBlockMatrixInv_upperLeft_eq_sigmaStar_inv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseStarredBlockMatrixInv U a).upperLeft = sigmaStar⁻¹ := by
  simpa using
    congrArg BlockMat.upperLeft
      (coarseStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public upper-right block formula for the reflected coarse matrix
`\mathbf A_*^{-1}(U; a)`. -/
theorem coarseStarredBlockMatrixInv_upperRight_eq_neg_sigmaStar_inv_mul_kappa_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseStarredBlockMatrixInv U a).upperRight = -(sigmaStar⁻¹ * kappa) := by
  simpa using
    congrArg BlockMat.upperRight
      (coarseStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public lower-left block formula for the reflected coarse matrix
`\mathbf A_*^{-1}(U; a)`. -/
theorem coarseStarredBlockMatrixInv_lowerLeft_eq_neg_transpose_kappa_mul_sigmaStar_inv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseStarredBlockMatrixInv U a).lowerLeft =
      -((matTranspose kappa) * sigmaStar⁻¹) := by
  simpa using
    congrArg BlockMat.lowerLeft
      (coarseStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public lower-right block formula for the reflected coarse matrix
`\mathbf A_*^{-1}(U; a)`. -/
theorem coarseStarredBlockMatrixInv_lowerRight_eq_bCoarse_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (coarseStarredBlockMatrixInv U a).lowerRight = bCoarse sigma sigmaStar kappa := by
  simpa using
    congrArg BlockMat.lowerRight
      (coarseStarredBlockMatrixInv_eq_starredBlockMatrixInvOfDeterministicData_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet)

/-- Public formula for the first component of `\mathbf A_*^{-1}(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseStarredBlockMatrixInv_fst_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (blockMatVecMul (coarseStarredBlockMatrixInv U a) (p, q)).1 =
      matVecMul sigmaStar⁻¹ (p - matVecMul kappa q) := by
  rw [blockMatVecMul_fst]
  rw [coarseStarredBlockMatrixInv_upperLeft_eq_sigmaStar_inv_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet,
    coarseStarredBlockMatrixInv_upperRight_eq_neg_sigmaStar_inv_mul_kappa_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet]
  ext i
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_mul, neg_matVecMul, matVecMul_neg]

/-- Public formula for the second component of `\mathbf A_*^{-1}(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseStarredBlockMatrixInv_snd_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    (blockMatVecMul (coarseStarredBlockMatrixInv U a) (p, q)).2 =
      matVecMul sigma q -
        matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (p - matVecMul kappa q)) := by
  calc
    (blockMatVecMul (coarseStarredBlockMatrixInv U a) (p, q)).2 =
        matVecMul (-((matTranspose kappa) * sigmaStar⁻¹)) p +
          matVecMul (bCoarse sigma sigmaStar kappa) q := by
      rw [blockMatVecMul_snd]
      rw [coarseStarredBlockMatrixInv_lowerLeft_eq_neg_transpose_kappa_mul_sigmaStar_inv_of_isCoarseBlockMatrix
          hA hS hK hSigma hdet,
        coarseStarredBlockMatrixInv_lowerRight_eq_bCoarse_of_isCoarseBlockMatrix
          hA hS hK hSigma hdet]
    _ = matVecMul sigma q -
          matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (p - matVecMul kappa q)) := by
      unfold bCoarse
      rw [add_matVecMul]
      ext i
      simp [sub_eq_add_neg, matVecMul_add, matVecMul_mul, neg_matVecMul,
        matVecMul_neg, Matrix.mul_assoc]
      ring

/-- Public formula for `\mathbf A_*^{-1}(U; a) (p, q)`. -/
theorem blockMatVecMul_coarseStarredBlockMatrixInv_of_isCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    blockMatVecMul (coarseStarredBlockMatrixInv U a) (p, q) =
      (matVecMul sigmaStar⁻¹ (p - matVecMul kappa q),
        matVecMul sigma q -
          matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ (p - matVecMul kappa q))) := by
  ext i
  · simpa using congrFun
      (blockMatVecMul_coarseStarredBlockMatrixInv_fst_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet p q) i
  · simpa using congrFun
      (blockMatVecMul_coarseStarredBlockMatrixInv_snd_of_isCoarseBlockMatrix
        hA hS hK hSigma hdet p q) i

end

end Homogenization
