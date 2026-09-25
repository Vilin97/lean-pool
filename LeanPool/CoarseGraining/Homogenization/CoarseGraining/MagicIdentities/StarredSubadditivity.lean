/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.BlockSubadditivity

/-! # Starred Subadditivity -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
Starred-block and `b`-matrix subadditivity consequences.
-/

theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a) X) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
  refine
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      j Q a hEll ?_ ?_ X
  · intro p q
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet Q) a hAQ hSQ hKQ hSigmaQ hdetQ p q
  · intro R hR p q
    rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet R) a hAR hSR hKR hSigmaR hdetR p q

theorem coarseStarredBlockMatrixInv_upperLeft_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a).upperLeft p) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).upperLeft p)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (p, 0)

theorem coarseStarredBlockMatrixInv_lowerRight_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a).lowerRight q) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).lowerRight q)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (0, q)

theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet (originCube d n)) a) X) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
  simpa using
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X

theorem coarseStarredBlockMatrixInv_upperLeft_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet (originCube d n)) a).upperLeft p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).upperLeft p)) := by
  simpa using
    coarseStarredBlockMatrixInv_upperLeft_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc p

theorem coarseStarredBlockMatrixInv_lowerRight_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (coarseStarredBlockMatrixInv (openCubeSet (originCube d n)) a).lowerRight q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a).lowerRight q)) := by
  simpa using
    coarseStarredBlockMatrixInv_lowerRight_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc q

theorem coarseStarredBlockMatrixInv_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a) X) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet R) a) X)) := by
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a) X)
      = (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet (originCube d n)) a) X) := by
            rw [coarseStarredBlockMatrixInv_cubeSet_eq_openCubeSet_of_triadicCube
              (Q := originCube d n) a]
    _ ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
            exact
              coarseStarredBlockMatrixInv_subadditive_openCubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
                j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X
    _ = descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet R) a) X)) := by
            unfold descendantsAverage
            refine congrArg (fun t => ((descendantsAtDepth (originCube d n) j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rw [← coarseStarredBlockMatrixInv_cubeSet_eq_openCubeSet_of_triadicCube (Q := R) a]

theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    BlockMatLoewnerLE (coarseStarredBlockMatrixInv (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet Q) a) X)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseStarredBlockMatrixInv (openCubeSet R) a) X)) := by
            exact
              coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
                j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X
    _ = (1 / 2 : ℝ) *
          blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat Q j
                (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) X) := by
            rw [descendantsAverage_smul]
            rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]

theorem coarseStarredBlockMatrixInv_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    BlockMatLoewnerLE (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a)
      (descendantsAverageBlockMat (originCube d n) j
        (fun R => coarseStarredBlockMatrixInv (cubeSet R) a)) := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a) X)
      ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseStarredBlockMatrixInv (cubeSet R) a) X)) := by
            exact
              coarseStarredBlockMatrixInv_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
                j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X
    _ = (1 / 2 : ℝ) *
          blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat (originCube d n) j
                (fun R => coarseStarredBlockMatrixInv (cubeSet R) a)) X) := by
            rw [descendantsAverage_smul]
            rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]

theorem coarseStarredBlockMatrixInv_upperLeft_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a).upperLeft p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseStarredBlockMatrixInv (cubeSet R) a).upperLeft p)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (p, 0)

theorem coarseStarredBlockMatrixInv_lowerRight_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hAQ : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (coarseStarredBlockMatrixInv (cubeSet (originCube d n)) a).lowerRight q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseStarredBlockMatrixInv (cubeSet R) a).lowerRight q)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseStarredBlockMatrixInv_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (0, q)

theorem sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (sigmaStarInvCoarse (openCubeSet R) a) q)) := by
  have hscalar :
      ResponseJ (openCubeSet Q) 0 q a ≤
        descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) 0 q a) :=
    responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
      j Q a hEll 0 q
  calc
    (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q)
      = ResponseJ (openCubeSet Q) 0 q a := by
          symm
          simpa [matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
            basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
              (U := openCubeSet Q) a hSQ hKQ hSigmaQ hdetQ (0 : Vec d) q
    _ ≤ descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) 0 q a) := hscalar
    _ = descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * vecDot q
              (matVecMul (sigmaStarInvCoarse (openCubeSet R) a) q)) := by
          unfold descendantsAverage
          refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
          simpa [matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
            basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
              (U := openCubeSet R) a hSR hKR hSigmaR hdetR (0 : Vec d) q

theorem sigmaStarInvCoarse_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (sigmaStarInvCoarse (openCubeSet (originCube d n)) a) q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (sigmaStarInvCoarse (openCubeSet R) a) q)) := by
  simpa using
    sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hSQ hKQ hSigmaQ hdetQ hDesc q

theorem sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (q : Vec d) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (sigmaStarInvCoarse (cubeSet (originCube d n)) a) q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (sigmaStarInvCoarse (cubeSet R) a) q)) := by
  calc
    (1 / 2 : ℝ) * vecDot q
        (matVecMul (sigmaStarInvCoarse (cubeSet (originCube d n)) a) q)
      = (1 / 2 : ℝ) * vecDot q
          (matVecMul (sigmaStarInvCoarse (openCubeSet (originCube d n)) a) q) := by
            rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
              (Q := originCube d n) (a := a) hSQ]
    _ ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot q
              (matVecMul (sigmaStarInvCoarse (openCubeSet R) a) q)) := by
            exact
              sigmaStarInvCoarse_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
                j n a hEll hSQ hKQ hSigmaQ hdetQ hDesc q
    _ = descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot q
              (matVecMul (sigmaStarInvCoarse (cubeSet R) a) q)) := by
            unfold descendantsAverage
            refine congrArg (fun t => ((descendantsAtDepth (originCube d n) j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
            rw [← sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
              (Q := R) (a := a) hSR]

theorem sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    MatLoewnerLE (sigmaStarInvCoarse (openCubeSet Q) a)
      (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (openCubeSet R) a)) := by
  intro q
  calc
    (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * vecDot q
              (matVecMul (sigmaStarInvCoarse (openCubeSet R) a) q)) := by
            exact
              sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
                j Q a hEll hSQ hKQ hSigmaQ hdetQ hDesc q
    _ = (1 / 2 : ℝ) *
          vecDot q
            (matVecMul
              (descendantsAverageMat Q j
                (fun R => sigmaStarInvCoarse (openCubeSet R) a)) q) := by
            rw [descendantsAverage_smul]
            rw [vecDot_matVecMul_descendantsAverageMat]

theorem sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    MatLoewnerLE (sigmaStarInvCoarse (cubeSet (originCube d n)) a)
      (descendantsAverageMat (originCube d n) j
        (fun R => sigmaStarInvCoarse (cubeSet R) a)) := by
  intro q
  calc
    (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (cubeSet (originCube d n)) a) q)
      ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot q
              (matVecMul (sigmaStarInvCoarse (cubeSet R) a) q)) := by
            exact
              sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
                j n a hEll hSQ hKQ hSigmaQ hdetQ hDesc q
    _ = (1 / 2 : ℝ) *
          vecDot q
            (matVecMul
              (descendantsAverageMat (originCube d n) j
                (fun R => sigmaStarInvCoarse (cubeSet R) a)) q) := by
            rw [descendantsAverage_smul]
            rw [vecDot_matVecMul_descendantsAverageMat]

theorem bCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (openCubeSet Q) a)
            (sigmaStarCoarse (openCubeSet Q) a)
            (kappaCoarse (openCubeSet Q) a)) p) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (bCoarse (sigmaCoarse (openCubeSet R) a)
                (sigmaStarCoarse (openCubeSet R) a)
                (kappaCoarse (openCubeSet R) a)) p)) := by
  have hscalar :
      ResponseJ (openCubeSet Q) p 0 a ≤
        descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p 0 a) :=
    responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
      j Q a hEll p 0
  calc
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (openCubeSet Q) a)
            (sigmaStarCoarse (openCubeSet Q) a)
            (kappaCoarse (openCubeSet Q) a)) p)
      = ResponseJ (openCubeSet Q) p 0 a := by
          symm
          exact basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
            (U := openCubeSet Q) a hSQ hKQ hSigmaQ hdetQ p
    _ ≤ descendantsAverage Q j (fun R => ResponseJ (openCubeSet R) p 0 a) := hscalar
    _ = descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul
                (bCoarse (sigmaCoarse (openCubeSet R) a)
                  (sigmaStarCoarse (openCubeSet R) a)
                  (kappaCoarse (openCubeSet R) a)) p)) := by
          unfold descendantsAverage
          refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
          exact
            basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
              (U := openCubeSet R) a hSR hKR hSigmaR hdetR p

theorem bCoarse_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (openCubeSet (originCube d n)) a)
            (sigmaStarCoarse (openCubeSet (originCube d n)) a)
            (kappaCoarse (openCubeSet (originCube d n)) a)) p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (bCoarse (sigmaCoarse (openCubeSet R) a)
                (sigmaStarCoarse (openCubeSet R) a)
                (kappaCoarse (openCubeSet R) a)) p)) := by
  simpa using
    bCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hSQ hKQ hSigmaQ hdetQ hDesc p

theorem bCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (p : Vec d) :
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (cubeSet (originCube d n)) a)
            (sigmaStarCoarse (cubeSet (originCube d n)) a)
            (kappaCoarse (cubeSet (originCube d n)) a)) p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (bCoarse (sigmaCoarse (cubeSet R) a)
                (sigmaStarCoarse (cubeSet R) a)
                (kappaCoarse (cubeSet R) a)) p)) := by
  calc
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (cubeSet (originCube d n)) a)
            (sigmaStarCoarse (cubeSet (originCube d n)) a)
            (kappaCoarse (cubeSet (originCube d n)) a)) p)
      = (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (bCoarse (sigmaCoarse (openCubeSet (originCube d n)) a)
              (sigmaStarCoarse (openCubeSet (originCube d n)) a)
              (kappaCoarse (openCubeSet (originCube d n)) a)) p) := by
                rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
                  (Q := originCube d n) (a := a) hSQ hKQ hSigmaQ hdetQ]
    _ ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul
                (bCoarse (sigmaCoarse (openCubeSet R) a)
                  (sigmaStarCoarse (openCubeSet R) a)
                  (kappaCoarse (openCubeSet R) a)) p)) := by
            exact
              bCoarse_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
                j n a hEll hSQ hKQ hSigmaQ hdetQ hDesc p
    _ = descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul
                (bCoarse (sigmaCoarse (cubeSet R) a)
                  (sigmaStarCoarse (cubeSet R) a)
                  (kappaCoarse (cubeSet R) a)) p)) := by
            unfold descendantsAverage
            refine congrArg (fun t => ((descendantsAtDepth (originCube d n) j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
            rw [← bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
              (Q := R) (a := a) hSR hKR hSigmaR hdetR]

theorem bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet Q) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet Q) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet Q) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse (openCubeSet Q) a)
        (sigmaStarCoarse (openCubeSet Q) a)
        (kappaCoarse (openCubeSet Q) a))
      (descendantsAverageMat Q j
        (fun R =>
          bCoarse (sigmaCoarse (openCubeSet R) a)
            (sigmaStarCoarse (openCubeSet R) a)
            (kappaCoarse (openCubeSet R) a))) := by
  intro p
  calc
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (openCubeSet Q) a)
            (sigmaStarCoarse (openCubeSet Q) a)
            (kappaCoarse (openCubeSet Q) a)) p)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul
                (bCoarse (sigmaCoarse (openCubeSet R) a)
                  (sigmaStarCoarse (openCubeSet R) a)
                  (kappaCoarse (openCubeSet R) a)) p)) := by
            exact
              bCoarse_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
                j Q a hEll hSQ hKQ hSigmaQ hdetQ hDesc p
    _ = (1 / 2 : ℝ) *
          vecDot p
            (matVecMul
              (descendantsAverageMat Q j
                (fun R =>
                  bCoarse (sigmaCoarse (openCubeSet R) a)
                    (sigmaStarCoarse (openCubeSet R) a)
                    (kappaCoarse (openCubeSet R) a))) p) := by
            rw [descendantsAverage_smul]
            rw [vecDot_matVecMul_descendantsAverageMat]

theorem bCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (j : ℕ) (n : ℤ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    {sigmaQ sigmaStarQ kappaQ : Mat d}
    (hSQ : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStarQ)
    (hKQ : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStarQ kappaQ)
    (hSigmaQ : IsSigmaCoarse (openCubeSet (originCube d n)) a sigmaQ sigmaStarQ kappaQ)
    (hdetQ : IsUnit sigmaStarQ.det)
    (hDesc :
      ∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse (cubeSet (originCube d n)) a)
        (sigmaStarCoarse (cubeSet (originCube d n)) a)
        (kappaCoarse (cubeSet (originCube d n)) a))
      (descendantsAverageMat (originCube d n) j
        (fun R =>
          bCoarse (sigmaCoarse (cubeSet R) a)
            (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a))) := by
  intro p
  calc
    (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse (sigmaCoarse (cubeSet (originCube d n)) a)
            (sigmaStarCoarse (cubeSet (originCube d n)) a)
            (kappaCoarse (cubeSet (originCube d n)) a)) p)
      ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul
                (bCoarse (sigmaCoarse (cubeSet R) a)
                  (sigmaStarCoarse (cubeSet R) a)
                  (kappaCoarse (cubeSet R) a)) p)) := by
            exact
              bCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
                j n a hEll hSQ hKQ hSigmaQ hdetQ hDesc p
    _ = (1 / 2 : ℝ) *
          vecDot p
            (matVecMul
              (descendantsAverageMat (originCube d n) j
                (fun R =>
                  bCoarse (sigmaCoarse (cubeSet R) a)
                    (sigmaStarCoarse (cubeSet R) a)
                    (kappaCoarse (cubeSet R) a))) p) := by
            rw [descendantsAverage_smul]
            rw [vecDot_matVecMul_descendantsAverageMat]

end

end Homogenization
