/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.Basics

/-! # Block Subadditivity -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
Block-matrix and response-side subadditivity packages.
-/

theorem magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_slice_formulas {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d)
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hRespUpper :
      ∀ p : Vec d,
        ResponseJ U p 0 a =
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseBlockMatrix U a).upperLeft p))
    (hRespMixed :
      ∀ p q : Vec d,
        ResponseJ U p q a - ResponseJ U p 0 a - ResponseJ U 0 q a + vecDot p q =
          -vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p))
    (hRespLower :
      ∀ q : Vec d,
        ResponseJ U 0 q a =
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseBlockMatrix U a).lowerRight q))
    (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
      vecDot p q := by
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  calc
    ResponseJ U p q a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
      linarith [hRespUpper p, hRespMixed p q, hRespLower q]
    _ =
        (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
          vecDot p q := by
      linarith [magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hAc.1 p q]

theorem magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
      vecDot p q := by
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix
      ⟨deterministicCoarseBlockMatrix U a, hA⟩
  calc
    ResponseJ U p q a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
      exact basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q
    _ =
        (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
          vecDot p q := by
      linarith [magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hAc.1 p q]

private theorem coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) :
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using! cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using! openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  calc
    coarseBlockMatrix (cubeSet Q) a
        = coarseBlockMatrix (translateSet z (cubeSet (originCube d Q.scale))) a := by
            rw [hcube]
    _ = coarseBlockMatrix (cubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
          exact coarseBlockMatrix_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) a
    _ = coarseBlockMatrix (openCubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
          exact coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) (a := translateCoeffField z a)
    _ = coarseBlockMatrix (translateSet z (openCubeSet (originCube d Q.scale))) a := by
          symm
          exact coarseBlockMatrix_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) a
    _ = coarseBlockMatrix (openCubeSet Q) a := by
          rw [hopen]

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_pair_of_isSigmaCoarse
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
    (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q))) := by
  refine
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_pair_of_responseJ_blockQuadratic
      j Q a hEll ?_ ?_ p q
  · intro p q
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet Q) a hAQ hSQ hKQ hSigmaQ hdetQ p q
  · intro R hR p q
    rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet R) a hAR hSR hKR hSigmaR hdetR p q

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
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
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) X) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
  refine
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      j Q a hEll ?_ ?_ X
  · intro p q
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet Q) a hAQ hSQ hKQ hSigmaQ hdetQ p q
  · intro R hR p q
    rcases hDesc R hR with ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
      (openCubeSet R) a hAR hSR hKR hSigmaR hdetR p q

theorem coarseBlockMatrix_upperLeft_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseBlockMatrix (openCubeSet R) a).upperLeft p)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (p, 0)

theorem coarseBlockMatrix_lowerRight_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight q) ≤
      descendantsAverage Q j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight q)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (0, q)

theorem coarseBlockMatrix_subadditive_openCubeSet_originCube_descendantsAtDepth_pair_of_isSigmaCoarse
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
    (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a) (-p, q)) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q))) := by
  simpa using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_pair_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc p q

theorem coarseBlockMatrix_subadditive_openCubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
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
        (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a) X) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
  simpa using
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X

theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
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
    BlockMatLoewnerLE (coarseBlockMatrix (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) X)
      ≤ descendantsAverage Q j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
            exact
              coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
                j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X
    _ = (1 / 2 : ℝ) *
          blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) X) := by
            rw [descendantsAverage_smul]
            rw [blockVecDot_blockMatVecMul_descendantsAverageBlockMat]

theorem coarseBlockMatrix_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
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
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet (originCube d n)) a)
      (descendantsAverageBlockMat (originCube d n) j (fun R => coarseBlockMatrix (cubeSet R) a)) := by
  intro X
  simpa [descendantsAverageBlockMat, descendantsAverageMat,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] using
    (coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X)

theorem coarseBlockMatrix_upperLeft_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a).upperLeft p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseBlockMatrix (openCubeSet R) a).upperLeft p)) := by
  simpa using
    coarseBlockMatrix_upperLeft_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc p

theorem coarseBlockMatrix_lowerRight_subadditive_openCubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a).lowerRight q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight q)) := by
  simpa using
    coarseBlockMatrix_lowerRight_subadditive_openCubeSet_descendantsAtDepth_of_isSigmaCoarse
      (j := j) (Q := originCube d n) (a := a) hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc q

theorem coarseBlockMatrix_subadditive_cubeSet_originCube_descendantsAtDepth_pair_of_isSigmaCoarse
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
    (p q : Vec d) :
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a) (-p, q)) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) (-p, q))) := by
  calc
    (1 / 2 : ℝ) * blockVecDot (-p, q)
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a) (-p, q))
      = (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a) (-p, q)) := by
            rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (Q := originCube d n) a]
    _ ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q))) := by
            exact
              coarseBlockMatrix_subadditive_openCubeSet_originCube_descendantsAtDepth_pair_of_isSigmaCoarse
                j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc p q
    _ = descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) (-p, q))) := by
            unfold descendantsAverage
            refine congrArg (fun t => ((descendantsAtDepth (originCube d n) j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (Q := R) a]

theorem coarseBlockMatrix_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
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
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a) X) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) X)) := by
  calc
    (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a) X)
      = (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d n)) a) X) := by
            rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (Q := originCube d n) a]
    _ ≤ descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X)) := by
            exact
              coarseBlockMatrix_subadditive_openCubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
                j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc X
    _ = descendantsAverage (originCube d n) j
          (fun R =>
            (1 / 2 : ℝ) * blockVecDot X
              (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) X)) := by
            unfold descendantsAverage
            refine congrArg (fun t => ((descendantsAtDepth (originCube d n) j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (Q := R) a]

theorem coarseBlockMatrix_upperLeft_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft p) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseBlockMatrix (cubeSet R) a).upperLeft p)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseBlockMatrix_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (p, 0)

theorem coarseBlockMatrix_lowerRight_subadditive_cubeSet_originCube_descendantsAtDepth_of_isSigmaCoarse
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
        (matVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight q) ≤
      descendantsAverage (originCube d n) j
        (fun R =>
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseBlockMatrix (cubeSet R) a).lowerRight q)) := by
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left, vecDot_zero_right] using
    coarseBlockMatrix_subadditive_cubeSet_originCube_descendantsAtDepth_blockQuadratic_of_isSigmaCoarse
      j n a hEll hAQ hSQ hKQ hSigmaQ hdetQ hDesc (0, q)

theorem coarseStarredBlockMatrixInv_cubeSet_eq_openCubeSet_of_triadicCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) :
    coarseStarredBlockMatrixInv (cubeSet Q) a =
      coarseStarredBlockMatrixInv (openCubeSet Q) a := by
  simp [coarseStarredBlockMatrixInv_eq_blockReflect,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) a]

theorem ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using! cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using! openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  calc
    ResponseJ (cubeSet Q) p q a
        = ResponseJ (translateSet z (cubeSet (originCube d Q.scale))) p q a := by
            rw [hcube]
    _ = ResponseJ (cubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) p q (translateCoeffField z a)
    _ = ResponseJ (translateSet z (openCubeSet (originCube d Q.scale))) p q a := by
          symm
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet Q) p q a := by
          rw [hopen]

theorem isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) {a : CoeffField d} {sigmaStar : Mat d} :
    IsSigmaStarCoarse (cubeSet Q) a sigmaStar ↔
      IsSigmaStarCoarse (openCubeSet Q) a sigmaStar := by
  constructor
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro q
    rw [← ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := 0) (q := q) a]
    exact hresp q
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro q
    rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := 0) (q := q) a]
    exact hresp q

theorem isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) {a : CoeffField d} {sigmaStar kappa : Mat d} :
    IsKappaCoarse (cubeSet Q) a sigmaStar kappa ↔
      IsKappaCoarse (openCubeSet Q) a sigmaStar kappa := by
  constructor
  · intro hK p q
    rw [← ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := q) a,
      ← ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := 0) a,
      ← ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := 0) (q := q) a]
    exact hK p q
  · intro hK p q
    rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := q) a,
      ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := 0) a,
      ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := 0) (q := q) a]
    exact hK p q

theorem isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) {a : CoeffField d} {sigma sigmaStar kappa : Mat d} :
    IsSigmaCoarse (cubeSet Q) a sigma sigmaStar kappa ↔
      IsSigmaCoarse (openCubeSet Q) a sigma sigmaStar kappa := by
  constructor
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro p
    rw [← ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := 0) a]
    exact hresp p
  · rintro ⟨hsymm, hresp⟩
    refine ⟨hsymm, ?_⟩
    intro p
    rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (p := p) (q := 0) a]
    exact hresp p

theorem sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet Q) a sigmaStar) :
    sigmaStarInvCoarse (cubeSet Q) a = sigmaStarInvCoarse (openCubeSet Q) a := by
  have hSCube : IsSigmaStarCoarse (cubeSet Q) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := Q)).2 hS
  rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCube,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]

theorem bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet Q) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet Q) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet Q) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    bCoarse (sigmaCoarse (cubeSet Q) a)
        (sigmaStarCoarse (cubeSet Q) a)
        (kappaCoarse (cubeSet Q) a) =
      bCoarse (sigmaCoarse (openCubeSet Q) a)
        (sigmaStarCoarse (openCubeSet Q) a)
        (kappaCoarse (openCubeSet Q) a) := by
  have hSCube : IsSigmaStarCoarse (cubeSet Q) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := Q)).2 hS
  have hKCube : IsKappaCoarse (cubeSet Q) a sigmaStar kappa :=
    (isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := Q)).2 hK
  have hSigmaCube : IsSigmaCoarse (cubeSet Q) a sigma sigmaStar kappa :=
    (isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := Q)).2 hSigma
  rw [sigmaCoarse_eq_of_isSigmaCoarse hSCube hKCube hSigmaCube hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hSCube hdet,
    eq_kappaCoarse_of_isKappaCoarse hSCube hKCube hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet]


end

end Homogenization
