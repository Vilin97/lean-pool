/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.StarredSubadditivity

/-! # Subadditivity -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Origin-cube elliptic recovery -- subadditivity wrappers

These wrappers package the descendant deterministic-coarse-data burden behind
either `OpenCubeDescendantDeterministicCoarseData` or the stronger recovery-
family hypothesis. This is the note-facing surface downstream Chapter-3
consumers should use, rather than unpacking the individual coarse witnesses by
hand.
-/

private theorem descendantWitnesses_of_deterministicCoarseData
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) (j : ℕ) :
    ∀ R ∈ descendantsAtDepth Q j,
      ∃ sigmaR sigmaStarR kappaR,
        IsCoarseBlockMatrix (openCubeSet R) a
          (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
        IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
        IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
        IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
        IsUnit sigmaStarR.det := by
  intro R hR
  have hk : Q.scale - (j : ℤ) ≤ Q.scale := by
    omega
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
    rw [mem_descendantsAtScale_iff hk]
    have hcast :
        Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
      rw [show Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) by omega]
      simp
    simpa [hcast] using hR
  exact hData (Q.scale - (j : ℤ)) hk R hRscale

/-- Subadditivity of the coarse block matrix in Loewner order, packaged from
deterministic coarse data on all descendants. -/
theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    BlockMatLoewnerLE (coarseBlockMatrix (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) := by
  rcases hData.self with ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  exact
    coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ
      (descendantWitnesses_of_deterministicCoarseData hData j)

/-- Subadditivity of the inverse starred block matrix in Loewner order,
packaged from deterministic coarse data on all descendants. -/
theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    BlockMatLoewnerLE (coarseStarredBlockMatrixInv (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) := by
  rcases hData.self with ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  exact
    coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
      j Q a hEll hAQ hSQ hKQ hSigmaQ hdetQ
      (descendantWitnesses_of_deterministicCoarseData hData j)

/-- Subadditivity of `σ_*^{-1}` in Loewner order, packaged from deterministic
coarse data on all descendants. -/
theorem sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    MatLoewnerLE (sigmaStarInvCoarse (openCubeSet Q) a)
      (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (openCubeSet R) a)) := by
  rcases hData.self with ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  exact
    sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
      j Q a hEll hSQ hKQ hSigmaQ hdetQ
      (descendantWitnesses_of_deterministicCoarseData hData j)

/-- Subadditivity of the canonical `b`-matrix in Loewner order, packaged from
deterministic coarse data on all descendants. -/
theorem bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse (openCubeSet Q) a)
        (sigmaStarCoarse (openCubeSet Q) a)
        (kappaCoarse (openCubeSet Q) a))
      (descendantsAverageMat Q j
        (fun R =>
          bCoarse (sigmaCoarse (openCubeSet R) a)
            (sigmaStarCoarse (openCubeSet R) a)
            (kappaCoarse (openCubeSet R) a))) := by
  rcases hData.self with ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  exact
    bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
      j Q a hEll hSQ hKQ hSigmaQ hdetQ
      (descendantWitnesses_of_deterministicCoarseData hData j)

/-- Recovery-family wrapper for coarse-block-matrix subadditivity in Loewner
order. -/
theorem coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_recoveryFamily
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    BlockMatLoewnerLE (coarseBlockMatrix (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) :=
  coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    j Q a hEll (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

/-- Recovery-family wrapper for inverse-starred-block-matrix subadditivity in
Loewner order. -/
theorem coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_recoveryFamily
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    BlockMatLoewnerLE (coarseStarredBlockMatrixInv (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseStarredBlockMatrixInv (openCubeSet R) a)) :=
  coarseStarredBlockMatrixInv_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    j Q a hEll (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

/-- Recovery-family wrapper for `σ_*^{-1}` subadditivity in Loewner order. -/
theorem sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_recoveryFamily
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    MatLoewnerLE (sigmaStarInvCoarse (openCubeSet Q) a)
      (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (openCubeSet R) a)) :=
  sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    j Q a hEll (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

/-- Recovery-family wrapper for canonical `b`-matrix subadditivity in Loewner
order. -/
theorem bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_recoveryFamily
    {d : ℕ} [NeZero d] (j : ℕ) (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    MatLoewnerLE
      (bCoarse (sigmaCoarse (openCubeSet Q) a)
        (sigmaStarCoarse (openCubeSet Q) a)
        (kappaCoarse (openCubeSet Q) a))
      (descendantsAverageMat Q j
        (fun R =>
          bCoarse (sigmaCoarse (openCubeSet R) a)
            (sigmaStarCoarse (openCubeSet R) a)
            (kappaCoarse (openCubeSet R) a))) :=
  bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_deterministicCoarseData
    j Q a hEll (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

end

end Homogenization
