/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometric

/-! # Coefficient Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem thetaRatio_eq_div {d : ℕ} (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d) :
    ThetaRatio Q s t a = LambdaSq Q s (.finite 1) a / lambdaSq Q t (.finite 1) a := rfl

@[simp] theorem homogenizationError_finite_eq {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent) (q : ℝ)
    (a : CoeffField d) (a0 : Mat d) :
    HomogenizationError Q n s p (.finite q) a a0 =
      HomogenizationErrorFinite Q n s p q a a0 := rfl

@[simp] theorem homogenizationError_infinity_eq {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent)
    (a : CoeffField d) (a0 : Mat d) :
    HomogenizationError Q n s p .infinity a a0 =
      HomogenizationErrorInfinity Q n s p a a0 := rfl

theorem homogenizationErrorOnCube_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : MultiscaleExponent)
    (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s p q a a0 =
      HomogenizationError Q Q.scale s p q a a0 := rfl

@[simp] theorem multiscale_ellipticity_LambdaSq_one_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    LambdaSq Q s (.finite 1) a = LambdaSqFinite Q s 1 a := by
  simp

@[simp] theorem multiscale_ellipticity_lambdaSq_one_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    lambdaSq Q s (.finite 1) a = lambdaSqFinite Q s 1 a := by
  simp

@[simp] theorem multiscale_ellipticity_LambdaSqFinite_one_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    LambdaSqFinite Q s 1 a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2))
        2 := by
  unfold LambdaSqFinite
  norm_num

@[simp] theorem multiscale_ellipticity_lambdaSqFinite_one_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    lambdaSqFinite Q s 1 a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2))
        (-2) := by
  unfold lambdaSqFinite
  norm_num

@[simp] theorem multiscale_ellipticity_LambdaSq_one_formula {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    LambdaSq Q s (.finite 1) a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2))
        2 := by
  rw [multiscale_ellipticity_LambdaSq_one_eq, multiscale_ellipticity_LambdaSqFinite_one_eq]

@[simp] theorem multiscale_ellipticity_lambdaSq_one_formula {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) :
    lambdaSq Q s (.finite 1) a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2))
        (-2) := by
  rw [multiscale_ellipticity_lambdaSq_one_eq, multiscale_ellipticity_lambdaSqFinite_one_eq]

@[simp] theorem thetaRatio_eq_div_finite_one {d : ℕ}
    (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d) :
    ThetaRatio Q s t a = LambdaSqFinite Q s 1 a / lambdaSqFinite Q t 1 a := by
  simp [thetaRatio_eq_div]

@[simp] theorem homogenizationError_infinity_one_eq {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationError Q n s .infinity (.finite 1) a a0 =
      HomogenizationErrorFinite Q n s .infinity 1 a a0 := by
  simp

@[simp] theorem homogenizationErrorFinite_infinity_one_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorFinite Q n s .infinity 1 a a0 =
      ∑' l : ℕ, geometricWeight s 1 l * scaleResponseAtScale Q (n - (l : ℤ)) .infinity a a0 := by
  unfold HomogenizationErrorFinite
  simp [Real.rpow_one]

@[simp] theorem homogenizationErrorFinite_infinity_one_formula {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorFinite Q n s .infinity 1 a a0 =
      ∑' l : ℕ,
        geometricWeight s 1 l *
          Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q (n - (l : ℤ)) a a0) (1 / 2) := by
  rw [homogenizationErrorFinite_infinity_one_eq_tsum]
  simp

@[simp] theorem homogenizationErrorOnCube_infinity_one_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 =
      HomogenizationErrorFinite Q Q.scale s .infinity 1 a a0 := by
  simp [homogenizationErrorOnCube_eq]

@[simp] theorem homogenizationErrorOnCube_infinity_one_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 =
      ∑' l : ℕ, geometricWeight s 1 l * scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq, homogenizationErrorFinite_infinity_one_eq_tsum]

@[simp] theorem homogenizationErrorOnCube_infinity_one_formula {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 =
      ∑' l : ℕ,
        geometricWeight s 1 l *
          Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0)
            (1 / 2) := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  simp

theorem coarseBBlockNorm_nonneg {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) :
    0 ≤ coarseBBlockNorm Q a := by
  unfold coarseBBlockNorm
  exact matNorm_nonneg _

theorem coarseSigmaStarInvBlockNorm_nonneg {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) :
    0 ≤ coarseSigmaStarInvBlockNorm Q a := by
  unfold coarseSigmaStarInvBlockNorm
  exact matNorm_nonneg _

theorem coarseBBlockNorm_le_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    coarseBBlockNorm Q a ≤ maxDescendantBBlockNormAtScale Q k a := by
  let j : ℕ := Int.toNat (Q.scale - k)
  have hQQ : Q ∈ descendantsAtScale Q Q.scale := by
    simp [descendantsAtScale_self]
  rcases hData Q.scale le_rfl Q hQQ with
    ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  have hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    exact hData k hk R hRk
  have hcanonQ :
      bCoarse sigmaQ sigmaStarQ kappaQ =
        bCoarse (sigmaCoarse (cubeSet Q) a)
          (sigmaStarCoarse (cubeSet Q) a)
          (kappaCoarse (cubeSet Q) a) := by
    calc
      bCoarse sigmaQ sigmaStarQ kappaQ =
          bCoarse (sigmaCoarse (openCubeSet Q) a)
            (sigmaStarCoarse (openCubeSet Q) a)
            (kappaCoarse (openCubeSet Q) a) := by
              rw [sigmaCoarse_eq_of_isSigmaCoarse hSQ hKQ hSigmaQ hdetQ,
                eq_sigmaStarCoarse_of_isSigmaStarCoarse hSQ hdetQ,
                eq_kappaCoarse_of_isKappaCoarse hSQ hKQ hdetQ]
      _ =
          bCoarse (sigmaCoarse (cubeSet Q) a)
            (sigmaStarCoarse (cubeSet Q) a)
            (kappaCoarse (cubeSet Q) a) := by
              symm
              rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
                (Q := Q) (a := a) hSQ hKQ hSigmaQ hdetQ]
  have hAvgEq :
      descendantsAverageMat Q j
        (fun R =>
          bCoarse (sigmaCoarse (openCubeSet R) a)
            (sigmaStarCoarse (openCubeSet R) a)
            (kappaCoarse (openCubeSet R) a)) =
        descendantsAverageMat Q j
          (fun R =>
            bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a)) := by
    ext i l
    unfold descendantsAverageMat descendantsAverage
    refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        bCoarse (sigmaCoarse (openCubeSet R) a)
            (sigmaStarCoarse (openCubeSet R) a)
            (kappaCoarse (openCubeSet R) a) =
          bCoarse (sigmaCoarse (cubeSet R) a)
            (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a) := by
      symm
      rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
        (Q := R) (a := a) hSR hKR hSigmaR hdetR]
    simpa using congrArg (fun M : Mat d => M i l) hcanonR
  have hLoewner :
      MatLoewnerLE
        (bCoarse (sigmaCoarse (cubeSet Q) a)
          (sigmaStarCoarse (cubeSet Q) a)
          (kappaCoarse (cubeSet Q) a))
        (descendantsAverageMat Q j
          (fun R =>
            bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a))) := by
    intro p
    calc
      (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (bCoarse (sigmaCoarse (cubeSet Q) a)
              (sigmaStarCoarse (cubeSet Q) a)
              (kappaCoarse (cubeSet Q) a)) p) =
        (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (bCoarse (sigmaCoarse (openCubeSet Q) a)
              (sigmaStarCoarse (openCubeSet Q) a)
              (kappaCoarse (openCubeSet Q) a)) p) := by
            rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
              (Q := Q) (a := a) hSQ hKQ hSigmaQ hdetQ]
      _ ≤ (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (descendantsAverageMat Q j
                (fun R =>
                  bCoarse (sigmaCoarse (openCubeSet R) a)
                    (sigmaStarCoarse (openCubeSet R) a)
                    (kappaCoarse (openCubeSet R) a))) p) := by
              exact
                bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
                  j Q a hEll hSQ hKQ hSigmaQ hdetQ hDesc p
      _ = (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (descendantsAverageMat Q j
                (fun R =>
                  bCoarse (sigmaCoarse (cubeSet R) a)
                    (sigmaStarCoarse (cubeSet R) a)
                    (kappaCoarse (cubeSet R) a))) p) := by
              rw [hAvgEq]
  have hParentPSD :
      (bCoarse (sigmaCoarse (cubeSet Q) a)
        (sigmaStarCoarse (cubeSet Q) a)
        (kappaCoarse (cubeSet Q) a)).PosSemidef := by
    rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
      (Q := Q) (a := a) hSQ hKQ hSigmaQ hdetQ]
    exact bCoarse_canonical_posSemidef_of_isSigmaCoarse hSQ hKQ hSigmaQ hdetQ
  have hAvgPSD :
      (descendantsAverageMat Q j
        (fun R =>
          bCoarse (sigmaCoarse (cubeSet R) a)
            (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a))).PosSemidef := by
    refine descendantsAverageMat_posSemidef ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        bCoarse sigmaR sigmaStarR kappaR =
          bCoarse (sigmaCoarse (cubeSet R) a)
            (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a) := by
      calc
        bCoarse sigmaR sigmaStarR kappaR =
            bCoarse (sigmaCoarse (openCubeSet R) a)
              (sigmaStarCoarse (openCubeSet R) a)
              (kappaCoarse (openCubeSet R) a) := by
                rw [sigmaCoarse_eq_of_isSigmaCoarse hSR hKR hSigmaR hdetR,
                  eq_sigmaStarCoarse_of_isSigmaStarCoarse hSR hdetR,
                  eq_kappaCoarse_of_isKappaCoarse hSR hKR hdetR]
        _ =
            bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a) := by
                symm
                rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
                  (Q := R) (a := a) hSR hKR hSigmaR hdetR]
    rw [← hcanonR]
    exact bCoarse_posSemidef_of_isSigmaCoarse hSR hSigmaR
  have hParentEq :
      coarseBBlockNorm Q a =
        matNorm
          (bCoarse (sigmaCoarse (cubeSet Q) a)
            (sigmaStarCoarse (cubeSet Q) a)
            (kappaCoarse (cubeSet Q) a)) := by
    unfold coarseBBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a,
      coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hAQ hSQ hKQ hSigmaQ hdetQ,
      hcanonQ]
  have hterm_eq :
      ∀ R ∈ descendantsAtDepth Q j,
        matNorm
            (bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a)) =
          coarseBBlockNorm R a := by
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        bCoarse sigmaR sigmaStarR kappaR =
          bCoarse (sigmaCoarse (cubeSet R) a)
            (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a) := by
      calc
        bCoarse sigmaR sigmaStarR kappaR =
            bCoarse (sigmaCoarse (openCubeSet R) a)
              (sigmaStarCoarse (openCubeSet R) a)
              (kappaCoarse (openCubeSet R) a) := by
                rw [sigmaCoarse_eq_of_isSigmaCoarse hSR hKR hSigmaR hdetR,
                  eq_sigmaStarCoarse_of_isSigmaStarCoarse hSR hdetR,
                  eq_kappaCoarse_of_isKappaCoarse hSR hKR hdetR]
        _ =
            bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a) := by
                symm
                rw [bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
                  (Q := R) (a := a) hSR hKR hSigmaR hdetR]
    unfold coarseBBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hAR hSR hKR hSigmaR hdetR,
      hcanonR]
  have himage :
      (fun R =>
          matNorm
            (bCoarse (sigmaCoarse (cubeSet R) a)
              (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a))) ''
        (↑(descendantsAtDepth Q j) : Set (TriadicCube d)) =
        (fun R => coarseBBlockNorm R a) '' (↑(descendantsAtDepth Q j) : Set (TriadicCube d)) := by
    ext x
    constructor
    · rintro ⟨R, hR, rfl⟩
      exact ⟨R, hR, (hterm_eq R hR).symm⟩
    · rintro ⟨R, hR, rfl⟩
      exact ⟨R, hR, hterm_eq R hR⟩
  calc
    coarseBBlockNorm Q a =
        matNorm
          (bCoarse (sigmaCoarse (cubeSet Q) a)
            (sigmaStarCoarse (cubeSet Q) a)
            (kappaCoarse (cubeSet Q) a)) := hParentEq
    _ ≤
        matNorm
          (descendantsAverageMat Q j
            (fun R =>
              bCoarse (sigmaCoarse (cubeSet R) a)
                (sigmaStarCoarse (cubeSet R) a)
                (kappaCoarse (cubeSet R) a))) := by
          exact matNorm_le_of_matLoewnerLE_of_posSemidef hParentPSD hAvgPSD hLoewner
    _ ≤ finsetSsup (descendantsAtDepth Q j)
          (fun R =>
            matNorm
              (bCoarse (sigmaCoarse (cubeSet R) a)
                (sigmaStarCoarse (cubeSet R) a)
                (kappaCoarse (cubeSet R) a))) := by
          exact matNorm_descendantsAverageMat_le_finsetSsup_matNorm Q j
            (fun R =>
              bCoarse (sigmaCoarse (cubeSet R) a)
                (sigmaStarCoarse (cubeSet R) a)
                (kappaCoarse (cubeSet R) a))
    _ = finsetSsup (descendantsAtDepth Q j) (fun R => coarseBBlockNorm R a) := by
          unfold finsetSsup
          rw [himage]
    _ = maxDescendantBBlockNormAtScale Q k a := by
          unfold maxDescendantBBlockNormAtScale
          rw [descendantsAtScale_eq_descendantsAtDepth Q hk]

theorem coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    coarseSigmaStarInvBlockNorm Q a ≤
      maxDescendantSigmaStarInvNormAtScale Q k a := by
  let j : ℕ := Int.toNat (Q.scale - k)
  have hQQ : Q ∈ descendantsAtScale Q Q.scale := by
    simp [descendantsAtScale_self]
  rcases hData Q.scale le_rfl Q hQQ with
    ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  have hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    exact hData k hk R hRk
  have hAvgEq :
      descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (openCubeSet R) a) =
        descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (cubeSet R) a) := by
    ext i l
    unfold descendantsAverageMat descendantsAverage
    refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        sigmaStarInvCoarse (openCubeSet R) a = sigmaStarInvCoarse (cubeSet R) a := by
      symm
      rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
        (Q := R) (a := a) hSR]
    simpa using congrArg (fun M : Mat d => M i l) hcanonR
  have hLoewner :
      MatLoewnerLE (sigmaStarInvCoarse (cubeSet Q) a)
        (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (cubeSet R) a)) := by
    intro q
    calc
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (cubeSet Q) a) q) =
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) := by
            rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
              (Q := Q) (a := a) hSQ]
      _ ≤ (1 / 2 : ℝ) * vecDot q
            (matVecMul (descendantsAverageMat Q j
              (fun R => sigmaStarInvCoarse (openCubeSet R) a)) q) := by
              exact
                sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
                  j Q a hEll hSQ hKQ hSigmaQ hdetQ hDesc q
      _ = (1 / 2 : ℝ) * vecDot q
            (matVecMul (descendantsAverageMat Q j
              (fun R => sigmaStarInvCoarse (cubeSet R) a)) q) := by
              rw [hAvgEq]
  have hParentPSD : (sigmaStarInvCoarse (cubeSet Q) a).PosSemidef := by
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := Q) (a := a) hSQ]
    exact sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := openCubeSet Q) (a := a) hSQ
  have hAvgPSD :
      (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (cubeSet R) a)).PosSemidef := by
    refine descendantsAverageMat_posSemidef ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := R) (a := a) hSR]
    exact sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := openCubeSet R) (a := a) hSR
  have hcanonQsig : sigmaStarQ⁻¹ = sigmaStarInvCoarse (cubeSet Q) a := by
    calc
      sigmaStarQ⁻¹ = sigmaStarInvCoarse (openCubeSet Q) a := by
        symm
        rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSQ]
      _ = sigmaStarInvCoarse (cubeSet Q) a := by
        symm
        rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
          (Q := Q) (a := a) hSQ]
  have hParentEq :
      coarseSigmaStarInvBlockNorm Q a = matNorm (sigmaStarInvCoarse (cubeSet Q) a) := by
    unfold coarseSigmaStarInvBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a,
      coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix hAQ hSQ hKQ hSigmaQ hdetQ,
      hcanonQsig]
  have hterm_eq :
      ∀ R ∈ descendantsAtDepth Q j,
        matNorm (sigmaStarInvCoarse (cubeSet R) a) = coarseSigmaStarInvBlockNorm R a := by
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonRsig : sigmaStarR⁻¹ = sigmaStarInvCoarse (cubeSet R) a := by
      calc
        sigmaStarR⁻¹ = sigmaStarInvCoarse (openCubeSet R) a := by
          symm
          rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSR]
        _ = sigmaStarInvCoarse (cubeSet R) a := by
          symm
          rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
            (Q := R) (a := a) hSR]
    unfold coarseSigmaStarInvBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix hAR hSR hKR hSigmaR hdetR,
      hcanonRsig]
  have himage :
      (fun R => matNorm (sigmaStarInvCoarse (cubeSet R) a)) ''
        (↑(descendantsAtDepth Q j) : Set (TriadicCube d)) =
        (fun R => coarseSigmaStarInvBlockNorm R a) '' (↑(descendantsAtDepth Q j) : Set (TriadicCube d)) := by
    ext x
    constructor
    · rintro ⟨R, hR, rfl⟩
      exact ⟨R, hR, (hterm_eq R hR).symm⟩
    · rintro ⟨R, hR, rfl⟩
      exact ⟨R, hR, hterm_eq R hR⟩
  calc
    coarseSigmaStarInvBlockNorm Q a = matNorm (sigmaStarInvCoarse (cubeSet Q) a) := hParentEq
    _ ≤ matNorm (descendantsAverageMat Q j (fun R => sigmaStarInvCoarse (cubeSet R) a)) := by
          exact matNorm_le_of_matLoewnerLE_of_posSemidef hParentPSD hAvgPSD hLoewner
    _ ≤ finsetSsup (descendantsAtDepth Q j) (fun R => matNorm (sigmaStarInvCoarse (cubeSet R) a)) := by
          exact matNorm_descendantsAverageMat_le_finsetSsup_matNorm Q j
            (fun R => sigmaStarInvCoarse (cubeSet R) a)
    _ = finsetSsup (descendantsAtDepth Q j) (fun R => coarseSigmaStarInvBlockNorm R a) := by
          unfold finsetSsup
          rw [himage]
    _ = maxDescendantSigmaStarInvNormAtScale Q k a := by
          unfold maxDescendantSigmaStarInvNormAtScale
          rw [descendantsAtScale_eq_descendantsAtDepth Q hk]

@[simp] theorem maxDescendantBBlockNormAtScale_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) :
    maxDescendantBBlockNormAtScale Q Q.scale a = coarseBBlockNorm Q a := by
  unfold maxDescendantBBlockNormAtScale finsetSsup
  rw [descendantsAtScale_self]
  have himage :
      ((fun R => coarseBBlockNorm R a) '' (↑({Q} : Finset (TriadicCube d)) : Set (TriadicCube d))) =
        ({coarseBBlockNorm Q a} : Set ℝ) := by
    ext x
    simp
  rw [himage]
  simp

@[simp] theorem maxDescendantNormalizedBlockResponseAtScale_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q Q.scale a a0 =
      normalizedBlockResponseMax Q a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale
  rw [descendantsAtScale_self]
  simp

@[simp] theorem scaleResponseAtScale_finite_self_eq {d : ℕ}
    (Q : TriadicCube d) (p : ℝ) (a : CoeffField d) (a0 : Mat d) :
    scaleResponseAtScale Q Q.scale (.finite p) a a0 =
      Real.rpow (Real.rpow (normalizedBlockResponseMax Q a a0) (p / 2)) (1 / p) := by
  rw [scaleResponseAtScale_finite_eq]
  rw [descendantsAtScale_self, finsetAverage_singleton]

@[simp] theorem scaleResponseAtScale_infinity_self_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) :
    scaleResponseAtScale Q Q.scale .infinity a a0 =
      Real.rpow (normalizedBlockResponseMax Q a a0) (1 / 2) := by
  rw [scaleResponseAtScale_infinity_eq, maxDescendantNormalizedBlockResponseAtScale_self]

@[simp] theorem maxDescendantSigmaStarInvNormAtScale_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) :
    maxDescendantSigmaStarInvNormAtScale Q Q.scale a = coarseSigmaStarInvBlockNorm Q a := by
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  rw [descendantsAtScale_self]
  have himage :
      ((fun R => coarseSigmaStarInvBlockNorm R a) '' (↑({Q} : Finset (TriadicCube d)) : Set (TriadicCube d))) =
        ({coarseSigmaStarInvBlockNorm Q a} : Set ℝ) := by
    ext x
    simp
  rw [himage]
  simp

theorem coarseBBlockNorm_le_maxDescendantBBlockNormAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) :
    coarseBBlockNorm R a ≤ maxDescendantBBlockNormAtScale Q k a := by
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hBdd :
      BddAbove ((fun S => coarseBBlockNorm S a) '' (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun S => coarseBBlockNorm S a)).bddAbove
  exact le_csSup hBdd ⟨R, hR, rfl⟩

theorem coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) :
    coarseSigmaStarInvBlockNorm R a ≤ maxDescendantSigmaStarInvNormAtScale Q k a := by
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hBdd :
      BddAbove
        ((fun S => coarseSigmaStarInvBlockNorm S a) '' (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun S => coarseSigmaStarInvBlockNorm S a)).bddAbove
  exact le_csSup hBdd ⟨R, hR, rfl⟩


end

end Homogenization
