/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.AveragedLocal.ComponentBoundsBasic

/-! # Localized Energy Force -/

@[expose] public section

namespace Homogenization

noncomputable section


theorem coarsePoincareRHSRn_le_intrinsicLocalizedEnergyForce_of_localBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η : ℝ} (n : ℕ)
    {θ CE CF B : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (habs :
      0 < 1 - coarsePoincareRHSAbsorbedRnCoeff η)
    (hθ :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSDiscount s ≤ θ)
    (hEcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedEnergyCoeff η ≤ CE)
    (hFcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedForceCoeff η ≤ CF)
    (hCE_nonneg : 0 ≤ CE) (hCF_nonneg : 0 ≤ CF)
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      θ * coarsePoincareRHSRn Q s u (n + 1) +
        CE *
          (2 * coarsePoincareRHSParentHalfCoeff Q a s n *
            cubeAverage Q (coefficientEnergyDensity a u)) +
        CF * ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 * B) := by
  have hE_nonneg :
      0 ≤ coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n := by
    unfold coarsePoincareRHSIntrinsicEnergyErrorAverage
    exact descendantsAverage_nonneg Q n _ fun R hR => by
      unfold coarsePoincareRHSIntrinsicLocalEnergyError
      exact mul_nonneg
        (mul_nonneg (by norm_num) (coarsePoincareRHSLocalCoeff_nonneg R a hs))
        (havg_nonneg R hR)
  have hbase :=
    coarsePoincareRHSRn_le_intrinsicComponentBounds_of_localBound
      Q a g u s η n habs hθ hEcoeff hFcoeff
      (coarsePoincareRHSRn_nonneg Q s u (n + 1))
      hE_nonneg
      (coarsePoincareRHSIntrinsicForceErrorAverage_nonneg Q a g s n)
      hlocal
  have hE :=
    coarsePoincareRHSIntrinsicEnergyErrorAverage_le_parentHalfCoeff_globalAverage
      (Q := Q) (a := a) (u := u) (s := s) (lam := lam) (Lam := Lam) n
      hs hEll hData hsum_half havg_nonneg hint
  have hF :=
    coarsePoincareRHSIntrinsicForceErrorAverage_le_parentHalfLambda_of_centeredForceAverageBound
      (Q := Q) (a := a) (g := g) (s := s) (lam := lam) (Lam := Lam) n
      hs hEll hData hsum_half hforceAvg
  calc
    coarsePoincareRHSRn Q s u n
        ≤
          θ * coarsePoincareRHSRn Q s u (n + 1) +
            CE * coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n +
            CF * coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := hbase
    _ ≤
          θ * coarsePoincareRHSRn Q s u (n + 1) +
            CE *
              (2 * coarsePoincareRHSParentHalfCoeff Q a s n *
                cubeAverage Q (coefficientEnergyDensity a u)) +
            CF * ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 * B) := by
              exact
                add_le_add
                  (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hCE_nonneg))
                  (mul_le_mul_of_nonneg_left hF hCF_nonneg)

theorem coarsePoincareRHSRn_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η : ℝ} (n : ℕ)
    {θ CE CF B : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (habs :
      0 < 1 - coarsePoincareRHSAbsorbedRnCoeff η)
    (hθ :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSDiscount s ≤ θ)
    (hEcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedEnergyCoeff η ≤ CE)
    (hFcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff η)⁻¹ *
          coarsePoincareRHSAbsorbedForceCoeff η ≤ CF)
    (hCE_nonneg : 0 ≤ CE) (hCF_nonneg : 0 ≤ CF)
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ B)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η) :
    coarsePoincareRHSRn Q s u n ≤
      θ * coarsePoincareRHSRn Q s u (n + 1) +
        CE *
          (2 * coarsePoincareRHSParentHalfCoeff Q a s n *
            cubeAverage Q (coefficientEnergyDensity a u)) +
        CF * ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 * B) := by
  have hforceCentered :
      descendantsAverage Q n
        (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B := by
    rw [descendantsAverage_sq_coarsePoincareRHSLocalCenteredForceSeminorm_eq_of_mem
      Q g s n hmem]
    exact hforceAvg
  exact
    coarsePoincareRHSRn_le_intrinsicLocalizedEnergyForce_of_localBound
      Q a g u n hs hEll hData hsum_half habs hθ hEcoeff hFcoeff
      hCE_nonneg hCF_nonneg havg_nonneg hint hforceCentered hlocal


end

end Homogenization
