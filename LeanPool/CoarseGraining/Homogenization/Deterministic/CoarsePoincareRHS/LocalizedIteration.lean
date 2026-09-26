/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.AveragedLocal

/-! # Localized Iteration -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSRn_iterate_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η θ CE CF : ℝ} (B : ℕ → ℝ)
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
    (hθ_nonneg : 0 ≤ θ)
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
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hforceAvg :
      ∀ n : ℕ,
        descendantsAverage Q n
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ B n)
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
    (m N : ℕ) :
    coarsePoincareRHSRn Q s u m ≤
      θ ^ N * coarsePoincareRHSRn Q s u (m + N) +
        coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N := by
  let E : ℕ → ℝ := fun n =>
    coarsePoincareRHSIntrinsicLocalizedEnergyForceError Q a u s CE CF B n
  have hstep :
      ∀ n : ℕ,
        coarsePoincareRHSRn Q s u n ≤ θ * coarsePoincareRHSRn Q s u (n + 1) + E n := by
    intro n
    have hloc :=
      coarsePoincareRHSRn_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
        Q a g u n hs hEll hData hsum_half habs hθ hEcoeff hFcoeff
        hCE_nonneg hCF_nonneg (havg_nonneg n) hint hmem (hforceAvg n) (hlocal n)
    calc
      coarsePoincareRHSRn Q s u n
          ≤
            θ * coarsePoincareRHSRn Q s u (n + 1) +
              CE *
                (2 * coarsePoincareRHSParentHalfCoeff Q a s n *
                  cubeAverage Q (coefficientEnergyDensity a u)) +
              CF * ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 *
                B n) := hloc
      _ =
            θ * coarsePoincareRHSRn Q s u (n + 1) + E n := by
              simp [E, coarsePoincareRHSIntrinsicLocalizedEnergyForceError]
              ring
  simpa [E, coarsePoincareRHSRn,
    coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum] using
    real_forward_recurrence_iterate_le
      (R := fun n => coarsePoincareRHSRn Q s u n) (E := E)
      hθ_nonneg hstep m N

theorem coarsePoincareRHSSn_iterate_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η θ CE CF : ℝ} (B : ℕ → ℝ)
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
    (hθ_nonneg : 0 ≤ θ)
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
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hforceAvg :
      ∀ n : ℕ,
        descendantsAverage Q n
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ B n)
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
    (m N : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
          coarsePoincareRHSSn Q s u (m + N) +
        coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N := by
  have hR :=
    coarsePoincareRHSRn_iterate_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
      Q a g u B hs hEll hData hsum_half habs hθ_nonneg hθ hEcoeff hFcoeff
      hCE_nonneg hCF_nonneg havg_nonneg hint hmem hforceAvg hlocal m N
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s m := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmul :
      coarsePoincareRHSDepthWeight s m * coarsePoincareRHSRn Q s u m ≤
        coarsePoincareRHSDepthWeight s m *
          (θ ^ N * coarsePoincareRHSRn Q s u (m + N) +
            coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N) := by
    exact mul_le_mul_of_nonneg_left hR hweight_nonneg
  calc
    coarsePoincareRHSSn Q s u m
        = coarsePoincareRHSDepthWeight s m * coarsePoincareRHSRn Q s u m := by
            rfl
    _ ≤
        coarsePoincareRHSDepthWeight s m *
          (θ ^ N * coarsePoincareRHSRn Q s u (m + N) +
            coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N) := hmul
    _ =
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N) +
          coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF B m N := by
          have hterm :
              coarsePoincareRHSDepthWeight s m *
                  (θ ^ N * coarsePoincareRHSRn Q s u (m + N)) =
                (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
                  (coarsePoincareRHSDepthWeight s (m + N) *
                    coarsePoincareRHSRn Q s u (m + N)) := by
              rw [← mul_assoc,
                coarsePoincareRHSDepthWeight_mul_theta_pow_eq_scaledStepCoeff_mul
                  s θ m N]
              ring
          have herr :
              coarsePoincareRHSDepthWeight s m *
                coarsePoincareRHSIntrinsicWeightedLocalizedEnergyForceErrorSum
                  Q a u s θ CE CF B m N =
                coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum
                  Q a u s θ CE CF B m N :=
            coarsePoincareRHSDepthWeight_mul_intrinsicWeightedLocalizedEnergyForceErrorSum_eq
              Q a u s θ CE CF B m N
          rw [mul_add, hterm, herr]
          rfl

theorem coarsePoincareRHSSn_iterate_le_intrinsicLocalizedEnergyForce_of_globalForceBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η θ CE CF : ℝ}
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
    (hθ_nonneg : 0 ≤ θ)
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
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
    (m N : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
          coarsePoincareRHSSn Q s u (m + N) +
        coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF
          (fun n => coarsePoincareRHSGlobalForceBound Q g s n) m N := by
  refine
    coarsePoincareRHSSn_iterate_le_intrinsicLocalizedEnergyForce_of_forceAverageBound
      Q a g u
      (fun n => coarsePoincareRHSGlobalForceBound Q g s n)
      hs hEll hData hsum_half habs hθ_nonneg hθ hEcoeff hFcoeff
      hCE_nonneg hCF_nonneg havg_nonneg hint hmem ?_ hlocal m N
  intro n
  exact
    descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
      Q g s n hGlobalBdd (hLocalBdd n)

theorem coarsePoincareRHSSn_iterate_le_intrinsicGlobalEnergy_add_globalForce
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η θ CE CF : ℝ}
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
    (hθ_nonneg : 0 ≤ θ)
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
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
    (m N : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
          coarsePoincareRHSSn Q s u (m + N) +
        coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
        coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N := by
  calc
    coarsePoincareRHSSn Q s u m ≤
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N) +
          coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum Q a u s θ CE CF
            (fun n => coarsePoincareRHSGlobalForceBound Q g s n) m N :=
      coarsePoincareRHSSn_iterate_le_intrinsicLocalizedEnergyForce_of_globalForceBound
        Q a g u hs hEll hData hsum_half habs hθ_nonneg hθ hEcoeff
        hFcoeff hCE_nonneg hCF_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
        hlocal m N
    _ =
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N) +
          coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
          coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N := by
      rw [coarsePoincareRHSSIntrinsicWeightedLocalizedEnergyForceErrorSum_global_eq_energy_add_force]
      ring


end

end Homogenization
