/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalizedIteration

/-! # Global Iteration -/

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSSn_terminal_tendsto_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    {s θ : ℝ} (m : ℕ)
    (hr_nonneg : 0 ≤ coarsePoincareRHSFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSFiniteSumRatio s θ < 1)
    (hS_bdd :
      BddAbove (Set.range fun n : ℕ => coarsePoincareRHSSn Q s u n)) :
    Filter.Tendsto
      (fun N : ℕ =>
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
          coarsePoincareRHSSn Q s u (m + N))
      Filter.atTop (nhds 0) := by
  have hshift_bdd :
      BddAbove (Set.range fun N : ℕ => coarsePoincareRHSSn Q s u (m + N)) := by
    rcases hS_bdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hB ⟨m + N, rfl⟩
  exact
    tendsto_pow_mul_of_nonneg_bddAbove
      (r := coarsePoincareRHSScaledStepCoeff s θ)
      (F := fun N : ℕ => coarsePoincareRHSSn Q s u (m + N))
      (by simpa [coarsePoincareRHSFiniteSumRatio] using hr_nonneg)
      (by simpa [coarsePoincareRHSFiniteSumRatio] using hr_lt_one)
      (fun N => coarsePoincareRHSSn_nonneg Q s u (m + N))
      hshift_bdd

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergy_add_globalForce_of_terminal_tendsto
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
    (m : ℕ) {E F : ℝ}
    (hterminal :
      Filter.Tendsto
        (fun N : ℕ =>
          (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N))
        Filter.atTop (nhds 0))
    (hEbound :
      ∀ N : ℕ, coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N ≤ E)
    (hFbound :
      ∀ N : ℕ,
        coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N ≤ F) :
    coarsePoincareRHSSn Q s u m ≤ E + F := by
  refine real_le_of_forall_le_add_of_tendsto_zero hterminal ?_
  intro N
  have hiter :=
    coarsePoincareRHSSn_iterate_le_intrinsicGlobalEnergy_add_globalForce
      Q a g u hs hEll hData hsum_half habs hθ_nonneg hθ hEcoeff
      hFcoeff hCE_nonneg hCF_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hlocal m N
  have hsum :
      coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
          coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N ≤
        E + F :=
    add_le_add (hEbound N) (hFbound N)
  calc
    coarsePoincareRHSSn Q s u m
        ≤
          (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
              coarsePoincareRHSSn Q s u (m + N) +
            coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
            coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N :=
        hiter
    _ =
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N) +
          (coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N +
            coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N) := by
        ring
    _ ≤
        (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
            coarsePoincareRHSSn Q s u (m + N) +
          (E + F) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hsum
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ N *
              coarsePoincareRHSSn Q s u (m + N))

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteStep_of_bddAbove
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam η CE CF : ℝ}
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
          coarsePoincareRHSDiscount s ≤ coarsePoincareRHSNoteStepCoeff s)
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
    (hS_bdd :
      BddAbove (Set.range fun n : ℕ => coarsePoincareRHSSn Q s u n))
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s η)
    (m : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m *
          (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ +
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m *
          (1 - Real.rpow (3 : ℝ) (-(3 * s / 2)))⁻¹ := by
  have hgeom :=
    coarsePoincareRHSSn_le_intrinsicGlobalEnergy_add_globalForce_of_terminal_tendsto
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam) (η := η)
      (θ := coarsePoincareRHSNoteStepCoeff s) (CE := CE) (CF := CF)
      hs hEll hData hsum_half habs
      (coarsePoincareRHSNoteStepCoeff_nonneg s) hθ hEcoeff hFcoeff
      hCE_nonneg hCF_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd hlocal
      (m := m)
      (E := coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m *
        (1 - coarsePoincareRHSFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s))⁻¹)
      (F := coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m *
        (1 - coarsePoincareRHSForceFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s))⁻¹)
      (coarsePoincareRHSSn_terminal_tendsto_of_bddAbove
        Q u m
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_nonneg s)
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_lt_one hs)
        hS_bdd)
      ?_ ?_
  · rw [coarsePoincareRHSFiniteSumRatio_noteStepCoeff_eq s,
      coarsePoincareRHSForceFiniteSumRatio_noteStepCoeff_eq s] at hgeom
    exact hgeom
  · intro N
    exact
      coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_le_base_mul_inv_one_sub_of_nonneg
        Q a u m N hs hCE_nonneg (havg_nonneg 0 Q (by simp))
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_nonneg s)
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_lt_one hs)
  · intro N
    have hfr_nonneg :
        0 ≤ coarsePoincareRHSForceFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) :=
      coarsePoincareRHSForceFiniteSumRatio_nonneg_of_finiteSumRatio_nonneg
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_nonneg s)
    have hfr_lt_one :
        coarsePoincareRHSForceFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) < 1 :=
      coarsePoincareRHSForceFiniteSumRatio_lt_one_of_finiteSumRatio_lt_one
        hs (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_nonneg s)
        (coarsePoincareRHSFiniteSumRatio_noteStepCoeff_lt_one hs)
    exact
      coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_le_base_mul_inv_one_sub_of_nonneg
        Q a g m N hCF_nonneg hfr_nonneg hfr_lt_one

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
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
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
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
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s))
    (m : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 m * (5 * s⁻¹) +
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m *
          (5 * s⁻¹) := by
  have hEcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s))⁻¹ *
          coarsePoincareRHSAbsorbedEnergyCoeff (coarsePoincareRHSNoteEta s) ≤ 5 := by
    simpa [coarsePoincareRHSNoteEnergyEnvelope] using
      coarsePoincareRHSNoteEnergyEnvelope_le_five hs (by linarith : s ≤ 2)
  have hFcoeff :
      (1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s))⁻¹ *
          coarsePoincareRHSAbsorbedForceCoeff (coarsePoincareRHSNoteEta s) ≤
        120 * s⁻¹ := by
    simpa [coarsePoincareRHSNoteForceEnvelope] using
      coarsePoincareRHSNoteForceEnvelope_le_oneTwenty_mul_inv hs hs_le
  have hCF_nonneg : 0 ≤ 120 * s⁻¹ := by positivity
  have hraw :=
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteStep_of_bddAbove
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      (η := coarsePoincareRHSNoteEta s) (CE := 5) (CF := 120 * s⁻¹)
      hs hEll hData hsum_half
      (one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_pos hs)
      (coarsePoincareRHS_noteEta_discount_le_noteStepCoeff hs)
      hEcoeff hFcoeff (by norm_num : 0 ≤ (5 : ℝ)) hCF_nonneg
      havg_nonneg hint hmem hGlobalBdd hLocalBdd
      (coarsePoincareRHSSn_bddAbove_of_memLp Q hs u hu) hlocal m
  have hEbase_nonneg :
      0 ≤ coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 m :=
    coarsePoincareRHSSIntrinsicGlobalEnergyBase_nonneg
      Q a u hs (by norm_num) (havg_nonneg 0 Q (by simp)) m
  have hFbase_nonneg :
      0 ≤ coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m :=
    coarsePoincareRHSSIntrinsicGlobalForceBase_nonneg Q a g s hCF_nonneg m
  have hEfac :
      (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ ≤ 5 * s⁻¹ :=
    inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le
  have hFfac :
      (1 - Real.rpow (3 : ℝ) (-(3 * s / 2)))⁻¹ ≤ 5 * s⁻¹ :=
    inv_one_sub_rpow_three_neg_three_half_le_five_inv hs hs_le
  calc
    coarsePoincareRHSSn Q s u m
        ≤
          coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 m *
              (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ +
            coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m *
              (1 - Real.rpow (3 : ℝ) (-(3 * s / 2)))⁻¹ := hraw
    _ ≤
          coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 m * (5 * s⁻¹) +
            coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m *
              (5 * s⁻¹) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hEfac hEbase_nonneg)
              (mul_le_mul_of_nonneg_left hFfac hFbase_nonneg)


end

end Homogenization
