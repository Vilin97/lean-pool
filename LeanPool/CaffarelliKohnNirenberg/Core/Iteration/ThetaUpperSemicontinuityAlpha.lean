/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuityBasic

/-!
# Theta Upper Semicontinuity Alpha

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- The time-slice energy restricted to the ball of radius `r` stays bounded
above near the base point, uniformly along the one-sided time parameter used in
the Step 2 transfer argument. -/
lemma theta_usc_timeSliceEnergy_bounded
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {R r h₁ : ℝ}
    (hR : 0 < R) (hrrR : r < R) (hh₁ : 0 < h₁) (hh₁R : h₁ < R ^ 2)
    (hsubAt : ∀ {h : ℝ}, 0 ≤ h → h ≤ h₁ →
      closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I)
    (hIntAt : ∀ {h : ℝ}, 0 < h → h ≤ h₁ →
      ∀ᵐ s ∂volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
        IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 r) volume ∧
        IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 R) volume)
    (hS0 : essSup (timeSliceBallEnergy z₀.1 R ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≠ ⊤) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
      (fun h => (essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball z₀.1 r,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))).toReal) := by
  let Sf : ℝ≥0∞ := essSup (timeSliceBallEnergy z₀.1 R ·
      (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)))
  have hSf : Sf ≠ ⊤ := by
    have hsubf : closure (parabolicCylinder z₀.1 (z₀.2 + h₁) R) ⊆
        spaceTimeSet Ω I := hsubAt (h := h₁) hh₁.le le_rfl
    have hrectf : euclideanClosedBall z₀.1 R ×ˢ
        Icc (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁) ⊆ spaceTimeSet Ω I := by
      intro w hw
      apply hsubf
      rw [closure_parabolicCylinder hR]
      have heq := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).1 hw.1
      have heq' : vec3EuclideanNorm (w.1 - z₀.1) ≤ R := by
        have hnorm : vecEuclideanNorm (w.1 - z₀.1) =
            vec3EuclideanNorm (w.1 - z₀.1) := by
          simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot]
          apply congrArg Real.sqrt
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [← hnorm]
        exact heq
      exact ⟨heq', hw.2⟩
    exact ne_of_lt (sws_timeSliceBallEnergy_essSup_lt_top hsol hR
      (by nlinarith only [hR]) hrectf)
  let B : ℝ := max
    (essSup (timeSliceBallEnergy z₀.1 R ·
      (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal Sf.toReal
  refine isBoundedUnder_of_eventually_le (a := B) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hh₁).filter_mono nhdsWithin_le_nhds] with h hh hsmall
  have hhpos : 0 < h := by simpa only [mem_Ioi] using hh
  have hInt := hIntAt hhpos (le_of_lt hsmall)
  have hsplit : Ioc (z₀.2 - R ^ 2) (z₀.2 + h) =
        Ioc (z₀.2 - R ^ 2) z₀.2 ∪ Ioc z₀.2 (z₀.2 + h) := by
      ext s
      constructor
      · intro hs
        by_cases hleft : s ≤ z₀.2
        · exact Or.inl ⟨hs.1, hleft⟩
        · exact Or.inr ⟨lt_of_not_ge hleft, hs.2⟩
      · rintro (hs | hs)
        · exact ⟨hs.1, le_trans hs.2 (by linarith only [hhpos.le])⟩
        · exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
  have hOldSub : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆
        Ioc (z₀.2 - R ^ 2) (z₀.2 + h) := by
      intro s hs
      exact ⟨hs.1, by linarith only [hs.2, hhpos.le]⟩
  have hFutureSub : Ioc z₀.2 (z₀.2 + h) ⊆
        Ioc (z₀.2 - R ^ 2) (z₀.2 + h) := by
      intro s hs
      exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
  have hIntOld := ae_restrict_of_ae_restrict_of_subset hOldSub hInt
  have hIntFuture := ae_restrict_of_ae_restrict_of_subset hFutureSub hInt
  have hAE : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
        ENNReal.ofReal (∫ y in vec3Ball z₀.1 r,
          (vec3EuclideanNorm (u (y, s))) ^ 2) ≤ ENNReal.ofReal B := by
      rw [hsplit, ae_restrict_union_iff]
      constructor
      · have hBae : ∀ᵐ s ∂volume.restrict
            (Ioc (z₀.2 - R ^ 2) z₀.2),
            timeSliceBallEnergy z₀.1 R s
              (fun w => vec3EuclideanNorm (u w)) ≤
              essSup (timeSliceBallEnergy z₀.1 R ·
                (fun w => vec3EuclideanNorm (u w)))
                (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) :=
          ae_le_essSup
        filter_upwards [hIntOld, hBae] with s hs hB
        have hsub : vec3Ball z₀.1 r ⊆ vec3Ball z₀.1 R := by
          intro y hy
          rw [mem_vec3Ball] at hy ⊢
          exact lt_trans hy hrrR
        have houter : IntegrableOn
            (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
            (vec3Ball z₀.1 R) volume := by
          exact hs.2
        have hsmall' : ∫ y in vec3Ball z₀.1 r,
            (vec3EuclideanNorm (u (y, s))) ^ 2 ≤
            ∫ y in vec3Ball z₀.1 R,
              (vec3EuclideanNorm (u (y, s))) ^ 2 := by
          exact setIntegral_mono_set houter
            (Filter.Eventually.of_forall (fun y => sq_nonneg _))
            (Filter.Eventually.of_forall (fun y hy => hsub hy))
        have houterEq := time_slice_energy_eq_ofReal houter
        have hS0le : essSup (timeSliceBallEnergy z₀.1 R ·
            (fun w => vec3EuclideanNorm (u w)))
            (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≤
            ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_toReal hS0]
          exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
        exact ((ENNReal.ofReal_le_ofReal hsmall').trans_eq houterEq).trans
          (hB.trans hS0le)
      · have hBae : ∀ᵐ s ∂volume.restrict
            (Ioc (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)),
            timeSliceBallEnergy z₀.1 R s
              (fun w => vec3EuclideanNorm (u w)) ≤ Sf :=
          ae_le_essSup
        have hFutureSfSub : Ioc z₀.2 (z₀.2 + h) ⊆
            Ioc (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁) := by
          intro s hs
          exact ⟨by linarith only [hs.1, hh₁R], by linarith only [hs.2, hsmall]⟩
        have hBae₀ : ∀ᵐ s ∂volume.restrict
              (Ioc (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)),
              timeSliceBallEnergy z₀.1 R s
                (fun w => vec3EuclideanNorm (u w)) ≤ Sf :=
          ae_le_essSup
        have hBae := ae_restrict_of_ae_restrict_of_subset
          hFutureSfSub hBae₀
        filter_upwards [hIntFuture, hBae] with s hs hB
        have hsub : vec3Ball z₀.1 r ⊆ vec3Ball z₀.1 R := by
          intro y hy
          rw [mem_vec3Ball] at hy ⊢
          exact lt_trans hy hrrR
        have houter : IntegrableOn
            (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
            (vec3Ball z₀.1 R) volume := by
          exact hs.2
        have hsmall' : ∫ y in vec3Ball z₀.1 r,
            (vec3EuclideanNorm (u (y, s))) ^ 2 ≤
            ∫ y in vec3Ball z₀.1 R,
              (vec3EuclideanNorm (u (y, s))) ^ 2 := by
          exact setIntegral_mono_set houter
            (Filter.Eventually.of_forall (fun y => sq_nonneg _))
            (Filter.Eventually.of_forall (fun y hy => hsub hy))
        have houterEq := time_slice_energy_eq_ofReal houter
        have hSfle : Sf ≤ ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_toReal hSf]
          exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
        exact ((ENNReal.ofReal_le_ofReal hsmall').trans_eq houterEq).trans
          (hB.trans hSfle)
  let _ : (ae (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))).NeBot := by
    rw [MeasureTheory.ae_restrict_neBot]
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (by nlinarith only [hR, hhpos])).ne'
  have hEss := essSup_le_of_ae_le (ENNReal.ofReal B) hAE
      (isCoboundedUnder_le_of_eventually_le _ (Filter.Eventually.of_forall fun _ => bot_le))
  have hreal := (ENNReal.toReal_le_toReal
      (ne_of_lt (lt_of_le_of_lt hEss ENNReal.ofReal_lt_top))
      ENNReal.ofReal_ne_top).mpr hEss
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ B)] using hreal

end CKN
