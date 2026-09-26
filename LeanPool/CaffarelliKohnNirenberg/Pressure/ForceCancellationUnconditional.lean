/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceCancellation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms

/-!
# Force Cancellation Unconditional

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private theorem mollifiedBallCutoff_smoothCompactTest {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) :
    SmoothCompactTest (mollifiedBallCutoff x₀ hρ) := by
  refine ⟨fun n => ?_, mollifiedBallCutoff_hasCompactSupport x₀ hρ⟩
  exact (mollifiedBallCutoff_smooth x₀ hρ).of_le (by simp)

private theorem force_source_integrable
    {f : ParabolicPoint → Vec3} {s : ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) {V : Set Vec3}
    (hfs : Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V))
    (hηV : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ V) :
    (∀ j, Integrable
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j)) ∧
    (∀ j, Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
          f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
          f (y, s) j)) := by
  have hηmeasV : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict V) :=
    ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hsourceInt (j : Fin 3) :
      Integrable
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume := by
    have hfc : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) :=
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hfs.aestronglyMeasurable
    have hfcint : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfcint.mul_bdd hηmeasV
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          (abs_le.mpr ⟨by linarith only
            [mollifiedBallCutoff_nonneg x₀ hρ y],
            mollifiedBallCutoff_le_one x₀ hρ y⟩)))
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) V volume by
        simpa only [IntegrableOn, mul_comm] using hmul)
      ((tsupport_mul_subset_left (f := mollifiedBallCutoff x₀ hρ)
        (g := fun y => f (y, s) j)).trans hηV)
  have hsourceSupp (j : Fin 3) : HasCompactSupport
      (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) := by
    exact (mollifiedBallCutoff_hasCompactSupport x₀ hρ).mul_right
  have hderivC (j : Fin 3) : HasCompactSupport
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hderivV (j : Fin 3) :
      tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) ⊆ V := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηV
  have hderivInt (j : Fin 3) :
      Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
          f (y, s) j) volume := by
    have hηd := contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) j
    have hηdV : AEStronglyMeasurable
        (spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (volume.restrict V) := by
      have hηdmeas : AEStronglyMeasurable
          (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) volume :=
        hηd.continuous.aestronglyMeasurable
      exact hηdmeas.mono_measure Measure.restrict_le_self
    have hfc : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfc.mul_bdd hηdV
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          pressure_cutoff_spatialDeriv_bound x₀ hρ y j))
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
            f (y, s) j) V volume by
        simpa only [IntegrableOn] using
          (hmul.congr (Eventually.of_forall (fun y => by ring))))
      ((tsupport_mul_subset_left
        (f := spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (g := fun y => f (y, s) j)).trans (hderivV j))
  have hderivSupp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
        f (y, s) j) := by
    exact (hderivC j).mul_right
  constructor
  · intro j
    exact ⟨hsourceInt j, hsourceSupp j⟩
  · intro j
    exact ⟨hderivInt j, hderivSupp j⟩

/- The solution-level adapter separates the distributional slice hypothesis from
the local integrability and growth estimates used by the global harmonic
uniqueness theorem. -/
theorem pressure_force_eq_zero_of_sws_distributionalDivergenceFree
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {C : ℝ → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      DistributionalDivergenceFree (fun x : Vec3 => f (x, s)))
    (hmem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)))
    (hgrowth : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ C s ∧ ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C s * (1 + R)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hηc : HasCompactSupport η := by
    exact mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηmeas : AEStronglyMeasurable η volume := by
    exact (mollifiedBallCutoff_smooth z.1 hρ).continuous.aestronglyMeasurable
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ := by
    exact pressure_cutoff_support_subset_ball z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    apply abs_le.mpr
    exact ⟨by linarith only [mollifiedBallCutoff_nonneg z.1 hρ y],
      mollifiedBallCutoff_le_one z.1 hρ y⟩
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω := by
    exact hηsupport.trans (fun x hx =>
      hbox.2.2.1 (subset_closure (hball hx)))
  obtain ⟨V, _hVopen, hηV, _hVmeas, hVcompact, hVΩ, hslice⟩ :=
    decomposition_slice_integrability hsol hηc
      hηΩ hηc hηΩ
  have hTsubI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I := by
    exact htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hsliceT : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V) := by
    exact (ae_restrict_of_ae_restrict_of_subset hTsubI hslice).mono
      (fun s hs => hs.2.2)
  filter_upwards [hdiv, hmem, hgrowth, hsliceT] with s hsdiv hsmem hsgrowth hs
  have hsource := force_source_integrable hρ hs hηV
  have htest := mollifiedBallCutoff_smoothCompactTest (x₀ := z.1) hρ
  exact
    (pressure_force_eq_zero_of_distributionalDivergenceFree htest hsdiv
    (fun j => (hsource.1 j).1) (fun j => (hsource.1 j).2)
    (fun j => (hsource.2 j).1) (fun j => (hsource.2 j).2)
    hsmem ⟨C s, hsgrowth.1, hsgrowth.2⟩)

/-- The force part vanishes on almost every slice once the force is locally
integrable and distributionally divergence free in space-time. -/
theorem pressure_force_eq_zero_of_sws_unconditional
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hloc : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      LocallyIntegrable (fun x : Vec3 => f (x, s) i) volume)
    (hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂volume = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  have hdiv := ae_distributional_divergence_free_of_forall_test hloc hslice
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    hsol hρ hsub
  let C : ℝ → ℝ := fun s =>
    CKN.Foundation.Euclidean.pressureP7GrowthConstant
        (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ) +
      CKN.Foundation.Euclidean.pressureP8GrowthConstant
        (mollifiedBallCutoff z.1 hρ) f s
        (vec3EuclideanNorm z.1 + ρ)
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) :=
    hproducer.mono fun s hs => hs.1
  have hgrowth : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ C s ∧ ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C s * (1 + R) := by
    filter_upwards [hproducer] with s hs
    exact ⟨by simpa [C] using hs.2.1, by simpa [C] using hs.2.2⟩
  exact pressure_force_eq_zero_of_sws_distributionalDivergenceFree
    hsol hρ hsub hdiv hmem hgrowth

end CKN
