/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpP8
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallOrigin

/-!
# Harmonic Remainder Force Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

private theorem memLp_volume_of_memLp_restrict_of_support_q
    {h : Vec3 → ℝ} {s : Set Vec3} {q : ℝ}
    (hmeas : AEStronglyMeasurable h volume) (hsupp : Function.support h ⊆ s)
    (hh : MemLp h (ENNReal.ofReal q) (volume.restrict s)) :
    MemLp h (ENNReal.ofReal q) volume := by
  rw [memLp_iff] at hh ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hmeas hsupp] at hh

private theorem force_sources_memLp_of_slice_data
    {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {x₀ : Vec3} {ρ s q : ℝ}
    (hq : 6 / 5 ≤ q)
    (hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηderiv : ∀ j y, |spatialDeriv η j y| ≤ cutoffGradientConstant / ρ)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hηbound : ∀ y, |η y| ≤ 1)
    (hf : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hI : (∫⁻ y in vec3Ball x₀ ρ,
      ‖f (y, s)‖ₑ ^ q) < ∞)
    (hsource₇ : ∀ j : Fin 3, AEStronglyMeasurable
      (fun y => η y * f (y, s) j) volume) :
    (∀ j : Fin 3, MemLp (fun y => η y * f (y, s) j)
      (ENNReal.ofReal q) volume) ∧
    (∀ j : Fin 3, MemLp (fun y => spatialDeriv η j y * f (y, s) j)
      (ENNReal.ofReal q) volume) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hq0 : 0 < q := by linarith only [hq]
  haveI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ, B] using
        (volume_vec3Ball_lt_top (x := x₀) (r := ρ))⟩
  have hF : MemLp (fun y : Vec3 => f (y, s))
      (ENNReal.ofReal q) (volume.restrict B) := by
    rw [memLp_iff, eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top hf, eLpNorm'_eq_lintegral_enorm]
    have hI' : (∫⁻ y in B, ‖f (y, s)‖ₑ ^ (ENNReal.ofReal q).toReal) < ⊤ := by
      simpa only [B, ENNReal.toReal_ofReal hq0.le] using hI
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt hI')
  have hcomponent (j : Fin 3) : MemLp (fun y : Vec3 => f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict B) := by
    apply hF.of_le
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hf)
    filter_upwards [] with y
    change ‖f (y, s) j‖ ≤ ‖f (y, s)‖
    exact norm_le_pi_norm (f (y, s)) j
  have hsource₇_support (j : Fin 3) :
      Function.support (fun y : Vec3 => η y * f (y, s) j) ⊆ B := by
    intro y hy
    by_contra hyB
    apply hy
    change η y * f (y, s) j = 0
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₈_support (j : Fin 3) :
      Function.support
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) ⊆ B := by
    intro y hy
    by_contra hyB
    apply hy
    change spatialDeriv η j y * f (y, s) j = 0
    have hzero : spatialDeriv η j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport hηy))
    rw [hzero, zero_mul]
  have hsource₇_mem (j : Fin 3) : MemLp
      (fun y : Vec3 => η y * f (y, s) j)
      (ENNReal.ofReal q) (volume.restrict B) := by
    apply (hcomponent j).of_le
      ((hsource₇ j).mono_measure Measure.restrict_le_self)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, one_mul] using
      (mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg (f (y, s) j)))
  have hsource₇_mem_global (j : Fin 3) : MemLp
      (fun y : Vec3 => η y * f (y, s) j)
      (ENNReal.ofReal q) volume := by
    exact memLp_volume_of_memLp_restrict_of_support_q
      ((hsource₇ j)) (hsource₇_support j) (hsource₇_mem j)
  have hderiv_meas (j : Fin 3) : AEStronglyMeasurable
      (spatialDeriv η j) volume := by
    have hηd := contDiff_spatialDeriv_smooth hηsmooth j
    exact hηd.continuous.aestronglyMeasurable
  have hsource₈_int (j : Fin 3) : Integrable
      (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) volume := by
    have hqone : 1 ≤ q := by linarith only [hq]
    have hmul := (hcomponent j).integrable
      (ENNReal.one_le_ofReal.2 hqone)
    have hderiv_meas_B : AEStronglyMeasurable (spatialDeriv η j)
        (volume.restrict B) :=
      (hderiv_meas j).mono_measure Measure.restrict_le_self
    have hmul' := hmul.mul_bdd
      hderiv_meas_B
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          hηderiv j y))
    have hmul'' : Integrable
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j)
        (volume.restrict B) := by
      simpa only [mul_comm] using hmul'
    exact decomposition_full_of_on_sws hmul''
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y : Vec3 => f (y, s) j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))
  constructor
  · exact fun j => hsource₇_mem_global j
  · intro j
    apply memLp_volume_of_memLp_restrict_of_support_q
      (hsource₈_int j).aestronglyMeasurable (hsource₈_support j)
    let c : ℝ := max (cutoffGradientConstant / ρ) 0
    have hc : 0 ≤ c := le_max_right _ _
    have hcmem : MemLp (fun y : Vec3 => c * f (y, s) j)
        (ENNReal.ofReal q) (volume.restrict B) := (hcomponent j).const_mul c
    apply hcmem.of_le
      ((hsource₈_int j).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc] using
      (mul_le_mul_of_nonneg_right
        ((hηderiv j y).trans (le_max_left _ _)) (abs_nonneg (f (y, s) j)))

/-- The force potentials have the local membership and linear growth required by the
force-cancellation theorem, for almost every slice of a suitable weak solution. -/
theorem pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      0 ≤ pressureP7GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
          (vec3EuclideanNorm z.1 + ρ) +
        pressureP8GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
          (vec3EuclideanNorm z.1 + ρ) ∧
      ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
        (pressureP7GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
            (vec3EuclideanNorm z.1 + ρ) +
          pressureP8GrowthConstant (mollifiedBallCutoff z.1 hρ) f s
            (vec3EuclideanNorm z.1 + ρ)) * (1 + R) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hηc : HasCompactSupport η := by
    simpa [η] using mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using mollifiedBallCutoff_smooth z.1 hρ
  have hηmeas : AEStronglyMeasurable η volume :=
    hηsmooth.continuous.aestronglyMeasurable
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ := by
    simpa [η] using pressure_cutoff_support_subset_ball z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    apply abs_le.mpr
    exact ⟨by linarith only [mollifiedBallCutoff_nonneg z.1 hρ y], by
      simpa [η] using mollifiedBallCutoff_le_one z.1 hρ y⟩
  have hηderiv : ∀ j y, |spatialDeriv η j y| ≤ cutoffGradientConstant / ρ := by
    intro j y
    simpa [η] using pressure_cutoff_spatialDeriv_bound z.1 hρ y j
  obtain ⟨_Ω', _J, hbox, hball, _htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω := by
    exact hηsupport.trans (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  have hdata := sws_p7_slice_data hsol hρ hsub hηc hηΩ hηbound hηsupport hηmeas
  let R₀ : ℝ := vec3EuclideanNorm z.1 + ρ
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  have hball₀ : vec3Ball z.1 ρ ⊆ closedBall (0 : Vec3) R₀ := by
    simpa [R₀] using vec3Ball_subset_closedBall_zero z.1 ρ
  filter_upwards [hdata] with s hs
  have hq₆ : 6 / 5 ≤ q := by linarith only [hsol.2.2.2.1]
  obtain ⟨hmem₇, hmem₈⟩ := force_sources_memLp_of_slice_data hq₆ hηsmooth
    hηderiv hηsupport hηbound hs.1 hs.2.1 (fun j => (hs.2.2 j).1)
  have hsupp₇ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R₀ →
      η y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun hyB => hy (hball₀ hyB)
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hsupp₈ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R₀ →
      spatialDeriv η j y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun hyB => hy (hball₀ hyB)
    have hzero : spatialDeriv η j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport hηy))
    rw [hzero, zero_mul]
  obtain ⟨hpair_mem, hpair_growth⟩ :=
    pressureP7_add_pressureP8_memLp_and_lpNorm_growth hR₀ hq₆
      hmem₇ hsupp₇ hmem₈ hsupp₈
  have hpair_nonneg := pressureP7_add_pressureP8_growthConstant_nonneg η f s hR₀
  refine ⟨?_, ?_, ?_⟩
  · simpa [η] using hpair_mem
  · simpa [η, R₀] using hpair_nonneg
  · simpa [η, R₀] using hpair_growth

end CKN
