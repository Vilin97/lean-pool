/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationHarmonic

/-!
# Lin34 Slices

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! Almost-everywhere pressure slice integrability on an admissible cylinder. -/

theorem sws_pressure_memLp_slice_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hpmeas : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.1
  have hpprod : AEStronglyMeasurable p
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hpmeas
  have hpBT : AEStronglyMeasurable p
      ((volume.restrict B).prod (volume.restrict T)) := by
    apply hpprod.mono_measure
    apply Measure.prod_mono
    · exact Measure.restrict_mono_set volume hball
    · exact Measure.restrict_mono_set volume htime
  have hpglobal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hdata.2.2.2.2.2.2.1
  have hpBT' : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    apply hpglobal.mono_measure
    apply Measure.prod_mono
    · exact Measure.restrict_mono_set volume hball
    · exact Measure.restrict_mono_set volume htime
  have hpPow : Integrable (fun w : Vec3 × ℝ =>
      |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have h := hpBT'.integrable_norm_rpow (by norm_num) (by norm_num)
    change Integrable (fun w : Vec3 × ℝ =>
      ‖p w‖ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal)
      ((volume.restrict B).prod (volume.restrict T)) at h
    simpa only [Real.norm_eq_abs,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h
  have hpPowSlice := hpPow.prod_left_ae
  have hpMeasSlice := hpBT.prodMk_right
  filter_upwards [hpPowSlice, hpMeasSlice] with s hs hms
  have hs' : Integrable (fun x : Vec3 =>
      ‖p (x, s)‖ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal)
      (volume.restrict B) := by
    simpa only [Real.norm_eq_abs,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hs
  exact (integrable_norm_rpow_iff hms (by norm_num) (by norm_num)).mp hs'

/-! The residual is formed before any Calderón--Zygmund estimate is used. -/

theorem pressure_cutoff_pressure_memLp_slice
    {p : ParabolicPoint → ℝ} {η : Vec3 → ℝ} {s : ℝ}
    {B : Set Vec3}
    (hp : MemLp (fun x : Vec3 => p (x, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B))
    (hηmeas : AEStronglyMeasurable η (volume.restrict B))
    (hηbound : ∀ᵐ x ∂volume.restrict B, ‖η x‖ ≤ (1 : ℝ)) :
    MemLp (fun x : Vec3 => η x * p (x, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) := by
  apply hp.of_le (hηmeas.mul hp.aestronglyMeasurable)
  filter_upwards [hηbound] with x hx
  change |η x * p (x, s)| ≤ ‖p (x, s)‖
  rw [abs_mul, Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs, one_mul] using
    (mul_le_mul_of_nonneg_right hx (abs_nonneg (p (x, s))))

theorem pressure_remainder_eq_on_inner
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3}
    {ρ s : ℝ} (hρ : 0 < ρ) :
    (pressureP2 (mollifiedBallCutoff x₀ hρ) u c s +
      pressureP3 (mollifiedBallCutoff x₀ hρ) u c s +
      pressureP4 (mollifiedBallCutoff x₀ hρ) u c s +
      pressureP5 (mollifiedBallCutoff x₀ hρ) p s +
      pressureP6 (mollifiedBallCutoff x₀ hρ) p s) =ᵐ[
        volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      ((fun x => p (x, s)) -
        pressureP1 (mollifiedBallCutoff x₀ hρ) u c p f s -
        (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s)) := by
  filter_upwards [ae_restrict_mem
      (by
        change MeasurableSet (euclideanBall x₀ (13 * ρ / 20))
        exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
          continuous_const).measurableSet)] with x hx
  have hη : mollifiedBallCutoff x₀ hρ x = 1 :=
    mollifiedBallCutoff_eq_one_on_inner x₀ hρ hx
  have hpoint := pressure_decomposition_pointwise
    (mollifiedBallCutoff x₀ hρ) u c p f s x
  rw [hη] at hpoint
  change pressureP2 (mollifiedBallCutoff x₀ hρ) u c s x +
      pressureP3 (mollifiedBallCutoff x₀ hρ) u c s x +
      pressureP4 (mollifiedBallCutoff x₀ hρ) u c s x +
      pressureP5 (mollifiedBallCutoff x₀ hρ) p s x +
      pressureP6 (mollifiedBallCutoff x₀ hρ) p s x =
    p (x, s) - pressureP1 (mollifiedBallCutoff x₀ hρ) u c p f s x -
      (pressureP7 (mollifiedBallCutoff x₀ hρ) f s x +
        pressureP8 (mollifiedBallCutoff x₀ hρ) f s x)
  linarith only [hpoint]

theorem pressure_harmonic_potential_data_ae_of_sws_annulus
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hzero : ∀ y, y ∉ euclideanBall z.1 (3 * ρ / 4) \
      euclideanClosedBall z.1 (13 * ρ / 20) →
      (∀ i, spatialDeriv (mollifiedBallCutoff z.1 hρ) i y = 0) ∧
      (∀ i j, mixedSecond (mollifiedBallCutoff z.1 hρ) i j y = 0)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      PressureHarmonicPotentialData
        ((euclideanBall z.1 (3 * ρ / 4) \
          euclideanClosedBall z.1 (13 * ρ / 20))ᶜ)
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff z.1 hρ) :=
    mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport (mollifiedBallCutoff z.1 hρ) :=
    mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hBΩ : vec3Ball z.1 ρ ⊆ Ω := by
    intro x hx
    exact hbox.2.2.1 (subset_closure (hball hx))
  have hηΩ : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans hBΩ
  have hglobal : ∀ᵐ s ∂volume.restrict I,
      PressureHarmonicPotentialData
        ((euclideanBall z.1 (3 * ρ / 4) \
          euclideanClosedBall z.1 (13 * ρ / 20))ᶜ)
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s := by
    apply pressure_harmonic_potential_data_ae_of_sws
      (U := (euclideanBall z.1 (3 * ρ / 4) \
        euclideanClosedBall z.1 (13 * ρ / 20))ᶜ)
      (c := fun t j => MeasureTheory.average
        (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
      hsol hη hηc hηΩ
    · intro i y hy
      exact (hzero y hy).1 i
    · intro i j y hy
      exact (hzero y hy).2 i j
    · intro y hy
      rw [spatialLaplacian]
      simp only [Fin.sum_univ_three]
      have h0 := (hzero y hy).2 0 0
      have h1 := (hzero y hy).2 1 1
      have h2 := (hzero y hy).2 2 2
      change spatialDeriv (spatialDeriv (mollifiedBallCutoff z.1 hρ) 0) 0 y +
        spatialDeriv (spatialDeriv (mollifiedBallCutoff z.1 hρ) 1) 1 y +
        spatialDeriv (spatialDeriv (mollifiedBallCutoff z.1 hρ) 2) 2 y = 0
      simp only [show spatialDeriv (spatialDeriv
          (mollifiedBallCutoff z.1 hρ) 0) 0 y = 0 by simpa [mixedSecond] using h0,
        show spatialDeriv (spatialDeriv
          (mollifiedBallCutoff z.1 hρ) 1) 1 y = 0 by simpa [mixedSecond] using h1,
        show spatialDeriv (spatialDeriv
          (mollifiedBallCutoff z.1 hρ) 2) 2 y = 0 by simpa [mixedSecond] using h2,
        add_zero]
  have hTI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  exact ae_restrict_of_ae_restrict_of_subset hTI hglobal

end CKN
