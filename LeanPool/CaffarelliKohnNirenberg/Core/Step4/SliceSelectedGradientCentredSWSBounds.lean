/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSData

/-!
# Quantitative bounds for the centred source

The slice norms in `def:sws` give the uncentred source estimate, the
mean-component bounds, and the localized force estimate used in
`eq:pressure-gradient-decomposition`.
All coefficients are explicit and independent of the solution.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- The uncentred source majorant in `eq:pressure-gradient-decomposition`, using the
native vector norms of the velocity, gradient, and force slices. -/
@[expose] def centredSWSUncentredMajorant (x : Vec3) (ρ q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ≥0∞ :=
  let μ := volume.restrict (vec3Ball x ρ)
  let A := eLpNorm (fun y => u (y, s)) 3 μ
  let D := eLpNorm (fun y => Du (y, s)) 2 μ
  let F := eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q) μ
  3 * (3 * (D * A + ENNReal.ofReal (cutoffGradientConstant / ρ) *
    (A * A * μ univ ^ (1 / 6 : ℝ))) + F * μ univ ^ (5 / 6 - 1 / q))

private theorem component_norm_le {μ : Measure Vec3} {g : Vec3 → Vec3}
    {p : ℝ≥0∞} (hg : MemLp g p μ) (i : Fin 3) :
    eLpNorm (fun x => g x i) p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae (hg.eval i).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_le_pi_norm (g x) i)

private theorem gradient_component_norm_le {μ : Measure Vec3}
    {g : Vec3 → Fin 3 → Vec3} {p : ℝ≥0∞} (hg : MemLp g p μ) (i j : Fin 3) :
    eLpNorm (fun x => g x i j) p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae ((hg.eval i).eval j).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_le_pi_norm (g x i) j).trans (norm_le_pi_norm (g x) i))

private theorem cutoff_partial_bound {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) (y : Vec3) :
    |spatialDeriv (mollifiedBallCutoff x hρ) i y| ≤ cutoffGradientConstant / ρ := by
  exact (abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff x hρ) y) i).trans
    (mollifiedBallCutoff_gradient_bound x hρ y)

/-- The uncentred estimate of `eq:pressure-gradient-decomposition` follows from suitable
solution data, with the explicit constants `3`, `1`, and the cutoff derivative bound. -/
theorem centredSWS_uncentred_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      AEStronglyMeasurable (fun x => sourceMorreyCutoffV
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, s)) (fun y => Du (y, s)) (fun y => f (y, s)) x)
        (volume.restrict (vec3Ball z.1 ρ)) ∧
      eLpNorm (fun x => sourceMorreyCutoffV
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, s)) (fun y => Du (y, s)) (fun y => f (y, s)) x)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball z.1 ρ)) ≤
          centredSWSUncentredMajorant z.1 ρ q u Du f s := by
  have hη := (mollifiedBallCutoff_smooth z.1 hρ).continuous.aestronglyMeasurable
    (μ := volume.restrict (vec3Ball z.1 ρ))
  have hdη (j : Fin 3) := (contDiff_spatialDeriv_smooth
    (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.aestronglyMeasurable
    (μ := volume.restrict (vec3Ball z.1 ρ))
  have hμ : (volume.restrict (vec3Ball z.1 ρ)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (μ := volume) subset_closure).trans_lt
      (measure_closure_vec3Ball_lt_top hρ)
  have hCd : 0 ≤ cutoffGradientConstant / ρ :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound z.1 hρ z.1)
  filter_upwards [centredSWS_slice_data hsol hρ hsub] with s hs
  have hbound := sourceMorreyCutoffV_slice_bound hsol.2.2.2.1 hμ
    (by norm_num : (0 : ℝ) ≤ 1) hCd hη
    (Eventually.of_forall fun y => by
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
      exact mollifiedBallCutoff_le_one z.1 hρ y) hdη
    (fun j => Eventually.of_forall (cutoff_partial_bound hρ j))
    (fun j => by simpa only [ENNReal.ofReal_ofNat] using component_norm_le hs.1 j)
    (fun i j => by simpa only [ENNReal.ofReal_ofNat] using gradient_component_norm_le hs.2.1 i j)
    (fun i => component_norm_le hs.2.2.1 i)
    (fun j => (hs.1.eval j).aestronglyMeasurable)
    (fun i j => ((hs.2.1.eval i).eval j).aestronglyMeasurable)
    (fun i => (hs.2.2.1.eval i).aestronglyMeasurable)
  refine ⟨?_, ?_⟩
  · apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.of_eval
    intro i
    apply AEStronglyMeasurable.aemeasurable
    simpa only [sourceMorreyCutoffV, pressureDivergenceCutoffSource, Pi.sub_apply,
      Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_def, Pi.mul_def] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
      ((hη.mul ((hs.2.1.eval i).eval j).aestronglyMeasurable).mul
        (hs.1.eval j).aestronglyMeasurable).add
      (((hdη j).mul (hs.1.eval i).aestronglyMeasurable).mul
        (hs.1.eval j).aestronglyMeasurable)).sub
      (hη.mul (hs.2.2.1.eval i).aestronglyMeasurable)
  · simpa only [centredSWSUncentredMajorant, ENNReal.ofReal_one, one_mul] using hbound

/-- Finite-volume Hölder bounds for the low-exponent velocity and gradient
components used in the mean correction of `eq:pressure-gradient-decomposition`. -/
theorem centredSWS_low_exponent_bounds_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ j, ‖sourceSliceCentredMean z.1 ρ u s j‖ ≤
        ⨍ y in vec3Ball z.1 ρ, |u (y, s) j|) ∧
      (∀ j, eLpNorm (fun y => u (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) ≤
        eLpNorm (fun y => u (y, s)) 3 (volume.restrict (vec3Ball z.1 ρ)) *
          (volume (vec3Ball z.1 ρ)) ^ (1 / 2 : ℝ)) ∧
      (∀ i j, eLpNorm (fun y => Du (y, s) i j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) ≤
        eLpNorm (fun y => Du (y, s)) 2 (volume.restrict (vec3Ball z.1 ρ)) *
          (volume (vec3Ball z.1 ρ)) ^ (1 / 3 : ℝ)) := by
  filter_upwards [centredSWS_slice_data hsol hρ hsub] with s hs
  refine ⟨fun j => centred_source_average_component_bound j, ?_, ?_⟩
  · intro j
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (q := 3) (by norm_num)
      (hs.1.eval j).aestronglyMeasurable
    have hm := mul_le_mul_of_nonneg_right (component_norm_le hs.1 j)
      (show (0 : ℝ≥0∞) ≤ volume (vec3Ball z.1 ρ) ^ (1 / 2 : ℝ) from bot_le)
    norm_num [Measure.restrict_apply_univ] at h
    exact h.trans hm
  · intro i j
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (q := 2) (by norm_num)
      ((hs.2.1.eval i).eval j).aestronglyMeasurable
    have hm := mul_le_mul_of_nonneg_right (gradient_component_norm_le hs.2.1 i j)
      (show (0 : ℝ≥0∞) ≤ volume (vec3Ball z.1 ρ) ^ (1 / 3 : ℝ) from bot_le)
    norm_num [Measure.restrict_apply_univ] at h
    exact h.trans hm

/-- The localized force in `eq:pk` has global `L^{6/5}` membership and its
explicit finite-volume Hölder bound on almost every suitable-solution slice. -/
theorem centredSWS_force_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i,
      MemLp (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      eLpNorm (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q)
          (volume.restrict (vec3Ball z.1 ρ)) *
            volume (vec3Ball z.1 ρ) ^ (5 / 6 - 1 / q) := by
  filter_upwards [centredSWS_slice_data hsol hρ hsub,
    slice_force_source_data_ae_of_sws hsol hρ hsub] with s hs hf
  intro i
  refine ⟨hf.2.1 i, ?_⟩
  have hfi := hs.2.2.1.eval i
  rw [← euclideanBall_eq_vec3Ball hρ] at hfi
  have h := eLpNorm_cutoff_mul_g_le hρ
    (by linarith only [hsol.2.2.2.1] : (6 / 5 : ℝ) ≤ q) hfi
  rw [euclideanBall_eq_vec3Ball hρ] at h
  have he : (1 / (6 / 5 : ℝ) - 1 / q) = 5 / 6 - 1 / q := by ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (component_norm_le hs.2.2.1 i) bot_le)

end CKN.Core.Step4
