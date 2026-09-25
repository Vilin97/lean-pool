/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSBounds

/-!
# Global centred-source estimates

The local norm data of `def:sws` give compactly supported `L^{6/5}` sources
and the explicit centred majorant used in `eq:pressure-gradient-decomposition`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- The global componentwise source majorant in `eq:pressure-gradient-decomposition`,
including the constant-mean correction and the localized force norm. -/
def centredSWSCentredMajorant (x : Vec3) (ρ q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ≥0∞ :=
  let μ := volume.restrict (vec3Ball x ρ)
  let A := eLpNorm (fun y => u (y, s)) 3 μ * volume (vec3Ball x ρ) ^ (1 / 2 : ℝ)
  let D := eLpNorm (fun y => Du (y, s)) 2 μ * volume (vec3Ball x ρ) ^ (1 / 3 : ℝ)
  centredSWSUncentredMajorant x ρ q u Du f s +
    ENNReal.ofReal (∑ j : Fin 3, ⨍ y in vec3Ball x ρ, |u (y, s) j|) *
      (∑ _j : Fin 3, (D + ENNReal.ofReal (cutoffGradientConstant / ρ) * A)) +
    eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q) μ *
      volume (vec3Ball x ρ) ^ (5 / 6 - 1 / q)

/-- Suitable-solution data supply global source membership and compact support
for any time-dependent spatial centring vector in `eq:pressure-gradient-decomposition`. -/
theorem centredSWS_source_data_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i, MemLp (fun x => sourceMorreyCutoffVCentredTensorSpacetime
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        u Du c (x, s) i) (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i, HasCompactSupport (fun x => sourceMorreyCutoffVCentredTensorSpacetime
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        u Du c (x, s) i)) := by
  let K := tsupport (mollifiedBallCutoff z.1 hρ)
  have hK : IsCompact K := (mollifiedBallCutoff_hasCompactSupport z.1 hρ).isCompact
  have hKB : K ⊆ vec3Ball z.1 ρ := pressure_cutoff_support_subset_ball z.1 hρ
  filter_upwards [centredSWS_slice_data hsol hρ hsub] with s hs
  exact pressureDivergenceCutoffSourceCentredTensor_memLp_hasCompactSupport
    (c := c s) hK (mollifiedBallCutoff_smooth z.1 hρ) le_rfl
    (fun j => (hs.1.eval j).mono_measure (Measure.restrict_mono hKB le_rfl))
    (fun i j => ((hs.2.1.eval i).eval j).mono_measure (Measure.restrict_mono hKB le_rfl))

/-- The quantitative centred bound for `eq:pressure-gradient-decomposition`, with all
local source estimates extracted from the suitable weak solution. -/
theorem centredSWS_source_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i,
      eLpNorm (fun x => sourceMorreyCutoffVCentredTensorSpacetime
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        u Du (sourceSliceCentredMean z.1 ρ u) (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          centredSWSCentredMajorant z.1 ρ q u Du f s := by
  let η := mollifiedBallCutoff z.1 hρ
  let B := vec3Ball z.1 ρ
  have hη := (mollifiedBallCutoff_smooth z.1 hρ).continuous.aestronglyMeasurable
    (μ := volume.restrict B)
  have hdη (j : Fin 3) := (contDiff_spatialDeriv_smooth
    (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.aestronglyMeasurable
    (μ := volume.restrict B)
  have hCd : 0 ≤ cutoffGradientConstant / ρ :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound z.1 hρ z.1)
  filter_upwards [centredSWS_slice_data hsol hρ hsub,
    centredSWS_uncentred_bound_ae hsol hρ hsub,
    centredSWS_low_exponent_bounds_ae hsol hρ hsub,
    centredSWS_force_bound_ae hsol hρ hsub,
    centredSWS_source_data_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u)]
    with s hs hunc hlo hf hglob
  have hlocal := sourceMorreyCutoffVCentredTensor_slice_bound_of_sourceMorrey
    (x := z.1) (ρ := ρ) (s := s)
    (by norm_num : (0 : ℝ) ≤ 1) hCd hη hdη
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
      exact mollifiedBallCutoff_le_one z.1 hρ y)
    (fun j => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact (abs_apply_le_vecEuclideanNorm (classicalGradient η y) j).trans
        (mollifiedBallCutoff_gradient_bound z.1 hρ y))
    (fun j => (hs.1.eval j).aestronglyMeasurable)
    (fun i j => ((hs.2.1.eval i).eval j).aestronglyMeasurable)
    hlo.2.1 hlo.2.2 hunc.1 hunc.2
    (fun i => (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hf i).2)
  intro i
  have hsupp : Function.support (fun x => sourceMorreyCutoffVCentredTensorSpacetime
      η (spatialDeriv η) u Du (sourceSliceCentredMean z.1 ρ u) (x, s) i) ⊆ B := by
    intro x hx
    by_contra hn
    have he : η x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hn (pressure_cutoff_support_subset_ball z.1 hρ h))
    have hd (j : Fin 3) : spatialDeriv η j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn
        (pressure_cutoff_support_subset_ball z.1 hρ
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)) h)))
    apply hx
    simp only [sourceMorreyCutoffVCentredTensorSpacetime, sourceMorreyCutoffVCentredTensor,
      pressureDivergenceCutoffSourceCentredTensor, he, hd, zero_mul, add_zero,
      Finset.sum_const_zero]
  rw [← eLpNorm_restrict_eq_of_support_subset (hglob.1 i).aestronglyMeasurable hsupp]
  simpa only [centredSWSCentredMajorant, sourceMorreyCutoffVCentredTensorSpacetime,
    ENNReal.ofReal_one, one_mul, η, B] using hlocal i

end CKN.Core.Step4
