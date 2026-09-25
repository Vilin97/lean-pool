/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceWholeTime
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance

/-!
# Time integrability from a finite spatial slice estimate

The component estimates for `eq:pressure-gradient-morrey` supply all temporal
obligations on compactly interior source balls. A finite spatial estimate
then transfers them to the entire carrier in `prop:bootstrap`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- The explicit slice majorant in coordinates translated to a source centre. -/
def theoremATranslatedSliceMajorant
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) : ℝ≥0∞ :=
  originSliceGradientMajorant (rescaleVelocity 1 (x, 0) u)
    (rescaleGradient 1 (x, 0) Du) (rescalePressure 1 (x, 0) p)
    (rescaleForce 1 (x, 0) f) ((0 : Vec3), 0) hρ s

/-- Compact containment of the source ball suffices for both temporal
obligations of the complete origin majorant. -/
theorem theoremA_origin_majorant_time_of_spatial_inclusion
    {Ω : Set Vec3} {I : Set ℝ} {q ρ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hball : closure (vec3Ball (0 : Vec3) ρ) ⊆ Ω) :
    (∀ᵐ s ∂volume.restrict I,
      originSliceGradientMajorant u Du p f ((0 : Vec3), 0) hρ s ≠ ⊤) ∧
    (∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun s => (originSliceGradientMajorant u Du p f
        ((0 : Vec3), 0) hρ s).toReal) (volume.restrict T)) := by
  obtain ⟨J, _, hJord, hJcpt, hJI, hJunion, hJcover⟩ :=
    OriginInstance.exists_compact_ordConnected_exhaustion hsol.2.1 hsol.2.2.1
  have hbox (n : ℕ) : localBox Ω I (vec3Ball (0 : Vec3) ρ) (J n) := by
    refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hρ, hball, hJord n, ?_, ?_⟩
    · simpa only [(hJcpt n).isClosed.closure_eq] using hJcpt n
    · simpa only [(hJcpt n).isClosed.closure_eq] using hJI n
  constructor
  · rw [← hJunion, ae_restrict_iUnion_iff]
    intro n
    have hsource := origin_centered_source_memLp_ae_on_local_box hsol (hbox n) hρ
      (Subset.refl _) (fun s j => average (volume.restrict (vec3Ball (0 : Vec3) ρ))
        (fun y => u (y, s) j))
    filter_upwards [hsource] with s hs
    unfold originSliceGradientMajorant
    apply ne_of_lt
    apply ENNReal.add_lt_top.mpr
    refine ⟨ENNReal.add_lt_top.mpr ⟨?_, ENNReal.ofReal_lt_top⟩, ENNReal.ofReal_lt_top⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr (fun i _ => (hs i).eLpNorm_lt_top))
  · intro T hTc hTI
    obtain ⟨n, hn⟩ := hJcover (closure T) hTc hTI
    exact (origin_slice_majorant_integrable_on_local_box hsol hρ (hbox n)).mono_measure
      (Measure.restrict_mono (subset_closure.trans hn) le_rfl)

/-- Translating the source centre preserves the full-interval finiteness and
compact-time integrability of the explicit slice majorant. -/
theorem theoremA_translated_majorant_time
    {Ω : Set Vec3} {I : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hball : closure (vec3Ball x ρ) ⊆ Ω) :
    (∀ᵐ s ∂volume.restrict I, theoremATranslatedSliceMajorant u Du p f x hρ s ≠ ⊤) ∧
    (∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun s => (theoremATranslatedSliceMajorant u Du p f x hρ s).toReal)
        (volume.restrict T)) := by
  have ht : rescaledTime 1 0 I = I := by
    ext t
    simp [rescaledTime, scalingTime]
  have hshift := isSuitableWeakSolutionIntegrable_rescale hsol (x, 0) (by norm_num : (0 : ℝ) < 1)
  rw [ht] at hshift
  have hb : closure (vec3Ball (0 : Vec3) ρ) ⊆ rescaledSpace 1 x Ω := by
    intro y hy
    apply hball
    rw [closure_vec3Ball hρ] at hy ⊢
    simpa [rescaledSpace, scalingSpace] using hy
  exact theoremA_origin_majorant_time_of_spatial_inclusion hshift hρ hb

/-- A finite spatial slice estimate supplies all carrier time obligations.
The source centres and radius are chosen before the suitable solution. -/
theorem theoremA_carrier_slice_time_of_finite_cover
    (hCarrierFiniteCoverEstimate :
      ∀ R₁ : ℝ, 0 < R₁ → R₁ < 3 / 4 →
      ∃ (n : ℕ) (x : Fin n → Vec3) (ρ : ℝ) (hρ : 0 < ρ),
        (∀ j, closure (vec3Ball (x j) ρ) ⊆ vec3Ball (0 : Vec3) 1) ∧
        ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
          ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
          (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
            LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
            HasWeakPartialDerivOn (vec3Ball 0 R₁) i
              (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
          ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
            eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
                (volume.restrict (vec3Ball 0 R₁)) ≤
              ∑ j, theoremATranslatedSliceMajorant u Du p f (x j) hρ s) :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      0 < R₁ → R₁ < 3 / 4 →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      (∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
        eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball 0 R₁)) ≠ ⊤) ∧
      (∀ (i : Fin 3) (T : Set ℝ), IsCompact (closure T) → closure T ⊆ I →
        Integrable (fun s => (eLpNorm (fun y => Dp (y, s) i)
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball 0 R₁))).toReal)
          (volume.restrict T)) := by
  intro Ω I q R₁ u Du p f hsol hdom hR₁ hR₁upper Dp hDp hfield
  obtain ⟨n, x, ρ, hρ, hballs, hbound⟩ := hCarrierFiniteCoverEstimate R₁ hR₁ hR₁upper
  have hΩ := (OriginInstance.originUnitBall_subset_of_dom hdom).1
  have hb (j : Fin n) : closure (vec3Ball (x j) ρ) ⊆ Ω := by
    intro y hy
    apply hΩ
    change vec3EuclideanNorm (y - 0) ≤ 1
    exact (show vec3EuclideanNorm (y - 0) < 1 from hballs j hy).le
  let K : Fin n → ℝ → ℝ≥0∞ := fun j => theoremATranslatedSliceMajorant u Du p f (x j) hρ
  have ht (j : Fin n) := theoremA_translated_majorant_time hsol hρ (hb j)
  have hfinite : ∀ᵐ s ∂volume.restrict I, ∀ j : Fin n, K j s ≠ ⊤ :=
    ae_all_iff.mpr (fun j => (ht j).1)
  have hsum : ∀ᵐ s ∂volume.restrict I, (∑ j, K j s) ≠ ⊤ := by
    filter_upwards [hfinite] with s hs
    exact ne_of_lt (ENNReal.sum_lt_top.mpr (fun j _ => lt_top_iff_ne_top.mpr (hs j)))
  have hnorm := hbound hsol hdom Dp hDp hfield
  have htop : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball 0 R₁)) ≠ ⊤ := by
    intro i
    filter_upwards [hnorm i, hsum] with s hs hf
    exact ne_of_lt (hs.trans_lt (lt_top_iff_ne_top.mpr hf))
  refine ⟨htop, ?_⟩
  intro i T hTc hTI
  have hm := origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 6 / 5)
    (((measurable_pi_apply i).comp hDp).aemeasurable
      (μ := volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ T)))
  have hint : Integrable (fun s => ∑ j, (K j s).toReal) (volume.restrict T) :=
    integrable_finsetSum _ (fun j _ => (ht j).2 T hTc hTI)
  apply hint.mono' hm.ennreal_toReal.aestronglyMeasurable
  have hrestrict := Measure.restrict_mono (subset_closure.trans hTI) (le_refl volume)
  filter_upwards [ae_mono hrestrict hfinite, ae_mono hrestrict (htop i),
    ae_mono hrestrict (hnorm i), ae_mono hrestrict hsum] with s hs hn hbnd hsumfin
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [← ENNReal.toReal_sum (fun j _ => hs j)]
  exact (ENNReal.toReal_le_toReal hn hsumfin).mpr hbnd

end CKN.Core.Endgame
