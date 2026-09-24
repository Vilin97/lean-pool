/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTWindowSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSourceMeasurable

/-! # Jointly measurable completed pressure operators from suitability

Both force-free and near-force sources use one spatial cutoff and one time
window. The selected operator fields satisfy the completed-operator identity
on the full spatial space at almost every time, including the zero extension.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Suitable-solution data give jointly measurable completed Riesz fields for
both fixed sources, with the spatial and time indicators explicit. -/
theorem exists_measurable_fixed_riesz_fields_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η)
      u Du (sourceSliceCentredMean z.1 ρ u)
    let Q := parabolicCylinder z.1 z.2 ρ
    ∃ T Tforce : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ j i, Measurable (T j i)) ∧ (∀ j i, Measurable (Tforce j i)) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => Q.indicator (fun w => V w j) (y, s))) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => Tforce j i (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => Q.indicator (fun w => η w.1 * f w j) (y, s))) := by
  dsimp only
  have hm := fixed_pressure_sources_aemeasurable_of_sws hsol hρ hsub
  have hv := centredSWS_source_data_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u)
  have hf := slice_force_source_data_ae_of_sws hsol hρ hsub
  have hT (j i : Fin 3) := exists_measurable_riesz_extension_field_on_window j i hρ
    measurableSet_Ioc (hm j).1 (hv.mono (fun _ hs => hs.1 j))
  have hF (j i : Fin 3) := exists_measurable_riesz_extension_field_on_window j i hρ
    measurableSet_Ioc (hm j).2 (hf.mono (fun _ hs => hs.2.1 j))
  choose T hTm hTi using hT
  choose F hFm hFi using hF
  exact ⟨T, F, hTm, hFm, hTi, hFi⟩

/-- On the chosen time window, spatial restriction does not change a source
that vanishes off the localization ball. -/
theorem product_indicator_slice_eq_of_support
    {F : Vec3 × ℝ → ℝ} {B : Set Vec3} {J : Set ℝ} {s : ℝ}
    (hs : s ∈ J) (hF : ∀ y, y ∉ B → F (y, s) = 0) :
    (fun y => (B ×ˢ J).indicator F (y, s)) = fun y => F (y, s) := by
  funext y
  by_cases hy : y ∈ B
  · exact Set.indicator_of_mem (show (y, s) ∈ B ×ˢ J from ⟨hy, hs⟩) F
  · rw [Set.indicator_of_notMem (fun h => hy h.1), hF y hy]

/-- The fixed force-free source vanishes pointwise outside its cutoff ball. -/
theorem fixed_centred_source_eq_zero_off_ball
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {c : ℝ → Vec3} {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (s : ℝ) (i : Fin 3) (hy : y ∉ vec3Ball x ρ) :
    sourceMorreyCutoffVCentredTensorSpacetime (mollifiedBallCutoff x hρ)
      (spatialDeriv (mollifiedBallCutoff x hρ)) u Du c (y, s) i = 0 := by
  have he : mollifiedBallCutoff x hρ y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hy (pressure_cutoff_support_subset_ball x hρ h))
  have hd (j : Fin 3) : spatialDeriv (mollifiedBallCutoff x hρ) j y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy
      (pressure_cutoff_support_subset_ball x hρ
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)) h)))
  simp only [sourceMorreyCutoffVCentredTensorSpacetime,
    sourceMorreyCutoffVCentredTensor, pressureDivergenceCutoffSourceCentredTensor, he, hd,
      zero_mul, add_zero,
    Finset.sum_const_zero]

/-- On each time in the localization window, the spatial cutoff makes both
indicator-restricted sources equal to the original localized sources. -/
theorem fixed_pressure_sources_indicator_slice_eq
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Ioc (z.2 - ρ ^ 2) z.2) (j : Fin 3) :
    let η := mollifiedBallCutoff z.1 hρ
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η)
      u Du (sourceSliceCentredMean z.1 ρ u)
    ((fun y => (parabolicCylinder z.1 z.2 ρ).indicator (fun w => V w j) (y, s)) =
      fun y => V (y, s) j) ∧
    ((fun y => (parabolicCylinder z.1 z.2 ρ).indicator
      (fun w => η w.1 * f w j) (y, s)) = fun y => η y * f (y, s) j) := by
  dsimp only
  constructor
  · exact product_indicator_slice_eq_of_support hs
      (fun y hy => fixed_centred_source_eq_zero_off_ball hρ y s j hy)
  · apply product_indicator_slice_eq_of_support hs
    intro y hy
    have he : mollifiedBallCutoff z.1 hρ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (pressure_cutoff_support_subset_ball z.1 hρ h))
    rw [he, zero_mul]

end CKN.Core.Step4
