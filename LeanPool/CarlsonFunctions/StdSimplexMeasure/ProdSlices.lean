/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Product integrals over measurable sets by slices

This file provides Tonelli and Fubini formulas for integration over an arbitrary measurable
subset of a product, together with their specialization to a region between two measurable
real-valued graphs, in the closed-interval convention.

Mathlib's `setLIntegral_prod` / `setIntegral_prod` cover only rectangles `s ×ˢ t`. The inner
integral below is over the section `{y | (x, y) ∈ T}`, written `Prod.mk x ⁻¹' T`.

The named Mathlib region between graphs is `regionBetween` (`Ioo`). The lemmas in this file use
the closed companion already recorded as `measurableSet_region_between_cc`. For Lebesgue measure
on the fibre, the graphs are null, so the `Ioo` and `Icc` conventions agree.

This is a temporary project home. Intended Mathlib placement:

* `setLIntegral_prod_slices`, `setLIntegral_prod_slices_symm`
  → `Mathlib.MeasureTheory.Measure.Prod`, next to `setLIntegral_prod`
* `setIntegral_prod_slices`, `setIntegral_prod_slices_symm`
  → `Mathlib.MeasureTheory.Integral.Prod`, next to `setIntegral_prod`
* the `Icc` graph lemmas
  → next to `regionBetween` in `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

`setIntegral_prod_Icc_slice_volume` is a local convenience for the product `MeasureSpace`
instance on `α × ℝ` and is not intended for Mathlib.

TODO: if those lemmas land in Mathlib, delete this file and switch uses to the upstream names.
-/

open MeasureTheory Set

public noncomputable section

namespace MeasureTheory

private theorem indicator_swap {α β γ : Type*} [Zero γ] (T : Set (α × β)) (f : α × β → γ) :
    (fun q : β × α ↦ T.indicator f q.swap) =
      (Prod.swap ⁻¹' T).indicator (fun q ↦ f q.swap) := by
  classical
  ext q
  rw [Set.indicator_apply, Set.indicator_apply]
  exact if_congr Set.mem_preimage.symm rfl rfl

/-! ## Nonnegative integrals -/

/-- Tonelli's theorem for a nonnegative integral restricted to a measurable subset `T` of a
product. The inner integral is over the section `{y | (x, y) ∈ T}`. Unlike
`setIntegral_prod_slices`, this result requires no integrability hypothesis. -/
theorem setLIntegral_prod_slices
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → ENNReal) (hf : AEMeasurable f ((μ.prod ν).restrict T)) :
    ∫⁻ p in T, f p ∂μ.prod ν =
      ∫⁻ x, ∫⁻ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν ∂μ := by
  rw [← lintegral_indicator hT]
  rw [lintegral_prod _ ((aemeasurable_indicator_iff hT).mpr hf)]
  refine lintegral_congr fun x ↦ ?_
  rw [← lintegral_indicator (measurable_prodMk_left hT)]
  exact lintegral_congr fun y ↦ rfl

/-- Symmetric Tonelli theorem for a nonnegative integral restricted to a measurable subset `T`
of a product. The inner integral is over the section `{x | (x, y) ∈ T}`. -/
theorem setLIntegral_prod_slices_symm
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → ENNReal) (hf : AEMeasurable f ((μ.prod ν).restrict T)) :
    ∫⁻ p in T, f p ∂μ.prod ν =
      ∫⁻ y, ∫⁻ x in Prod.mk y ⁻¹' (Prod.swap ⁻¹' T), f (x, y) ∂μ ∂ν := by
  have hS : MeasurableSet (Prod.swap ⁻¹' T) := hT.preimage measurable_swap
  have hf' : AEMeasurable (fun q : β × α ↦ f q.swap)
      ((ν.prod μ).restrict (Prod.swap ⁻¹' T)) := by
    refine AEMeasurable.comp_measurable ?_ measurable_swap
    convert hf
    rw [← Measure.restrict_map measurable_swap hT, Measure.prod_swap]
  rw [← lintegral_indicator hT, ← lintegral_prod_swap, indicator_swap T f,
    lintegral_indicator hS]
  exact setLIntegral_prod_slices (Prod.swap ⁻¹' T) hS (fun q ↦ f q.swap) hf'

/-! ## Bochner integrals -/

/-- Fubini's theorem for an integrable function restricted to a measurable subset `T` of a
product. The inner integral is over the section `{y | (x, y) ∈ T}`. -/
theorem setIntegral_prod_slices
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → E) (hf : IntegrableOn f T (μ.prod ν)) :
    ∫ p in T, f p ∂μ.prod ν =
      ∫ x, ∫ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hT]
  rw [integral_prod _ (hf.integrable_indicator hT)]
  apply integral_congr_ae
  filter_upwards with x
  change ∫ y, T.indicator f (x, y) ∂ν = ∫ y in Prod.mk x ⁻¹' T, f (x, y) ∂ν
  rw [← integral_indicator (measurable_prodMk_left hT)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Symmetric Fubini theorem for an integrable function restricted to a measurable subset `T`
of a product. The inner integral is over the section `{x | (x, y) ∈ T}`. -/
theorem setIntegral_prod_slices_symm
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (f : α × β → E) (hf : IntegrableOn f T (μ.prod ν)) :
    ∫ p in T, f p ∂μ.prod ν =
      ∫ y, ∫ x in Prod.mk y ⁻¹' (Prod.swap ⁻¹' T), f (x, y) ∂μ ∂ν := by
  have hS : MeasurableSet (Prod.swap ⁻¹' T) := hT.preimage measurable_swap
  have hf' : IntegrableOn (fun q : β × α ↦ f q.swap) (Prod.swap ⁻¹' T) (ν.prod μ) := by
    have hInt : Integrable ((Prod.swap ⁻¹' T).indicator (fun q ↦ f q.swap)) (ν.prod μ) := by
      rw [← indicator_swap T f]
      exact integrable_swap_iff.mpr (hf.integrable_indicator hT)
    exact (integrable_indicator_iff hS).mp hInt
  rw [← integral_indicator hT, ← integral_prod_swap, indicator_swap T f, integral_indicator hS]
  exact setIntegral_prod_slices (Prod.swap ⁻¹' T) hS (fun q ↦ f q.swap) hf'

/-! ## Regions between graphs of real functions -/

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
private theorem prod_Icc_slice_preimage (s : Set α) (lo hi : α → ℝ) (x : α) :
    Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)} =
      {t | x ∈ s ∧ t ∈ Icc (lo x) (hi x)} := by
  ext t
  simp [mem_Icc]

/-- Tonelli's theorem for the region between two graphs, in the closed-interval convention.
This is the `Icc` companion of `regionBetween`; see `measurableSet_region_between_cc`. -/
theorem setLIntegral_prod_Icc_slice {μ : Measure α} [SFinite μ]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → ENNReal)
    (hf : AEMeasurable f
      ((μ.prod volume).restrict {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)})) :
    ∫⁻ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p ∂μ.prod volume =
      ∫⁻ x in s, ∫⁻ t in Icc (lo x) (hi x), f (x, t) ∂volume ∂μ := by
  have hT := measurableSet_region_between_cc hlo hhi hs
  rw [setLIntegral_prod_slices _ hT f hf, ← lintegral_indicator hs]
  refine lintegral_congr fun x ↦ ?_
  rw [prod_Icc_slice_preimage]
  by_cases hx : x ∈ s
  · simp [hx, Icc]
  · simp [hx]

/-- Fubini's theorem for the region between two graphs, in the closed-interval convention.
This is the `Icc` companion of `regionBetween`; see `measurableSet_region_between_cc`. -/
theorem setIntegral_prod_Icc_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → E)
    (hf : IntegrableOn f {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)} (μ.prod volume)) :
    ∫ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p ∂μ.prod volume =
      ∫ x in s, ∫ t in Icc (lo x) (hi x), f (x, t) ∂volume ∂μ := by
  have hT := measurableSet_region_between_cc hlo hhi hs
  rw [setIntegral_prod_slices _ hT f hf, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with x
  rw [prod_Icc_slice_preimage]
  by_cases hx : x ∈ s
  · simp [hx, Icc]
  · simp [hx]

omit [MeasurableSpace α] in
/-- Volume form of `setIntegral_prod_Icc_slice`, matching the product `MeasureSpace`
instance on `α × ℝ`. Local convenience, not intended for Mathlib. -/
theorem setIntegral_prod_Icc_slice_volume
    {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set α} (hs : MeasurableSet s)
    {lo hi : α → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (f : α × ℝ → E)
    (hf : IntegrableOn f {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}) :
    ∫ p in {p | p.1 ∈ s ∧ p.2 ∈ Icc (lo p.1) (hi p.1)}, f p =
      ∫ x in s, ∫ t in Icc (lo x) (hi x), f (x, t) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod_Icc_slice hs hlo hhi f hf

end MeasureTheory

end
