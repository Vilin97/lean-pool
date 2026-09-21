/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.BrokenVariation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Differentiation of parameter-dependent interval integrals

This file packages the compact-rectangle estimates used to differentiate the energy of a
coordinate variation twice.  Joint continuity on a compact parameter-time rectangle supplies
the uniform domination required by the interval-integral API.
-/

noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology Interval ContDiff

namespace BonnetMyersEntry

theorem intervalIntegral_hasDerivAt_of_continuousOn
    {F F' : ℝ → ℝ → ℝ} {x₀ a b : ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hsx : s ∈ 𝓝 x₀) (hab : a ≤ b)
    (hF : ContinuousOn F.uncurry (s ×ˢ Icc a b))
    (hF' : ContinuousOn F'.uncurry (s ×ˢ Icc a b))
    (hdiff : ∀ x ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasDerivAt (fun x ↦ ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  obtain ⟨C, hC⟩ := (hs.prod isCompact_Icc).bddAbove_image hF'.norm
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (a := a) (b := b)
      (s := s) (bound := fun _ ↦ C) hsx ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hsx] with x hx
    have hxcont : ContinuousOn (F x) (Icc a b) := by
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht ↦ mk_mem_prod hx ht)
    exact (hxcont.mono (by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self))
      |>.aestronglyMeasurable measurableSet_uIoc
  · have hx₀s : x₀ ∈ s := mem_of_mem_nhds hsx
    have hxcont : ContinuousOn (F x₀) (Icc a b) := by
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht ↦ mk_mem_prod hx₀s ht)
    have hxcont' : ContinuousOn (F x₀) [[a, b]] := by
      simpa [uIcc_of_le hab] using hxcont
    exact hxcont'.intervalIntegrable
  · have hx₀s : x₀ ∈ s := mem_of_mem_nhds hsx
    have hxcont : ContinuousOn (F' x₀) (Icc a b) := by
      exact hF'.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht ↦ mk_mem_prod hx₀s ht)
    exact (hxcont.mono (by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self))
      |>.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with t
    intro ht x hx
    apply hC
    have ht' : t ∈ Ioc a b := by simpa [uIoc_of_le hab] using ht
    exact ⟨(x, t), ⟨hx, ht'.1.le, ht'.2⟩, rfl⟩
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro ht x hx
    have ht' : t ∈ Ioc a b := by simpa [uIoc_of_le hab] using ht
    exact hdiff x hx t ⟨ht'.1.le, ht'.2⟩

theorem intervalIntegral_continuousOn_of_continuousOn
    {F : ℝ → ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hab : a ≤ b)
    (hF : ContinuousOn F.uncurry (s ×ˢ Icc a b)) :
    ContinuousOn (fun x ↦ ∫ t in a..b, F x t) (interior s) := by
  obtain ⟨C, hC⟩ := (hs.prod isCompact_Icc).bddAbove_image hF.norm
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (μ := volume) (bound := fun _ ↦ C)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hycont : ContinuousOn (F y) (Icc a b) := by
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht ↦ mk_mem_prod (interior_subset hy) ht)
    exact (hycont.mono (by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self))
      |>.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards with t
    intro ht
    apply hC
    have ht' : t ∈ Ioc a b := by simpa [uIoc_of_le hab] using ht
    exact ⟨(y, t), ⟨interior_subset hy, ht'.1.le, ht'.2⟩, rfl⟩
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro ht
    have ht' : t ∈ Ioc a b := by simpa [uIoc_of_le hab] using ht
    have hp : (x, t) ∈ s ×ˢ Icc a b :=
      ⟨interior_subset hx, ht'.1.le, ht'.2⟩
    have hg : ContinuousWithinAt (fun y : ℝ ↦ (y, t)) (interior s) x := by
      fun_prop
    change ContinuousWithinAt
      (F.uncurry ∘ fun y : ℝ ↦ (y, t)) (interior s) x
    exact ContinuousWithinAt.comp
      (f := fun y : ℝ ↦ (y, t)) (g := F.uncurry)
      (s := interior s) (t := s ×ˢ Icc a b) (x := x)
      (hF (x, t) hp) hg
      (fun y hy ↦ ⟨interior_subset hy, ht'.1.le, ht'.2⟩)

theorem intervalIntegral_contDiffAt_two_of_continuousOn
    {F F₁ F₂ : ℝ → ℝ → ℝ} {x₀ a b : ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hsx : s ∈ 𝓝 x₀) (hab : a ≤ b)
    (hF : ContinuousOn F.uncurry (s ×ˢ Icc a b))
    (hF₁ : ContinuousOn F₁.uncurry (s ×ˢ Icc a b))
    (hF₂ : ContinuousOn F₂.uncurry (s ×ˢ Icc a b))
    (hdiff₁ : ∀ x ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt (fun y ↦ F y t) (F₁ x t) x)
    (hdiff₂ : ∀ x ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt (fun y ↦ F₁ y t) (F₂ x t) x) :
    ContDiffAt ℝ 2 (fun x ↦ ∫ t in a..b, F x t) x₀ := by
  let G : ℝ → ℝ := fun x ↦ ∫ t in a..b, F₁ x t
  let H : ℝ → ℝ := fun x ↦ ∫ t in a..b, F₂ x t
  have hinterior : interior s ∈ 𝓝 x₀ := by
    exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hsx)
  have hGderiv : ∀ x ∈ interior s, HasDerivAt
      (fun y ↦ ∫ t in a..b, F y t) (G x) x := by
    intro x hx
    exact intervalIntegral_hasDerivAt_of_continuousOn hs
      (mem_interior_iff_mem_nhds.mp hx) hab hF hF₁ hdiff₁
  have hHderiv : ∀ x ∈ interior s, HasDerivAt G (H x) x := by
    intro x hx
    exact intervalIntegral_hasDerivAt_of_continuousOn hs
      (mem_interior_iff_mem_nhds.mp hx) hab hF₁ hF₂ hdiff₂
  have hHcont : ContinuousOn H (interior s) :=
    intervalIntegral_continuousOn_of_continuousOn hs hab hF₂
  rw [show (2 : ℕ∞ω) = (1 : ℕ) + 1 by norm_num,
    contDiffAt_succ_iff_hasFDerivAt]
  let DG : ℝ → ℝ →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.toSpanSingleton ℝ (G x)
  refine ⟨DG, ⟨interior s, hinterior, fun x hx ↦ (hGderiv x hx).hasFDerivAt⟩, ?_⟩
  have hGcontDiff : ContDiffAt ℝ (1 : ℕ∞ω) G x₀ := by
    rw [contDiffAt_one_iff]
    let DH : ℝ → ℝ →L[ℝ] ℝ := fun x ↦
      ContinuousLinearMap.toSpanSingleton ℝ (H x)
    refine ⟨DH, interior s, hinterior, ?_, ?_⟩
    · exact (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := ℝ)).continuous.comp_continuousOn hHcont
    · intro x hx
      exact (hHderiv x hx).hasFDerivAt
  change ContDiffAt ℝ (1 : ℕ∞ω)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)) ∘ G) x₀
  exact (ContinuousLinearMap.toSpanSingletonCLE
    (𝕜 := ℝ) (E := ℝ)).contDiff.contDiffAt.comp x₀ hGcontDiff

/-- The exact second iterated derivative obtained by differentiating a
parameter-dependent interval integral twice on a compact rectangle. -/
theorem intervalIntegral_iteratedDeriv_two_eq_of_continuousOn
    {F F₁ F₂ : ℝ → ℝ → ℝ} {x₀ a b : ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hsx : s ∈ 𝓝 x₀) (hab : a ≤ b)
    (hF : ContinuousOn F.uncurry (s ×ˢ Icc a b))
    (hF₁ : ContinuousOn F₁.uncurry (s ×ˢ Icc a b))
    (hF₂ : ContinuousOn F₂.uncurry (s ×ˢ Icc a b))
    (hdiff₁ : ∀ x ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt (fun y ↦ F y t) (F₁ x t) x)
    (hdiff₂ : ∀ x ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt (fun y ↦ F₁ y t) (F₂ x t) x) :
    iteratedDeriv 2 (fun x ↦ ∫ t in a..b, F x t) x₀ =
      ∫ t in a..b, F₂ x₀ t := by
  let A : ℝ → ℝ := fun x ↦ ∫ t in a..b, F x t
  let B : ℝ → ℝ := fun x ↦ ∫ t in a..b, F₁ x t
  have hAB : ∀ x ∈ interior s, HasDerivAt A (B x) x := by
    intro x hx
    exact intervalIntegral_hasDerivAt_of_continuousOn hs
      (mem_interior_iff_mem_nhds.mp hx) hab hF hF₁ hdiff₁
  have hB : HasDerivAt B (∫ t in a..b, F₂ x₀ t) x₀ :=
    intervalIntegral_hasDerivAt_of_continuousOn hs hsx hab hF₁ hF₂ hdiff₂
  have hderivAB : deriv A =ᶠ[𝓝 x₀] B := by
    have hinterior : interior s ∈ 𝓝 x₀ :=
      isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hsx)
    filter_upwards [hinterior] with x hx
    exact (hAB x hx).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  simp only [iteratedDeriv_one]
  rw [Filter.EventuallyEq.deriv_eq hderivAB]
  exact hB.deriv

end BonnetMyersEntry
