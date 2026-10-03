/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Differential-to-integral comparison

If `f` is continuous on `[0,T]`, differentiable on `(0,T)` with `f' ≤ B` and `B` continuous on
`[0,T]`, then `f T ≤ f 0 + ∫_0^T B`.  No regularity of `f'` is needed. -/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

theorem le_add_integral_of_deriv_le {f f' B : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hd : ∀ s ∈ Ioo 0 T, HasDerivAt f (f' s) s)
    (hB : ContinuousOn B (Icc 0 T)) (hle : ∀ s ∈ Ioo 0 T, f' s ≤ B s) :
    f T ≤ f 0 + ∫ s in (0 : ℝ)..T, B s := by
  have hu : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT
  have hBint : IntervalIntegrable B volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rwa [hu]
  have hPhiC : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, B s) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (a := 0) (b := T) (f := B) (by
        rw [hu]; exact hB.integrableOn_Icc)
    rwa [hu] at this
  have hPhiD : ∀ s ∈ Ioo 0 T, HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, B r) (B s) s := by
    intro s hs
    have hsI : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
    have hBs : IntervalIntegrable B volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.1.le]
      exact hB.mono (Icc_subset_Icc le_rfl hs.2.le)
    have hmeas : StronglyMeasurableAtFilter B (nhds s) volume :=
      (hB.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    have hca : ContinuousAt B s :=
      (hB.mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hs.1 hs.2)
    exact intervalIntegral.integral_hasDerivAt_right hBs hmeas hca
  set g : ℝ → ℝ := fun x => f x - ∫ r in (0 : ℝ)..x, B r with hg
  have hgC : ContinuousOn g (Icc 0 T) := hf.sub hPhiC
  have hgD : DifferentiableOn ℝ g (interior (Icc 0 T)) := by
    rw [interior_Icc]
    intro s hs
    exact ((hd s hs).sub (hPhiD s hs)).differentiableAt.differentiableWithinAt
  have hgd : ∀ x ∈ interior (Icc 0 T), deriv g x ≤ 0 := by
    rw [interior_Icc]
    intro s hs
    have hdg : HasDerivAt g (f' s - B s) s := (hd s hs).sub (hPhiD s hs)
    rw [hdg.deriv]
    linarith [hle s hs]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgC hgD hgd
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTm : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have := hanti h0 hTm hT
  simp only [hg, intervalIntegral.integral_same, sub_zero] at this
  linarith

end AVenhance.Infra.FullTheorem.Separation
