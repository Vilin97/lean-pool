/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.WeightedExponentialKernel

/-! # Bad Scale Tail Assembly -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Assembling the bad-scale tail from the split components

This file combines the sharp bad-scale split with the component estimates.  It
contains no new probabilistic input: the only ingredients are the four-way
union bound and the deterministic crude-top cutoff.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pure assembly of the four split branches of a bad-scale event. -/
theorem measureReal_badScaleEvent_le_of_component_bounds
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {Rht Rhb Rcb Rct : ℝ}
    (hht : μ.real (highTopBadScaleEvent H K a t α q) ≤ Rht)
    (hhb : μ.real (highBottomBadScaleEvent H K a t α q) ≤ Rhb)
    (hcb : μ.real (crudeBottomBadScaleEvent H K a t α q) ≤ Rcb)
    (hct : μ.real (crudeTopBadScaleEvent H K a t α q) ≤ Rct) :
    μ.real (badScaleEvent H t α q) ≤ Rht + Rhb + Rcb + Rct := by
  calc
    μ.real (badScaleEvent H t α q)
        ≤ μ.real (highTopBadScaleEvent H K a t α q) +
            μ.real (highBottomBadScaleEvent H K a t α q) +
              μ.real (crudeBottomBadScaleEvent H K a t α q) +
                μ.real (crudeTopBadScaleEvent H K a t α q) :=
          measureReal_badScaleEvent_le_sharp_split
            (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
    _ ≤ Rht + Rhb + Rcb + Rct := by
          linarith

/-- Assembly of the full bad-scale event when the crude-top branch is empty. -/
theorem measureReal_badScaleEvent_le_of_component_bounds_crudeTop_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {Rht Rhb Rcb : ℝ}
    (hht : μ.real (highTopBadScaleEvent H K a t α q) ≤ Rht)
    (hhb : μ.real (highBottomBadScaleEvent H K a t α q) ≤ Rhb)
    (hcb : μ.real (crudeBottomBadScaleEvent H K a t α q) ≤ Rcb)
    (hct : μ.real (crudeTopBadScaleEvent H K a t α q) = 0) :
    μ.real (badScaleEvent H t α q) ≤ Rht + Rhb + Rcb := by
  have hfull :=
    measureReal_badScaleEvent_le_of_component_bounds
      (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
      (Rht := Rht) (Rhb := Rhb) (Rcb := Rcb) (Rct := 0)
      hht hhb hcb (by simp [hct])
  linarith

/-- Full bad-scale bound from the three quantitative component bounds and
the deterministic crude-top cutoff. -/
theorem measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {Rht Rhb Rcb : ℝ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hq_large :
      let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
      L + 1 < (1 - α / a) * (q : ℝ))
    (hht : μ.real (highTopBadScaleEvent H K a t α q) ≤ Rht)
    (hhb : μ.real (highBottomBadScaleEvent H K a t α q) ≤ Rhb)
    (hcb : μ.real (crudeBottomBadScaleEvent H K a t α q) ≤ Rcb) :
    μ.real (badScaleEvent H t α q) ≤ Rht + Rhb + Rcb := by
  have hct :
      μ.real (crudeTopBadScaleEvent H K a t α q) = 0 :=
    measureReal_crudeTopBadScaleEvent_eq_zero_of_large
      (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
      ha hα_nonneg hαt hαa hq_large
  exact
    measureReal_badScaleEvent_le_of_component_bounds_crudeTop_zero
      (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
      hht hhb hcb hct

/-- Kernel-shaped assembly of the full bad-scale event.  This is the
manuscript four-way split after the crude-top component has been cut off:
the right side is exactly the sum of the three surviving branch bounds. -/
theorem measureReal_badScaleEvent_le_kernel_sum_of_component_kernels
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {Aht ρht τ Ahb ρhb Acb ρcb σ : ℝ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hq_large :
      let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
      L + 1 < (1 - α / a) * (q : ℝ))
    (hht :
      μ.real (highTopBadScaleEvent H K a t α q) ≤
        Real.exp 1 *
          (Real.exp (-(Aht ^ τ)) * linearExpKernelConst ρht τ))
    (hhb :
      μ.real (highBottomBadScaleEvent H K a t α q) ≤
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Ahb ^ τ)) * geometricExpKernelConst ρhb τ))
    (hcb :
      μ.real (crudeBottomBadScaleEvent H K a t α q) ≤
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Acb ^ σ)) * geometricExpKernelConst ρcb σ)) :
    μ.real (badScaleEvent H t α q) ≤
      Real.exp 1 *
          (Real.exp (-(Aht ^ τ)) * linearExpKernelConst ρht τ) +
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Ahb ^ τ)) * geometricExpKernelConst ρhb τ) +
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Acb ^ σ)) * geometricExpKernelConst ρcb σ) := by
  exact
    measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
      (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
      (Rht :=
        Real.exp 1 *
          (Real.exp (-(Aht ^ τ)) * linearExpKernelConst ρht τ))
      (Rhb :=
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Ahb ^ τ)) * geometricExpKernelConst ρhb τ))
      (Rcb :=
        ((q + 1 : ℕ) : ℝ) * Real.exp 1 *
          (Real.exp (-(Acb ^ σ)) * geometricExpKernelConst ρcb σ))
      ha hα_nonneg hαt hαa hq_large hht hhb hcb

/-- Weighted-kernel assembly of the full bad-scale event.  This is the
no-log version used in the current proof: the finite maxima remain in the
component constants, while the row weights are absorbed by the weighted
superexponential kernels. -/
theorem measureReal_badScaleEvent_le_weighted_kernel_sum_of_component_kernels
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {Aht ρht Ahb ρhb Acb ρcb ηhigh ηcrude Cht Chb Ccb w : ℝ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hq_large :
      let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
      L + 1 < (1 - α / a) * (q : ℝ))
    (hht :
      μ.real (highTopBadScaleEvent H K a t α q) ≤
        Cht *
          (Real.exp (-(Aht ^ ηhigh)) *
            weightedLinearExpKernelConst w (ρht ^ ηhigh)))
    (hhb :
      μ.real (highBottomBadScaleEvent H K a t α q) ≤
        Chb *
          (Real.exp (-(Ahb ^ ηhigh)) *
            weightedGeometricExpKernelConst w (ρhb ^ ηhigh)))
    (hcb :
      μ.real (crudeBottomBadScaleEvent H K a t α q) ≤
        Ccb *
          (Real.exp (-(Acb ^ ηcrude)) *
            weightedGeometricExpKernelConst w (ρcb ^ ηcrude))) :
    μ.real (badScaleEvent H t α q) ≤
      Cht *
          (Real.exp (-(Aht ^ ηhigh)) *
            weightedLinearExpKernelConst w (ρht ^ ηhigh)) +
        Chb *
          (Real.exp (-(Ahb ^ ηhigh)) *
            weightedGeometricExpKernelConst w (ρhb ^ ηhigh)) +
        Ccb *
          (Real.exp (-(Acb ^ ηcrude)) *
            weightedGeometricExpKernelConst w (ρcb ^ ηcrude)) := by
  exact
    measureReal_badScaleEvent_le_of_component_kernels_and_crudeTop_cutoff
      (μ := μ) (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
      (Rht :=
        Cht *
          (Real.exp (-(Aht ^ ηhigh)) *
            weightedLinearExpKernelConst w (ρht ^ ηhigh)))
      (Rhb :=
        Chb *
          (Real.exp (-(Ahb ^ ηhigh)) *
            weightedGeometricExpKernelConst w (ρhb ^ ηhigh)))
      (Rcb :=
        Ccb *
          (Real.exp (-(Acb ^ ηcrude)) *
            weightedGeometricExpKernelConst w (ρcb ^ ηcrude)))
      ha hα_nonneg hαt hαa hq_large hht hhb hcb

end

end Section57
end Ch05
end Book
end Homogenization
