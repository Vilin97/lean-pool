/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Positivity of operator-valued Bochner integrals

The double-layer argument produces a positive continuous-linear-map kernel
pointwise along a contour.  This file supplies the measure-theoretic bridge:
an integrable operator-valued function which is positive almost everywhere
has a positive Bochner integral.

## Main declarations

* `ContinuousLinearMap.isPositive_integral` -- positivity passes through a
  Bochner integral over a positive measure.
* `ContinuousLinearMap.isPositive_intervalIntegral` -- the oriented-interval
  specialization used by contour parametrizations.
* `ContinuousLinearMap.integral_mono_ae` -- almost-everywhere Loewner order
  passes to Bochner integrals.
* `ContinuousLinearMap.intervalIntegral_mono_ae` -- the corresponding result
  on positively oriented intervals.
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace ContinuousLinearMap

variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The Bochner integral of an integrable family of positive continuous
linear maps is positive when the family is positive almost everywhere. -/
theorem isPositive_integral (f : X → E →L[ℂ] E) (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, IsPositive (f x)) : IsPositive (∫ x, f x ∂μ) := by
  rw [isPositive_iff_complex]
  intro v
  have hfv : Integrable (fun x => f x v) μ :=
    (ContinuousLinearMap.apply ℂ E v).integrable_comp hf
  have hinner : Integrable (fun x => ⟪f x v, v⟫_ℂ) μ := hfv.inner_const v
  have hinter :
      ⟪(∫ x, f x ∂μ) v, v⟫_ℂ = ∫ x, ⟪f x v, v⟫_ℂ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hf]
    calc
      ⟪∫ x, f x v ∂μ, v⟫_ℂ = starRingEnd ℂ ⟪v, ∫ x, f x v ∂μ⟫_ℂ :=
        (inner_conj_symm (𝕜 := ℂ) (∫ x, f x v ∂μ) v).symm
      _ = starRingEnd ℂ (∫ x, ⟪v, f x v⟫_ℂ ∂μ) := by rw [integral_inner hfv]
      _ = ∫ x, starRingEnd ℂ ⟪v, f x v⟫_ℂ ∂μ := integral_conj.symm
      _ = ∫ x, ⟪f x v, v⟫_ℂ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact inner_conj_symm (𝕜 := ℂ) (f x v) v
  constructor
  · rw [hinter, ← integral_re hinner, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    exact (isPositive_iff_complex (f x)).mp hx v |>.1
  · rw [hinter, ← integral_re hinner]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact (isPositive_iff_complex (f x)).mp hx v |>.2

/-- A positively oriented interval integral of positive operators is
positive. -/
theorem isPositive_intervalIntegral (f : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hpos : ∀ᵐ x ∂volume.restrict (Set.Ioc a b), IsPositive (f x)) :
    IsPositive (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab]
  exact isPositive_integral f
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf) hpos

/-- Bochner integration is monotone for the Loewner order on continuous
linear maps. -/
theorem integral_mono_ae (f g : X → E →L[ℂ] E) (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  rw [ContinuousLinearMap.le_def, ← integral_sub hg hf]
  exact isPositive_integral (fun x => g x - f x) (hg.sub hf) hfg

/-- Positively oriented interval integration is monotone for the Loewner
order on continuous linear maps. -/
theorem intervalIntegral_mono_ae (f g : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_mono_ae f g
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg) hfg

end ContinuousLinearMap

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
