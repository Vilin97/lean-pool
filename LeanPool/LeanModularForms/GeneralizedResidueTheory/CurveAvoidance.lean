/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Tactic.Common
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# Curve Avoidance API

General-purpose lemmas for proving that curves avoid points, computing minimum distances,
and establishing slitPlane membership for shifted curves.

## Main definitions

* `CurveAvoids` - a curve on [a,b] avoids a point z₀
* `curveInfDist` - infimum distance from z₀ to the curve image on [a,b]

## Main results

* `curveInfDist_pos_of_avoids` - positive inf distance when curve avoids z₀
* `curveAvoids_of_im_pos` - curve with positive imaginary part avoids real points
* `curve_sub_in_slitPlane` - shifted curve lands in slitPlane
-/

open Set Complex Metric

/-- A continuous curve on [a,b] avoids a point z₀. -/
def CurveAvoids (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∀ t ∈ Icc a b, γ t ≠ z₀

/-- Infimum distance from z₀ to the curve image on [a,b]. -/
noncomputable def curveInfDist (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ '' Icc a b)

/-! ### Basic avoidance criteria -/

/-- Trivial wrapper: CurveAvoids follows from pointwise inequality. -/
theorem curveAvoids_of_ne_on_Icc {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, γ t ≠ z₀) : CurveAvoids γ a b z₀ :=
  h

/-- If every point on the curve has imaginary part strictly greater than z₀.im,
then the curve avoids z₀. -/
theorem curveAvoids_of_im_lt {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, z₀.im < (γ t).im) : CurveAvoids γ a b z₀ := by
  intro t ht heq
  have := h t ht
  rw [heq] at this
  exact lt_irrefl _ this

/-- If every point on the curve has real part different from z₀.re,
then the curve avoids z₀. -/
theorem curveAvoids_of_re_ne {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, (γ t).re ≠ z₀.re) : CurveAvoids γ a b z₀ := by
  intro t ht heq
  exact h t ht (by rw [heq])

/-- If every point on the curve has norm different from ‖z₀‖, then the curve avoids z₀.
Useful for curves on circles. -/
theorem curveAvoids_of_norm_ne {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, ‖γ t‖ ≠ ‖z₀‖) : CurveAvoids γ a b z₀ := by
  intro t ht heq
  exact h t ht (by rw [heq])

/-! ### Positive inf-distance -/

/-- If a continuous curve on [a,b] with a ≤ b avoids z₀, then the infimum
distance from z₀ to the curve image is positive. -/
theorem curveInfDist_pos_of_avoids {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (hav : CurveAvoids γ a b z₀) : 0 < curveInfDist γ a b z₀ := by
  unfold curveInfDist
  have h_compact : IsCompact (γ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hγ
  have h_closed : IsClosed (γ '' Icc a b) :=
    h_compact.isClosed
  have h_nonempty : (γ '' Icc a b).Nonempty := by
    exact ⟨γ a, mem_image_of_mem γ (left_mem_Icc.mpr hab)⟩
  rw [← h_closed.notMem_iff_infDist_pos h_nonempty]
  intro ⟨t, ht, heq⟩
  exact hav t ht heq

/-! ### slitPlane membership -/

/-- If a continuous curve avoids z₀ and every shifted value γ t - z₀ has positive
imaginary part or positive real part, then every shifted value lies in the slit plane. -/
theorem curve_sub_in_slitPlane {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (_hγ : ContinuousOn γ (Icc a b))
    (_hav : CurveAvoids γ a b z₀)
    (hpos : ∀ t ∈ Icc a b, 0 < (γ t - z₀).im ∨ 0 < (γ t - z₀).re) :
    ∀ t ∈ Icc a b, γ t - z₀ ∈ slitPlane := by
  intro t ht
  rw [Complex.mem_slitPlane_iff]
  rcases hpos t ht with him | hre
  · right; exact him.ne'
  · left; exact hre
