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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.GlobalSourceSlice
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivatives of bounded-continuous spatial slices

A parabolic higher jet stores its time derivative pointwise in space.  Since
that derivative is itself a continuous path in the uniform norm, the whole
bounded-continuous spatial slice is differentiable in that norm.  The generic
lemma below records the uniform mean-value argument needed to make this
passage without postulating Banach-valued differentiability.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

section UniformDerivative

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise differentiability with a derivative continuous in the uniform
norm implies differentiability of the bounded-continuous-function-valued
path.  Only a neighborhood of the base time is needed. -/
theorem hasDerivAt_boundedContinuousFunction_of_pointwise
    {F G : ℝ → BoundedContinuousFunction X E} {t : ℝ}
    (hG : ContinuousAt G t)
    (hpoint : ∀ᶠ s in 𝓝 t, (∀ x : X,
      HasDerivAt (fun r : ℝ ↦ F r x) (G s x) s)) :
    HasDerivAt F (G t) t := by
  rw [hasDerivAt_iff_tendsto]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεtwo : 0 < ε / 2 := by positivity
  rw [Metric.continuousAt_iff] at hG
  obtain ⟨δG, hδG, hGδ⟩ := hG (ε / 2) hεtwo
  rw [eventually_nhds_iff] at hpoint
  obtain ⟨U, hU, hUopen, htU⟩ := hpoint
  obtain ⟨δU, hδU, hballU⟩ := Metric.isOpen_iff.mp hUopen t htU
  filter_upwards [Metric.ball_mem_nhds t (lt_min hδG hδU)] with s hst
  have hstG : dist s t < δG := hst.trans_le (min_le_left _ _)
  have hstU : dist s t < δU := hst.trans_le (min_le_right _ _)
  by_cases hseq : s = t
  · subst s
    simpa using hε
  have hsegmentU : segment ℝ t s ⊆ U := by
    intro r hr
    apply hballU
    have hrle : ‖r - t‖ ≤ ‖s - t‖ := norm_sub_le_of_mem_segment hr
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [Real.norm_eq_abs, abs_sub_comm] using hrle.trans_lt hstU
  have hsegmentG : ∀ r ∈ segment ℝ t s, dist (G r) (G t) < ε / 2 := by
    intro r hr
    apply hGδ
    have hrle : ‖r - t‖ ≤ ‖s - t‖ := norm_sub_le_of_mem_segment hr
    rw [Real.dist_eq] at hstG ⊢
    exact hrle.trans_lt hstG
  have hrem : ‖F s - F t - (s - t) • G t‖ ≤ (ε / 2) * ‖s - t‖ := by
    rw [BoundedContinuousFunction.norm_le (mul_nonneg hεtwo.le (norm_nonneg _))]
    intro x
    let R : ℝ → E := fun r ↦ F r x - (r - t) • G t x
    let R' : ℝ → E := fun r ↦ G r x - G t x
    have hRderiv : ∀ r ∈ segment ℝ t s,
        HasDerivWithinAt R (R' r) (segment ℝ t s) r := by
      intro r hr
      have hFr : HasDerivAt (fun a : ℝ ↦ F a x) (G r x) r := hU r (hsegmentU hr) x
      have hlin : HasDerivAt (fun a : ℝ ↦ (a - t) • G t x) (G t x) r := by
        simpa using ((hasDerivAt_id r).sub_const t).smul_const (G t x)
      exact (hFr.sub hlin).hasDerivWithinAt
    have hRbound : ∀ r ∈ segment ℝ t s, ‖R' r‖ ≤ ε / 2 := by
      intro r hr
      exact (BoundedContinuousFunction.norm_coe_le_norm (G r - G t) x).trans
        (le_of_lt (by simpa [dist_eq_norm] using hsegmentG r hr))
    have hmvt := (convex_segment t s).norm_image_sub_le_of_norm_hasDerivWithin_le
      hRderiv hRbound (left_mem_segment ℝ t s) (right_mem_segment ℝ t s)
    change ‖F s x - F t x - (s - t) • G t x‖ ≤ (ε / 2) * ‖s - t‖
    calc
      ‖F s x - F t x - (s - t) • G t x‖ = ‖R s - R t‖ := by
        simp only [R, sub_self, zero_smul, sub_zero]
        congr 1
        abel
      _ ≤ (ε / 2) * ‖s - t‖ := hmvt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · calc
      ‖s - t‖⁻¹ * ‖F s - F t - (s - t) • G t‖
          ≤ ‖s - t‖⁻¹ * ((ε / 2) * ‖s - t‖) := by
            gcongr
      _ = ε / 2 := by
        field_simp [sub_ne_zero.mpr hseq]
      _ < ε := by linarith
  · positivity

end UniformDerivative

section FiniteCylinder

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {t₀ T α : ℝ}

namespace FiniteParabolicC2AlphaBanach

/-- The value component of a finite higher jet, extended by clamping time at
the two faces and then regarded as a total path of bounded spatial
functions. -/
def clampedValueSlicePath
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ℝ → BoundedContinuousFunction X E :=
  ParabolicC0AlphaBanach.globalTimeSlice hα
    (ParabolicC0AlphaBanach.finiteSourceExtension hT hα
      (valueComponentL u))

/-- The corresponding clamped path of stored time derivatives. -/
def clampedTimeDerivSlicePath
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ℝ → BoundedContinuousFunction X E :=
  ParabolicC0AlphaBanach.globalTimeSlice hα
    (ParabolicC0AlphaBanach.finiteSourceExtension hT hα
      (timeDerivComponentL u))

@[simp]
theorem clampedValueSlicePath_apply_of_mem
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x : X) :
    clampedValueSlicePath hT hα u t x = value u (t, x) := by
  unfold clampedValueSlicePath
  rw [ParabolicC0AlphaBanach.globalTimeSlice_apply,
    ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
      hT hα (valueComponentL u) (t, x)
      (by simpa [parabolicFiniteCylinder] using ht),
    evalCLM_valueComponentL]

@[simp]
theorem clampedTimeDerivSlicePath_apply_of_mem
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x : X) :
    clampedTimeDerivSlicePath hT hα u t x = timeDeriv u (t, x) := by
  unfold clampedTimeDerivSlicePath
  rw [ParabolicC0AlphaBanach.globalTimeSlice_apply,
    ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
      hT hα (timeDerivComponentL u) (t, x)
      (by simpa [parabolicFiniteCylinder] using ht),
    evalCLM_timeDerivComponentL]

theorem continuous_clampedTimeDerivSlicePath
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    Continuous (clampedTimeDerivSlicePath hT hα u) :=
  ParabolicC0AlphaBanach.continuous_globalTimeSlice hα _

theorem continuous_clampedValueSlicePath
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    Continuous (clampedValueSlicePath hT hα u) :=
  ParabolicC0AlphaBanach.continuous_globalTimeSlice hα _

/-- The pointwise time derivative stored in a finite parabolic four-jet is
the genuine derivative of its entire bounded-continuous spatial slice. -/
theorem hasDerivAt_clampedValueSlicePath
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Ioo t₀ T) :
    HasDerivAt (clampedValueSlicePath hT hα u)
      (clampedTimeDerivSlicePath hT hα u t) t := by
  apply hasDerivAt_boundedContinuousFunction_of_pointwise
    (continuous_clampedTimeDerivSlicePath hT hα u).continuousAt
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  intro x
  have hbase := hasDerivAt_time u hs x
  have heq :
      (fun r : ℝ => clampedValueSlicePath hT hα u r x) =ᶠ[𝓝 s]
        (fun r : ℝ => value u (r, x)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact clampedValueSlicePath_apply_of_mem hT hα u ⟨hr.1, hr.2.le⟩ x
  have h := hbase.congr_of_eventuallyEq heq
  simpa only [clampedTimeDerivSlicePath_apply_of_mem
    hT hα u ⟨hs.1, hs.2.le⟩ x] using h

end FiniteParabolicC2AlphaBanach

end FiniteCylinder

end AnalyticPDE
end RicciFlow
