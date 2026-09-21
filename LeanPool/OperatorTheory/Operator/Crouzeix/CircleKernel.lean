/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR

/-!
# The double-layer circle kernel: continuity and integrability (L4.2d support)

For an operator `A` whose numerical range closure lies in the open disk `ball c R`, the circle
`sphere c R` lies in the resolvent set (by `spectrum_subset_closure_numericalRange`), so the
double-layer circle kernel `B t = (-i γ'(t)) • R_A(γ(t))`, `γ = circleMap c R`, is continuous in
`t`.  This file records that continuity and the interval integrability over `[0, 2π]` of `B`, of the
symmetrized kernel `B + B†`, and of its polynomial weighting `p(γ(t)) • (B t + (B t)†)` — the
side conditions consumed by the positive-kernel contractivity bound (`PositiveKernelBound.lean`,
`DoubleLayerBound.lean`).

## Main declarations

* `sphere_subset_resolventSet_of_closure_numericalRange_subset_ball`
* `continuous_resolvent_circleMap`, `continuous_circleKernel`,
  `continuous_circleKernel_add_adjoint`
* `intervalIntegrable_circleKernel`, `intervalIntegrable_circleKernel_add_adjoint`,
  `intervalIntegrable_eval_smul_circleKernel_add_adjoint`

Requires `[CompleteSpace E]` (spectrum, adjoints).
-/

open Complex Polynomial spectrum
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- If the closure of the numerical range lies in the open disk `ball c R`, the circle
`sphere c R` lies in the resolvent set. -/
theorem sphere_subset_resolventSet_of_closure_numericalRange_subset_ball (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hW : closure (numericalRange A) ⊆ Metric.ball c R) :
    Metric.sphere c R ⊆ resolventSet ℂ A := by
  intro z hz
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  intro hzσ
  have hzb : z ∈ Metric.ball c R := hW (spectrum_subset_closure_numericalRange A hzσ)
  rw [Metric.mem_ball] at hzb
  rw [Metric.mem_sphere] at hz
  exact lt_irrefl _ (hz ▸ hzb)

/-- The resolvent is continuous along a circle contained in the resolvent set. -/
theorem continuous_resolvent_circleMap (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => resolvent A (circleMap c R t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((spectrum.hasDerivAt_resolvent_const_left
    (hρ (circleMap_mem_sphere c hR t))).continuousAt).comp (continuous_circleMap c R).continuousAt

/-- The double-layer circle kernel `B t = (-i γ'(t)) • R_A(γ(t))`, `γ = circleMap c R`, is
continuous when the circle lies in the resolvent set. -/
theorem continuous_circleKernel (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) := by
  have hd : Continuous (fun t : ℝ => -I * deriv (circleMap c R) t) := by
    simp only [deriv_circleMap]
    fun_prop
  exact hd.smul (continuous_resolvent_circleMap A hρ hR)

/-- The symmetrized circle kernel `B t + (B t)†` is continuous. -/
theorem continuous_circleKernel_add_adjoint (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ =>
      (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) :=
  (continuous_circleKernel A hρ hR).add
    ((ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).continuous.comp
      (continuous_circleKernel A hρ hR))

/-- The circle kernel is interval integrable over `[0, 2π]`. -/
theorem intervalIntegrable_circleKernel (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  (continuous_circleKernel A hρ hR).intervalIntegrable 0 (2 * Real.pi)

/-- The symmetrized circle kernel is interval integrable over `[0, 2π]`. -/
theorem intervalIntegrable_circleKernel_add_adjoint (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ =>
      (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  (continuous_circleKernel_add_adjoint A hρ hR).intervalIntegrable 0 (2 * Real.pi)

/-- The polynomially weighted symmetrized circle kernel is interval integrable over `[0, 2π]`. -/
theorem intervalIntegrable_eval_smul_circleKernel_add_adjoint (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) (p : ℂ[X]) :
    IntervalIntegrable (fun t : ℝ => p.eval (circleMap c R t) •
      ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  ((p.continuous.comp (continuous_circleMap c R)).smul
    (continuous_circleKernel_add_adjoint A hρ hR)).intervalIntegrable 0 (2 * Real.pi)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
