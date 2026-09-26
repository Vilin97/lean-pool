/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ContourIntegral

/-!
# Banach-valued holomorphic circle integrals

A compact contour integral of a jointly analytic Banach-valued kernel is analytic in the
parameters. This is the parameter-dependent Cauchy integral used for Riemann extension. The
contour is fixed while its kernel may depend on all parameters.

## Main results

`analyticOnNhd_circleIntegral_kernel` is holomorphy of a circle integral of a jointly analytic
Banach-valued kernel. `analyticOnNhd_integral_smul_compact_kernel` is the compactly parametrized
form.
-/

public section

open Complex MeasureTheory Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α]

omit [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α] in
/-- A Banach-valued jointly analytic kernel has an analytic circle integral. -/
theorem analyticOnNhd_circleIntegral_kernel
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → F} (hH : AnalyticOnNhd ℂ H W)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hW : ∀ x ∈ U, ∀ t ∈ sphere c R, (x, t) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∮ t in C(c, R), H (x, t)) U := by
  have hg : ContinuousOn (fun t : ℝ => deriv (circleMap c R) t) (Icc 0 (2 * Real.pi)) := by
    simp only [deriv_circleMap]
    fun_prop
  have h := analyticOnNhd_integral_smul_compact_kernel (μ := volume) isCompact_Icc
    (hg.integrableOn_compact isCompact_Icc) (continuous_circleMap c R).continuousOn hU hH
    (fun x hx t _ => hW x hx _ (circleMap_mem_sphere c hR t))
  simpa only [circleIntegral_def_Icc] using h

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
