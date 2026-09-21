/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ParametricIntegral

/-!
# Locally dominated holomorphic integrals

A locally uniform integrable bound on a holomorphic integrand also bounds its derivatives on
smaller balls, by the Schwarz estimate. This avoids explicit logarithmic estimates when the
parameters occur in complex powers. Measurability of the derivative is kept as a separate
hypothesis so that the integration space needs no topology.

## Main results

`analyticOnNhd_integral_of_locally_dominated` is holomorphy of a parameter-dependent integral
under a locally integrable dominant, without a logarithmic estimate on the parameter.
-/

open Complex MeasureTheory Filter Metric Set
open scoped Topology
public section
variable {α P E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A locally dominated holomorphic integrand has a holomorphic integral. The derivative
measurability assumption is often obtained from continuity on the integration domain. -/
theorem analyticOnNhd_integral_of_locally_dominated
    {μ : Measure α} {U : Set P} {F : P → α → E}
    (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (F x) μ)
    (hderivmeas : ∀ x ∈ U,
      AEStronglyMeasurable (fun a => fderiv ℂ (F · a) x) μ)
    (hhol : ∀ᵐ a ∂μ, AnalyticOnNhd ℂ (F · a) U)
    (hdom : ∀ x ∈ U, ∃ (s : Set P) (bound : α → ℝ),
      s ∈ nhds x ∧ Integrable bound μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ s, ‖F y a‖ ≤ bound a) :
    AnalyticOnNhd ℂ (fun x => ∫ a, F x a ∂μ) U := by
  apply analyticOnNhd_integral_of_dominated_of_fderiv_le hU
  intro x hx
  obtain ⟨s, bound, hs, hboundInt, hbound⟩ := hdom x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hU.mem_nhds hx))
  have hsub : ball x ε ⊆ U := fun y hy => (hball hy).2
  have hbnd : ∀ᵐ a ∂μ, ∀ y ∈ ball x ε, ‖F y a‖ ≤ bound a :=
    hbound.mono fun a ha y hy => ha y (hball hy).1
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hsmall : ball x r ⊆ ball x ε := ball_subset_ball (half_le_self hε.le)
  have hnear (y : P) (hy : y ∈ ball x r) : ball y r ⊆ ball x ε := by
    intro w hw
    rw [mem_ball] at *
    calc
      dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < r + r := add_lt_add hw hy
      _ = ε := by dsimp [r]; ring
  refine ⟨ball x r, (fun a => (2 * bound a) / r),
    (fun y a => fderiv ℂ (F · a) y), ball_mem_nhds x hr, ?_, ?_,
    hderivmeas x hx, ?_, ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hmeas y hy
  · exact hboundInt.mono' (hmeas x hx)
      (hbnd.mono fun a ha => ha x (mem_ball_self hε))
  · filter_upwards [hhol, hbnd] with a ha hba
    intro y hy
    apply norm_fderiv_le_div_of_mapsTo_ball
      (ha.differentiableOn.mono ((hnear y hy).trans hsub)) ?_ hr
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖F w a - F y a‖ ≤ ‖F w a‖ + ‖F y a‖ := norm_sub_le _ _
      _ ≤ bound a + bound a := add_le_add (hba w (hnear y hy hw)) (hba y (hsmall hy))
      _ = 2 * bound a := by ring
  · exact (hboundInt.const_mul 2).div_const r
  · filter_upwards [hhol] with a ha
    intro y hy
    exact (ha y (hsub (hsmall hy))).differentiableAt.hasFDerivAt

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
