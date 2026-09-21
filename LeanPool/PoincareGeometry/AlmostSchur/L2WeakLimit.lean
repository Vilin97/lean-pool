/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Passing scalar L2 pairings to a limit

These measure-generic lemmas assemble the final functional-analytic step of a
weak derivative argument. The integration-by-parts identity and convergence
of the coordinate derivative must be proved separately.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace AlmostSchur

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Strong scalar L2 convergence preserves pairing with a fixed L2 test. -/
theorem tendsto_integral_mul_L2
    {u : ℕ → X →₂[μ] ℝ} {v : X →₂[μ] ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (g : X →₂[μ] ℝ) :
    Tendsto (fun n => ∫ x, u n x * g x ∂μ) atTop
      (𝓝 (∫ x, v x * g x ∂μ)) := by
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using
    (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := g)))

/-- A vanishing L2 norm makes every fixed L2 test pairing tend to zero. -/
theorem tendsto_integral_mul_L2_zero
    {u : ℕ → X →₂[μ] ℝ} (hu : Tendsto (fun n => ‖u n‖) atTop (𝓝 0))
    (g : X →₂[μ] ℝ) :
    Tendsto (fun n => ∫ x, u n x * g x ∂μ) atTop (𝓝 0) := by
  have hu' : Tendsto u atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hu
  have h := hu'.inner (𝕜 := ℝ) (tendsto_const_nhds (x := g))
  rw [inner_zero_left] at h
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using h

/-- Integration by parts survives strong L2 convergence when the derivative
factor has norm tending to zero. Both tests are fixed L2 elements. -/
theorem integral_mul_L2_eq_zero_of_limit
    {u w : ℕ → X →₂[μ] ℝ} {v : X →₂[μ] ℝ}
    (hu : Tendsto u atTop (𝓝 v))
    (hw : Tendsto (fun n => ‖w n‖) atTop (𝓝 0))
    (φ dφ : X →₂[μ] ℝ)
    (hibp : ∀ n, (∫ x, u n x * dφ x ∂μ) = -(∫ x, w n x * φ x ∂μ)) :
    (∫ x, v x * dφ x ∂μ) = 0 := by
  have hl := tendsto_integral_mul_L2 hu dφ
  have hr := (tendsto_integral_mul_L2_zero hw φ).neg
  have heq : (fun n => ∫ x, u n x * dφ x ∂μ) =
      (fun n => -(∫ x, w n x * φ x ∂μ)) := funext hibp
  rw [← heq, neg_zero] at hr
  exact tendsto_nhds_unique hl hr

/-- On a finite measure space, strong L2 convergence preserves integrals. -/
theorem tendsto_integral_L2 [IsFiniteMeasure μ]
    {u : ℕ → X →₂[μ] ℝ} {v : X →₂[μ] ℝ}
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, v x ∂μ)) := by
  let g := (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : X => (1 : ℝ))
  have heq (w : X →₂[μ] ℝ) : (∫ x, w x * g x ∂μ) = ∫ x, w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp] with x hx
    change g x = 1 at hx
    rw [hx, mul_one]
  simpa only [heq] using tendsto_integral_mul_L2 hu g

/-- The mean-zero constraint is closed under strong L2 limits. -/
theorem integral_L2_eq_zero_of_limit [IsFiniteMeasure μ]
    {u : ℕ → X →₂[μ] ℝ} {v : X →₂[μ] ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (hz : ∀ n, (∫ x, u n x ∂μ) = 0) :
    (∫ x, v x ∂μ) = 0 := by
  have h := tendsto_integral_L2 hu
  simp only [hz] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end AlmostSchur
